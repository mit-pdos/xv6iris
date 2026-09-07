# Round E2 — lane briefs and the build script (checkpointed 2026-09-05 so another agent can resume)

Companion to app-round-e2.md (the proposal and rulings).  Each brief below was written for a subagent lane; paths under /tmp/… in them refer to the ORIGINAL session's scratchpad — substitute this file and a copy of the script below.  The rules every lane follows: build only on the GCP VM through the script (never make by hand, never locally), never change git state inside a lane, no subagents inside a lane, absolute paths, batch edits (FsAbsDefs' cone is ~500 files, ~10 min), no Admitted/Axiom, and the statements of SystemAdequacy.xv6_fs_adequacy_xv6Σ and App.xv6_app_adequacy_triv_xv6Σ byte-identical.  After a lane is green: run `make audit-only` on the VM (13 axioms is the baseline), commit, fetch/rebase, rebuild if iris files came in, push.

## The build script (vmbuild.sh <tree> <logname> [new iris files relative to iris/])

Run it for THE CHECKOUT THE SESSION RUNS IN (`<tree>` = its basename, e.g. `xv6iris-2`) and for no
other: sibling checkouts under /shared belong to other sessions (owner, 2026-09-07: "do not touch
anything other than YOUR OWN DIRECTORY").  Lanes therefore run SEQUENTIALLY in one tree, one build at
a time.  Retries while the only errors are FastLia's `Error: Timeout!` flake (the `timeout 1` lia
gate escaping `first` under VM load; seen 4 times on 2026-09-07, always at a trivial lia).

```bash
#!/bin/bash
# vmbuild.sh <tree> <logname> [extra files relative to iris/ ...]
set -u
TREE=${1:?tree, e.g. xv6iris-2}; shift
LOG=${1:-build}; shift || true
cd /shared/$TREE || exit 9
FILES=$( (git diff --name-only; git diff --cached --name-only; git ls-files --others --exclude-standard) \
         | grep '^iris/.*\.v$' | sed 's|^iris/||' | sort -u | tr '\n' ' ')
FILES="$FILES $*"
/shared/$TREE/gcp-rocq/run-on-gcp -q bash -c "
  cd /mnt/rocq/trees/_shared_$TREE/iris || exit 9
  for f in $FILES; do rm -f \${f%.v}.vo \${f%.v}.vos \${f%.v}.vok \${f%.v}.glob; done
  rm -f CoqMakefile CoqMakefile.conf
  coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
  for attempt in 1 2 3; do
    (make -f CoqMakefile -j180 -k > /tmp/$LOG.log 2>&1; echo EXIT=\$? >> /tmp/$LOG.log)
    nerr=\$(grep -c '^Error' /tmp/$LOG.log); nto=\$(grep -c '^Error: Timeout!' /tmp/$LOG.log)
    if [ \$nerr -gt 0 ] && [ \$nerr -eq \$nto ]; then echo \"RETRY \$attempt: \$nto lia Timeout flake(s) only\"; continue; fi
    break
  done
  echo COMPILED=\$(grep -c 'ROCQ compile\|COQC' /tmp/$LOG.log)
  grep -n 'Error' /tmp/$LOG.log | head -40
  tail -1 /tmp/$LOG.log"
```

## roundE2V2-brief.md — LANDED 2026-09-05 (as-built record: app-round-e2.md "E2-V2 AS BUILT")

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

## roundE2D-brief.md — LANDED 2026-09-05 (as-built record: app-round-e2.md "E2-D AS BUILT"; one deviation: `delta_link_tgt t a` takes the observed row, because sys_link has no nlink-0 guard on its target).  NEXT: write the E2-C and E2-L briefs from app-round-e2.md §2(b)/§3/§5/§8 and §4, in these briefs' mold.

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

## roundE2L-brief.md — LANDED 2026-09-07 (as-built record: app-round-e2.md "E2-L AS BUILT"; deviations: `luntgt_fired`'s pre-row is existential, instant 3 reuses `utgt_commit_at`/`uf_utgt_fire` with no `luntgt_*` names, `sys_link_ret` kept beside `link_arms`, only the three tails past the bump gained binders).  History: UNBLOCKED 2026-09-07 (E2-L0 landed, commit 263098976: `inode_held` carries `⌜0 < bv_unsigned inum⌝` right after the upper bound, so the target's positivity is one more binder in the link proof's namei unpacking; the BLOCKER paragraph at the end is history)

## Lane E2-L: link IN PLACE — `wp_sys_link_sconf` gains the three-commit bundle, its three retags become fires

Rulings: Q-c YES ("strengthen in place: we have a single kernel proof"); Q-d (the view is the live
namespace, lane E2-V2); E2-D's deviation (`delta_link_tgt t a` takes the OBSERVED row — sys_link has
no `ip->nlink == 0` guard on its target, ProofSysLink.v ~1843 "THE IIIc WALL", so the target may be an
unlinked-but-open file with NO view row and the bump brings it back).  Read app-round-e2.md §4 and its
"E2-D AS BUILT"; FsAbsDelta.v §4b; SpecSysUnlinkAU.v §2 (`uent_commit_at`/`utgt_commit_at`, lines
~455-530: the two-phase mold, the `_unit` dischargers) and FsAbsUnlinkFire.v §2b/2c (`uf_uent_fire`,
`uf_utgt_fire`: the fire mold).  Build ONLY via the script (log `rE2L`); standing rules as above.

### The contract (SpecSysLink.v; body at :210, module type at :337 — the STATEMENT changes, Q-c)

Add, in the mold of SpecSysUnlinkAU's commits, three commits and their receipts:

    ltgt_commit_at Γ E Φtgt   : ∀ I t a, ⌜arow_at (abs_view I) t a⌝ -∗ ⌜an_node a is AFile _ or ADev _ _⌝ -∗
                                 auth(1/2) I ={E}=∗ auth(1/2) I ∗ app_step t I (delta_link_tgt t a (abs_view I))
                                 ∗ (∀ I', ⌜abs_view I' = delta_link_tgt t a (abs_view I)⌝ -∗ auth I' ={E}=∗ auth I' ∗ Φtgt (abs_view I) t a)
    lent_commit_at Γ E Φent   : the parent leg, `uent_commit_at`'s shape at `delta_link_ent d nm t` with
                                 ⌜abs_view I !! d = Some (MkAnode (ADir ents) nl)⌝ and ⌜ents !! nm = None⌝
    luntgt_commit_at          : IS `SpecSysUnlinkAU.utgt_commit_at` (the failure arm's count-down is an
                                 unlink-target step: `delta_link_untgt t = delta_unl_tgt t`) — reuse it, do not clone

Post arms (the honest two-instant reading, SpecSysUnlinkAU.v:95-108's stance): ret 0 — the tgt receipt
(`∃ av0 a, ⌜arow_at av0 t a⌝ ∗ Φtgt av0 t a`) AND the ent receipt (`∃ av1 ents nl, ⌜av1 !! d = Some
(MkAnode (ADir ents) nl)⌝ ∗ ⌜ents !! nm = None⌝ ∗ Φent av1 d nm t`), with `t` the target's inum and
`nm` the new path's last element; ret −1 — the fold: (i) nothing fired (all three commits back:
argstr failed, namei(old) failed, target is a dir, NLINK_MAX), (ii) tgt fired AND untgt fired (both
receipts; untgt's pre-row is `av2 !! t = Some (MkAnode (an_node a) (an_nlink a + 1))`, present since
the count is ≥ 1; `lent_commit_at` back) — every `goto bad` after the bump.  The dispatcher
(ProofSyscall.v ~4947) passes the `_unit` dischargers exactly as unlink's arm does (~4847-4860,
`FsAbsInvFire.fsabs_unlink_pre`): add `fsabs_link_pre` (the tgt unit pays with
`AppInv.app_step_acc_view`? NO — `delta_link_tgt` is an insert even at an absent row, so the unit
needs `is_Some (I !! t)`: add ⌜is_Some (I !! t)⌝ to `ltgt_commit_at`'s premises — the target's inum is
a region row, the fire has it from `ghost_map_lookup` — and pay with `app_step_acc`).

### The fires (new FsAbsLinkFire.v, ~300 lines, cloned from FsAbsUnlinkFire.v §2b/2c)

- `lf_tgt_fire`: `uf_utgt_fire`'s mold.  Premises: `inode_local t nt'`, `fn_type nt <> 0`,
  `fn_type nt' <> 0 /\ abs_row nt' = MkAnode (an_node (abs_row nt)) (fn_nlink nt + 1)`, the target is
  not a dir (`sl_tdir_zne`).  Pre-row: `arow_at (abs_view I) t (abs_row nt)` (`abs_view_arow`).
  Hdelta: `abs_view_insert_row` at count `fn_nlink nt + 1 ≠ 0` (the insert arm) = `delta_link_tgt`.
  Receipt: `⌜arow_at av t (abs_row nt)⌝ ∗ Φtgt av t (abs_row nt)`.  Pure helper `lf_nlink_row`
  (twin of `uf_nlink_row` at +1: `sl_setnl`/`sl_incnl` keep type/size/major/minor).
- `lf_ent_fire`: `uf_uent_fire`'s parent half / `mkf_acre_fire`'s parent leg.  Premises: parent is a
  dir with `fn_nlink np <> 0` (the `dp->nlink == 0` guard fell through: ProofSysLink.v ~2658, ARM E2),
  `dir_entries np !! nm = None`, `abs_of np' = Some (MkAnode (ADir (<[nm := t]> (dir_entries np))) (fn_nlink np))`
  (a `lf_parent_row` twin of `mkf_parent_row`: dirlink keeps type and count).  Hdelta:
  `abs_view_insert` + `delta_link_ent_dir`.
- `lf_untgt_fire`: IS `uf_utgt_fire` (premise `1 <= fn_nlink nt` holds: the count was bumped) — reuse.

### The three sites (the ONLY proof edits; each `ireg_top_retag_auto … Logic.I` becomes a fire)

- #28 ProofSysLink.v ~1934 (`era_node dn bm dat → era_node (sl_incnl dn) bm dat`, `Hlocnl`): `lf_tgt_fire`.
- #29 ProofSysLink.v ~3091 (parent `era_node dnd bmd datd → era_node dnd' bmd' datd'`, `Hdiok'`…): `lf_ent_fire`.
- #4 ProofSysLinkTails.v ~1438 (`sl_tail_bad`: `era_node dn bm dat → era_node dn' bm dat`, `Hloc'`, `Hnz`): `uf_utgt_fire`.
Thread the tgt receipt from #28 through the walk to every exit (the six tails `sl_tail_b/c/d/bad/f/e2`
take the residue in their binders; `sl_tail_bad` fires untgt and delivers both receipts), the ent
receipt from #29 to the success exit.  `ProofSysLink.v` is ONE lemma (~3.9k lines): batch the edits,
build once per pass.  Delete nothing else (E2-Z deletes the `_auto` movers once no site uses them).

### Gate

Green; `make audit-only` 13; both audited statements byte-identical; the dispatcher's link arm passes
`_unit`s; no Admitted/Axiom.  Report: the bundle verbatim, the post arms, the fires' statements, the
three site diffs, deviations.  Do not commit.

### BLOCKER (found 2026-09-05 while staging the lane; nothing of E2-L is built)

The parent-leg fire (`lf_ent_fire` at #29) needs the parent's new entry map to be
`<[nm := bv_unsigned inum]> old` — `FsStateEra.dir_entries_dirlink_ins` — and that lemma requires
`inum <> bv_0 16`: a dirent whose inum is 0 IS a free slot (`DirView.dir_live`), so a zero target
inum would leave the view unchanged and the delta would be false of the machine.  sys_link's
proof does NOT have the target's inum nonzero: the target comes out of namei as `inode_held`
(IcacheHeld.v:102), whose only bound is `bv_unsigned inum < 16 * Z.of_nat icfg_nib`; `SpecIget`'s
premise is the same upper bound (SpecIget.v ~226); neither SpecNamex nor SpecDirlookup states a lower
bound.  The fact is TRUE of every execution (dirlookup skips `de.inum == 0`, the root is 1, ialloc's
post has `0 < inum`) but no contract carries it, so E2-L cannot land honestly until it does.
(Create is not affected: its child inum is ialloc's, `Hcpos : 0 < bv_unsigned cinum`.)

ORDER: E2-L0 (below) → E2-L.  E2-C does not depend on either.

## roundE2L0-brief.md — LANDED 2026-09-07 (commit 263098976; 38 files; 2 builds; green, 13 axioms, both audited statements untouched)

AS BUILT.  Spelling: TWO conjuncts, `⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗ ⌜0 < bv_unsigned inum⌝`,
the lower bound placed AFTER the upper one everywhere (a single `0 < x < B` would have broken the ~25
`exact Hinumc` sites that feed bare `x < B` premises; two conjuncts cost one binder per destructuring
and every existing hypothesis name keeps its meaning).  Changed: `inode_held`, `inode_held_refp`,
`inode_held_ty/_at/_short`, `SpecNparEra.inode_held_ty_at`, `FileInvDefs.inode_core` (NOT in the brief:
the file table RE-FORMS `inode_held` at the last fileclose through `inode_pay_cancel`, so `inode_pay_alloc`,
`ProofSysOpenParts.so_publish` and the eight sys_open tail lemmas `so_join → so_alloc → so_stores →
so_tail_pub → so_publish` and their `_au` twins gained the premise, threaded from the walk's package or
from create's `0 < inum`); `SpecIget.wp_iget_sconf` gained the premise `0 < bv_unsigned inum ->` after
the upper bound.  Discharged at: the root (`ROOTINO = 1`) in ProofNamex/NamexTr/NamexEra/NparEra/
NamexRoot; dirlookup's found arm by the new `ProofDirlookupParts.dlk_live_pos : dir_live data k -> 0 <
bv_unsigned (zero_extend' 32 (dir_inum data k))` (SpecDirlookup states NO positivity, despite DirView.v's
comment), at ProofDirlookup and at each walker's found arm; ialloc/ireclaim (`proj1` of ialloc's post);
sys_open's O_CREATE arm (create's post).  No boot-pin producer exists (`cwd_ref_at` is only ever formed
from namei's root arm and repackagings), so that brief item was a no-op.  `SpecNamex/SpecNamei/
SpecNameiparent/SpecDirlookup/IgetLic` needed no edit (none states the bound; it lives inside
`inode_held`).  One proof surprise: after `rewrite dlk_zext32_unsigned` the two `bv_unsigned`s (at
`mword 16` vs `bv 16`) are convertible but not syntactically equal, so `lia` sees two atoms; proved by
conversion (`Z.lt_eq_cases` + `bv_eq`).

### The brief as written (for the record)

Add `0 < bv_unsigned inum` beside the upper bound in `IcacheHeld.inode_held` (and its one-unfold
view `inode_held_refp`), in `SpecIget`'s premise, and in every producer/consumer pattern.  Where it
is discharged: namex's root (`ROOTINO = 1`) and dirlookup's found arm (`DirView.dir_live data k :=
dir_inum data k <> bv_0 16` — the zero-extended halfword is positive), ialloc (`0 < bv_unsigned
inum < fsc_ninodes`, SpecIalloc.v ~318/516), the boot pins (INIT_INO/SH_INO/ROOTINO literals).
Sizing (2026-09-05): 67 files mention `inode_held`; the destructuring pattern `(%Hipe & %Hkk &
%Hinumc & …)` occurs 17 times in ProofIdup, ProofSysChdir, ProofSysOpenAUWalk, ProofSysChdirAU,
ProofSysLink, ProofSysOpen; every `iExists k, q, inum; iSplitR …` producer gains one pure conjunct.
`SpecIget.wp_iget_sconf` (SpecIget.v ~212/286) is called from ProofIalloc, ProofIreclaim,
ProofDirlookup, ProofNamexRoot, ProofNamex, ProofNamexTr, ProofNamexEra, ProofNparEra (8 files);
SpecNamex/SpecNamei/SpecNameiparent/IgetLic mention `inode_held` 24 times.
Mechanical; batch the edits (the IcacheHeld cone is most of the syscall proofs).  Gate: green,
audit 13, both audited statements byte-identical, no Admitted/Axiom.  Do not commit.

## roundE2C-brief.md — LANDED 2026-09-07 (as-built record: app-round-e2.md "E2-C AS BUILT"; deviations: sites #9/#10 fire the DOTS leg, the unarm is #13b alone; `acre_commit_at_gen` takes the content as a function of (parent, child); the dots commit is indexed by whether the `..` landed; `cre_commits_unit` lives in SpecCreate).  NEXT: E2-L.

## Lane E2-C: create's legs as fires — arm / dots / ent / unarm from the contract bundle

Rulings: Q-c YES (strengthen `wp_create_sconf` in place — it is the only create over an unpinned `ty`
and mkdir's only path: ProofSysMkdir.v ~1185 → `Create.wp_create_sconf` at `T_DIR_ty_ok`); Q-h YES
(the failure arms are a do-then-undo PAIR: arm then unarm); Q-d (live view: ialloc's CLAIM is
view-preserving — `abs_of_bare`: the claim box has no row — so there is NO claim commit and
ProofIlock.v:1271 / §8 is E2-Z's `_same`, not this lane's).  Read app-round-e2.md §1 (sites #7, #8,
#9, #10, #13, #13b, #14, #16, #18, #21, #23, #26), §2(b), §3, §5, "E2-D AS BUILT"; FsAbsDelta.v §1b;
FsAbsMknodFire.v (`mkf_acre_fire`, `caf_acre_fire`, the `acre_commit_at` two-phase mold);
ProofCreateShared.v ~1600-1760 (`cr_dirty`, `cr_dirty_arm/retag/clear` and their `_same` twins —
the armed child's movers over `ireg_top_retag_armed_auto`); InodeRegion.v ~3393/3472
(`ireg_top_retag_step`/`_armed_step`: the step-shaped movers, whose step is exactly what
`AppInv.app_step_at` produces from an `app_step` and a delta equation).  Build via the script (`rE2C`).

### The commits (FsAbsMknodFire.v or a new FsAbsCreateFire.v; `acre_commit_at`'s two-phase mold)

    aarm_commit_at Γ E c Φarm   : ∀ I i, ⌜abs_view I !! i = None⌝ -∗ ⌜is_Some (I !! i)⌝ -∗ auth(1/2) I ={E}=∗
                                   auth I ∗ app_step i I (delta_arm i c (abs_view I))
                                   ∗ (∀ I', ⌜abs_view I' = delta_arm i c (abs_view I)⌝ -∗ auth I' ={E}=∗ auth I' ∗ Φarm (abs_view I) i)
    adots_commit_at Γ E Φdots   : the same at ⌜abs_view I !! i = Some (MkAnode (ADir ∅) 1)⌝ and `delta_dots i d`
    aunarm_commit_at Γ E Φun    : the same at ⌜abs_view I !! i = Some (MkAnode c 1)⌝ and `delta_unarm i`
    (the parent leg STAYS `acre_commit_at`: at the fire instant the child is armed, so the fused
     `delta_create` IS `delta_ent` — `delta_create_split` + `insert_id`; no new commit)

The `is_Some (I !! i)` premise on the arm (the child's inum is a region row; the fire has it from
`ghost_map_lookup`) is what lets the `_unit` discharger pay with `app_step_acc` although the VIEW has
no row there; the other two pay off the row (`abs_view_lookup_is_Some`).  `_unit` and `_pinned` seeds
for each, in FsAbsInvFire's `fsabs_*` family for the dispatcher.

### The fires (the armed-child form: mold = `mkf_acre_fire`'s two phases INSIDE
`ireg_top_retag_armed_step`'s ftopN critical section — the armed registry is what exempts the
half-built child from `ftop_body`'s `inode_local` clause; copy how `_armed_step` closes it)

- `caf_arm_fire` (#8 ProofCreateAlloc.v ~453, #18 ProofCreateAU.v ~4873, #23 ProofCreateAUF.v ~5155;
  today `cr_dirty_arm`): pre-row `abs_of nc0 = None` (`abs_of_bare`: the claim box), post-row
  `abs_of nc = Some (MkAnode c 1)` (`abs_of_create_dev`/`caf_abs_of_create_file`/a dir twin at
  `ADir ∅`); Hdelta `abs_view_insert` = `delta_arm`.  Make `cr_dirty_arm` take the commit (or add
  `cr_dirty_arm_fire` beside it) — the arm and the retag stay ONE step (the registry arm is inside).
- `caf_dots_fire` (#13 ProofCreateMkdir.v ~2344, today `cr_dirty_clear`): `ADir ∅ → ADir {DOT ↦ i,
  DOTDOT ↦ d}` at count 1; Hdelta `abs_view_insert` + `delta_dots_dir`.  The clear also disarms and
  releases the token: keep that in the helper, the fire replaces only the `_armed_auto` inside.
- `caf_unarm_fire` (#9/#10 ProofCreateMkdir.v ~2510/~2648 via `cr_dirty_retag`; #13b
  ProofCreateFailMkdir.v ~494 via `cr_dirty_clear`; #16 ProofCreateFail.v ~474, #21 ProofCreateAU.v
  ~6621, #26 ProofCreateAUF.v ~6901 via `ireg_top_retag_auto`): post-row `abs_of nc' = None`
  (`abs_of_none`, right: `fn_nlink = 0` — `cr_setf … (mword_of_int 0)`); Hdelta `abs_view_insert_None`
  = `delta_unarm`.  At #16/#21/#26 the child is NOT armed (the plain fragment): `mkf_acre_fire`'s plain
  mold.
- The parent leg: #14 ProofCreateMkdir.v ~2110 (fused `ents += nm` AND `nlink+1`, c := `ADir dots`)
  and #7 ProofCreateAlloc.v ~1244 (non-dir): generalize `caf_acre_fire` from `(forall e, c <> ADir e)`
  to `d <> i` (fresh child ≠ parent: both proofs have it) so one fire serves every child kind, keep
  `caf_acre_fire_file` as its wrapper; the collapse lemma is `delta_create_parent` + `insert_id` at the
  armed child (mold `caf_delta_create_nondir`/`delta_create_dev`).  Both sites then call it with the
  `acre_commit_at` from the bundle.

### The bundles and the threading

- SpecCreate.v (`wp_create_sconf_body` :562, module type :771): gains `aarm_commit_at (c := c0 ty)`,
  `adots_commit_at`, `aunarm_commit_at`, `acre_commit_at` for the child's kind (ty-indexed:
  `c0 T_DIR = ADir ∅` etc.), and the post carries the receipts: success — arm + [dots] + acre
  receipts; failure — nothing fired (walk/guards/ialloc), or arm fired (+dots) and unarm fired.
  `ProofSysMkdir.v` (~1185) threads the bundle; the dispatcher's mkdir arm (ProofSyscall.v ~5504)
  passes `_unit`s.
- SpecCreateAU.v (`cau_ok`/`cau_fail` :150-183) and SpecCreateAUF.v (:150-190): `cau_ok` gains the
  arm receipt beside `cre_pre`; `cau_fail`'s ARM-FAIL branch gains the arm+unarm receipts (Q-h) and
  the other branches return the unfired `aarm_commit_at`/`aunarm_commit_at`; SpecSysMknodAU.v
  (~575-800 arms) and SpecSysOpenAU.v (`open_post_ok_create`/`_fail_create`) thread them;
  `fsabs_mknod_pre_era`/`fsabs_open_pre_create` gain the units; dispatcher arms unchanged in shape.
- ProofCreateShared.v: `cr_dirty_arm/retag/clear` → fire-taking forms (the `_same` twins stay for the
  arms that do not move the reading).  Every `Logic.I` (`top_move`) argument at the 13 sites
  disappears; `ireg_top_retag_auto`/`_armed_auto` are then unused by create (E2-Z deletes them).

### Gate

Green; audit 13; both audited statements byte-identical; no Admitted/Axiom; the mknod/open/mkdir
dispatcher arms pass `_unit`s.  Report: the commits verbatim, every changed post arm, the fires'
statements, the 13 site diffs, deviations.  Do not commit.  Expect ~3-4 VM builds: the SpecCreate*
cone is the whole create family (ProofCreateAU/AUF ~7k lines each; ~2 min per file).

## roundE2W-brief.md — LANDED 2026-09-07 (as-built record: app-round-e2.md "E2-W AS BUILT"; deviations: the partial commit quantifies the LANDED run, the `-1` and empty-run sub-arms are `_same`, #5 uses `ireg_top_retag_gen`, the step premise is persistent)

## Lane E2-W: write — the short chunk's state fire (#6), the raw step on the landed write (#5), the dispatch (W1)

Rulings: Q-i YES ("a bug in the sys_write spec; the whole write spec may be non-deterministic but
must account for the short write"); Q-e W1 ("doesn't matter" between W1 and W2 — W1 it is: the
landed sconf and the AU form both stay, the dispatcher picks); Q-d (live view: `delta_write` is the
identity at an absent row, `FsAbsDelta.delta_write_absent`).  Read app-round-e2.md §1 (sites #5, #6)
and §7, "E2-V2 AS BUILT" (`arow_at`, `app_step_acc_view`), "E2-C AS BUILT" (the freshest two-phase
commit/receipt mold); FsAbsWriteFire.v (§2 `awrite_full_at`/`awrite_part_at`/`awrite_chain`, the
units, §3 `wrf_awrite_fire`); SpecSysWriteAU.v §2 (`wri_pre`, the arms) and SpecSysWriteAUEra.v
(the chain-shaped arms, the fail arm's `x <= 1` slack); SpecFilewriteAU.v (`fw_au_raw_*`, the chain
node's two arms); ProofFilewriteAU.v ~2670-2700 (`Hjoin`) and ~2950-3010 (the three sub-arms after
writei: the chunk fires / SHORT: offset moved / NOTHING MOVED); SpecWritei.v :40-110 and ~740-760
(THE DISTURBED REGION: after a short write, `dist <= BSIZE` bytes at `off + tot` hold unspecified
`dstb`; `tot = n -> dist = 0`; the -1 return is the pre-write guards, nothing written); the landed
side: SpecFilewrite.v (the FD_INODE arm, ~415-560), ProofFilewrite.v ~2296-2320 (site #5, the
`ireg_top_retag_auto … Logic.I` after writei), SpecSysWrite.v, ProofSysWrite.v, ProofSyscall.v
~4360-4440 (the write arm; it holds `fd_frags (pv_fdg (us_V U)) sts` in `sysc_arm_pre`, :1588) and
FdSlots.v :509-545 (`foff_row (FdOpen _ _ (FdInode _ γo)) = off_user_inv γo`, persistent) and :798
(`fd_frags_acc`: one fragment out, its `foff_row`, and the give-back); FsAbsInvFire.v
`fsabs_awrite_chain` (the dispatcher-side chain unit, off `off_user_inv`).  Build via the script
(log `rE2W`).

### W-b FIRST (small, the landed cone): #5 becomes `_step`

- `SpecFilewrite`'s FD_INODE arm gains ONE premise, the raw step at the inode the arm discovers:
  `∀ (I : gmap Z fs_node) (off : nat) (bs : list (bv 8)), app_step i I (delta_write i off bs
  (abs_view I))` — quantified over `i` too where the inum is not a parameter of the contract
  (`∀ i I off bs, …`); it is threaded in and RETURNED (it is a plain wand family, use it as many
  times as writei runs).  `SpecSysWrite` threads the same premise; `ProofSysWrite` passes it down.
- Site #5 (ProofFilewrite.v ~2314): `ireg_top_retag_auto … Logic.I Hlocw` → `ireg_top_retag_step`
  (InodeRegion.v:3393) with the step built from the premise at the bytes writei landed.  The
  reading after writei is `delta_write i off bsw (abs_view I)` at SOME `bsw` — the written run plus
  whatever of the DISTURBED region lies inside the new size — so the site proves
  `abs_view (<[i := n']> I) = delta_write i off bsw (abs_view I)` for that `bsw` (the mold is
  `wrf_awrite_fire`'s `Hdelta` via `abs_view_insert_row`/`wrf_write_row`, generalized to a run that
  is not the caller's chunk); at an absent row (`abs_of n = None`: the file was unlinked while
  open) both sides are the identity (`delta_write_absent`, and `abs_of n' = None` by
  `fn_nlink` unchanged).  If the record readings the site needs were thrown away by the landed
  join (the AU EDIT comment at ProofFilewriteAU.v ~2676 lists what the AU join re-kept: `tot`,
  `wi_dinode`, `off <= length bs0`), re-keep them in ProofFilewrite's join the same way.
- The consumers pay: ProofSyscall's write arm (~4402) supplies the premise from `app_inv` —
  `AppInv.app_step_acc_view` (license where the row is, identity where it is not) at
  `delta_write_absent`; that is exactly what `awrite_chain_unit`'s full arm does — and every other
  caller of `wp_sys_write_sconf`/`wp_filewrite_sconf` (grep: LinkSysWrite, ProofFilewriteCons,
  SpecFilewriteCons/ProofSysWriteConsAU?, SpecFileread's shared frame — several are comments)
  threads or supplies it likewise.  The ConsAU write (console) does not reach the inode arm: it
  supplies the premise trivially if its frame is shared, else nothing changes.

### W-a: #6 — the chain's PARTIAL arm becomes a state fire (the contract hole, Q-i)

- `FsAbsWriteFire.awrite_part_at` today moves only the offset half ("no delta this contract can
  receipt").  That is the hole: the machine DID move the row.  Replace it by a two-phase commit in
  `awrite_full_at`'s mold, NON-DETERMINISTIC in the bytes:

      awrite_part_at Γ E i γo k Φ REST :=
        ∀ I off bs bs0 nl (r : nat) (junk : list (bv 8)),
          ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
          ⌜r < length bs⌝ -∗ ⌜length junk <= BSIZE⌝ -∗
          auth(1/2) I -∗ off_gv γo (1/2) off ={E}=∗
          auth(1/2) I ∗ app_step i I (delta_write i off (take r bs ++ junk) (abs_view I))
          ∗ (∀ I', ⌜abs_view I' = delta_write i off (take r bs ++ junk) (abs_view I)⌝ -∗ auth I' ={E}=∗
                   auth I' ∗ off_gv γo (1/2) (off + r) ∗ Φ k (abs_view I) off (take r bs ++ junk) ∗ REST)

  `r` is what writei returned (`0 <= r < the chunk`: the `rz = 0` sub-arm — the first copy failed,
  `tot = 0`, the offset does not move, the disturbed chunk MAY be committed — is `r = 0`; the
  `rz = -1` sub-arm is writei's pre-write guards, NOTHING moved: use `r = 0`, `junk = []`, and
  `delta_write_nil`/the identity, or keep it on the `_same` reading `abs_of n' = abs_of n` if the
  re-kept join facts give it — say which); `junk` is the disturbed region's bytes that lie inside
  the new size (`dist <= BSIZE` — SpecWritei's bound is what makes the clause statable).  The
  receipt spells its shape purely: add `wri_part_receipt` (the `∃ r junk` facts beside `Φ`) and
  let the fail arm carry it: `SpecSysWriteAU.write_post_fail` / `SpecSysWriteAUEra`'s chain form
  gain `(wri_part_receipt … ∨ nothing fired past the prefix)` in place of the silent `x <= 1`
  slack (the slack becomes: the partial node fired and receipted, or the chain resumes at the
  prefix).  `awrite_chain_unit` and `FsAbsInvFire.fsabs_awrite_chain` pay the new arm with
  `app_step_acc_view` at `delta_write_absent`, like the full arm.  If `wri_pre` cannot be
  established on the short arm (it wants `off <= length bs0` and the count), state the partial
  commit's pre-row with `arow_at` and the facts the arm HAS — report the exact statement.
- `wrf_awrite_fire` gets a partial twin `wrf_apart_fire` (same ftopN section; the offset's half in
  at `off`, out at `off + r`); `SpecFilewriteAU.fw_au_raw_spend_part` hands the new arm;
  ProofFilewriteAU.v's SHORT sub-arm (~2990-3010) fires it in place of `wrf_partial_move` + the
  `ireg_top_retag_auto`, and the NOTHING-MOVED sub-arm (~3011-3020) either fires it at `r = 0,
  junk = []` or goes `_same` — the `Logic.I` at ~2985 disappears either way.  `wrf_partial_move`
  is then unused: delete it.

### W-c LAST: the dispatch (W1)

- ProofSyscall's write arm (~4402) case-splits BEFORE choosing the callee: `destruct (arg_fd v0
  (pv_ofile (us_V U))) as [[fd fv] |] eqn:Hafd` — `None` → the landed `wp_sys_write_sconf` (as
  today); `Some (fd, fv)` → `fd_frags_acc` at `fd` (`sts !! fd = Some st` from `arg_fd`'s shape,
  `fd < NOFILE`) gives `fd_st … fd st`, `foff_row st` and the give-back; `destruct st`: `FdOpen rb
  true (FdInode i γo)` → `wp_sys_write_au` (SpecSysWriteAU / its Era seal — use the one the tree
  proves, `SYSWRITE_AU_ERA` via LinkSysWriteAU) with EXTRA := the chain unit
  (`fsabs_awrite_chain` off `foff_row st = off_user_inv γo`) and the True receipt family, then the
  fragment back into `fd_frags`; every other `st` (closed, read-only, pipe, device) → the landed
  sconf.  Both callees' posts imply `sys_write_ret` (SpecSysWriteAU header item 4), so the arm's
  landed post is unchanged.
- After W-c, site #5 is off the theorem's path (the sconf only serves non-inode fds and the argfd
  failure) but stays `_step` in the build (W-b); do NOT delete `wp_sys_write_sconf`'s inode arm
  (E2-X's business, and the cons/pipe arms live there).

### Gate

Green; `make audit-only` 13 (from the tree root); both audited statements byte-identical; no
Admitted/Axiom; every `Logic.I` at #5 and #6 gone; the dispatcher's write arm passes units.
Report: the partial commit verbatim, the changed fail arms (AU and Era), the step premise's final
placement, the three site diffs, the dispatch's case split, deviations.  Do not commit.  Expect
3-5 VM builds (the SpecFilewrite cone is the write family + ProofSyscall).

## roundE2X-brief.md — LANDED 2026-09-07 (as-built record: app-round-e2.md "E2-X AS BUILT"; deviations: ProofSysOpenTails kept, 19 newly-dead imports trimmed from ProofSysUnlink, `so_bud_iput` qualified)

## Lane E2-X: delete the dead non-AU forms (ruling Q-f) — the unlink walk, the open walk, mknod, `so_stores`

Ruling Q-f YES: "dead pre-AU proofs not linked into the kernel and superseded by an AU spec are
deleted."  The dispatcher (ProofSyscall.v :4847/:5639/:5799/:5823) runs unlink, mknod and open on
their AU contracts; `_CoqProject` :1453-1458 already parks `ProofSysMknod.v`, `LinkSysMknod.v`,
`LinkSysOpen.v`, `LinkSysUnlink.v` off the build with the note "ProofSysOpen*/ProofSysUnlink* stay:
the AU proofs reuse them as lemma libraries".  CENSUS (2026-09-07, `Require` lines and lemma
uses): the reuse is far smaller than the note says —
- `ProofSysOpen.v` (4453 lines): the AU open (ProofSysOpenAUWalk/Join) imports it for THREE pure
  helpers only, `so_neq_of_eq` / `so_neq_of_ne` / `so_bud_iput` (:133-150, ABOVE the functor);
  every other name the AU files mention (`so_tail_pub`, `so_alloc`, `so_join`, `so_entry_c/n`,
  `so_stores`) is inside the sealed functor `SysOpenProof` (:151-4453) and is mentioned in COMMENTS
  only.  `SysOpenBudget.v` mentions `so_join` in prose.
- `ProofSysUnlink.v` (667 lines): the AU unlink (AUW1/2/3/5F/5D, AUParts) imports it for its
  PURE LAYER (`su_*`, :140-460); the sealed walk `SysUnlinkProof` below it is what imports
  `ProofSysUnlinkW1/W2/W3/W5File/W5Dir` (which import `ProofSysUnlinkShared`); NOTHING else
  imports those six files.  `ProofSysUnlinkParts.v` / `ProofSysUnlinkTails.v` ARE shared with the
  AU walk and stay.
- `ProofSysMknod.v` (1963 lines, off the build; E2-C's edits to it are unverified) has no importer.
- The three Link files are off the build and have no importer.

### Delete (files) and split (functors)

1. `git rm`: `ProofSysMknod.v`, `LinkSysMknod.v`, `LinkSysOpen.v`, `LinkSysUnlink.v`,
   `ProofSysUnlinkW1.v`, `ProofSysUnlinkW2.v`, `ProofSysUnlinkW3.v`, `ProofSysUnlinkW5File.v`,
   `ProofSysUnlinkW5Dir.v`, `ProofSysUnlinkShared.v` (confirm each has no importer first:
   `grep -l "Require.*\bNAME\b" iris/*.v`); their `_CoqProject` lines and the parked comment block.
2. `ProofSysOpen.v`: MOVE the three pure helpers to `ProofSysOpenParts.v` (their names unchanged;
   the two AU importers' `Require Import ProofSysOpen` becomes `ProofSysOpenParts` if not already
   there), then `git rm ProofSysOpen.v` (the functor and `so_stores`, site #3, go with it).
   `ProofSysOpenTails.v`: check its importers; if only `ProofSysOpen.v` used it, delete it too.
3. `ProofSysUnlink.v`: delete the functor `SysUnlinkProof` and its `Require Import` of the W
   files; keep the pure layer (rename the file `ProofSysUnlinkPure.v`? NO — keep the name, the six
   AU importers name it; just cut the walk).
4. The specs STAY: `SpecSysMknod.v` (`K_sys_mknod`, the frame the Era form restates),
   `SpecSysOpen.v` (`sys_open_post_any` at ProofSyscall :5857, the frame `SpecSysOpenAU` reuses),
   `SpecSysUnlink.v` (`K_sys_unlink`, `sys_unlink_slots`, the frame at SpecSysUnlinkAU :673).
   Their `Module Type SYSMKNOD/SYSOPEN/SYSUNLINK` seals are dead once the proofs are gone: delete
   a seal only if nothing references it (`grep -n "SYSOPEN\b\|SYSUNLINK\b\|SYSMKNOD\b" iris/*.v`);
   keep every `wp_sys_*_sconf_body` a live file applies or restates.  `SysOpenBudget.v` /
   `SysUnlinkBudget.v` (the machine-checked ledger notes) stay; fix their prose if it names a
   deleted lemma.
5. Doc pointers: `claude-notes/design/*.md` and `projects/*.md` lines that cite a deleted file
   by name — one grep, fix the citation to the AU twin or drop the line (durable-notes: "a fact
   about something that no longer exists is deleted").  `tools/proof_coverage.py`'s comment at
   :301 is history and stays.

### Gate

Green (the deletions shrink the cone; the dead-imports CI workflow must stay green:
`grep -n "" .github/workflows/dead-imports.yml` to see what it checks and run its script locally
if it has one); `make audit-only` 13; both audited statements byte-identical; `tools/
proof_coverage.py`'s sysfile.c count unchanged (sys_open/sys_unlink/sys_mknod are credited to
their AU links — run it as CI does, `.github/workflows/ci.yml` "Proof coverage report", and
compare with the last green run's summary).  Report: the file list deleted, the helpers moved,
every seal/body kept and why, the coverage numbers before/after.  Do not commit.  One or two
VM builds.

## roundE2Z-brief.md — LANDED 2026-09-07 (as-built record: app-round-e2.md "E2-Z AS BUILT"; one deviation: neither site's pre-node count was in the context, so `InodeRegion.ireg_top_park` gained a count clause guarded by the record's `nlink` and `EscrowInode.escA_body`'s EMPTY arm gained `fn_nlink n = 0`, each proved where the fragment is parked).  ROUND E IS CLOSED.

## Lane E2-Z: the last two blanket movers become `_same`; delete `top_move` and the `_auto` movers

Under the live view (E2-V2) a row exists only at nonzero type AND nonzero count, so both remaining
non-AU sites move between two ABSENT rows:
- #2 ProofIlock.v ~1271 (the fresh-inode fill at `ClaimK ty`): `n0` (the region's free-row
  fragment from `ireg_withdraw`; its type is 0 — find the fact in the withdrawn box, `Hlocbox` /
  `fresh_shape`) → `era_node dn bm_empty zeros` with `di_nlink dn = 0` (`fresh_shape`).
  `ireg_top_retag_auto … Logic.I Hlocbox` → `ireg_top_retag_same` with `abs_of n0 = None`
  (`abs_of_none`, left) and `abs_of (era_node dn …) = None` (`abs_of_none`, right;
  `FsAbsCreateFire.caf_era_none_nl0` is the one-liner).
- #1 EscrowDeposit.v ~243 (`ireg_free_deposit_au`, orphan → free): `ntop` at count 0 (`Hnl0'`) →
  `free_node dn'` (type 0).  Same move: `_same` with `abs_of_none` on both sides.  Its caller
  `ireg_free_deposit_au`'s statement does not change.
Then DELETE, in this order, rebuilding once: `InodeRegion.ireg_top_retag_auto`,
`ireg_top_retag_armed_auto` (E2-C left them unused; `grep` must show only definitions and the
comment mentions at FsAbsInvFire.v :28 and FsAbsLinkFire.v :234, which you reword);
`AppInv.app_top_update_auto`; `AppInv.top_move` and its vacuous `⌜top_move n n'⌝` premise in
`app_auto_raw` (:95; the two `Logic.I`s that discharge it in `app_step_of_auto` and
`app_top_update_auto` go with it; `app_auto_raw_triv` loses one `_`).  `app_auto`/`app_auto_raw`/
`Happ_auto`/`app_step_of_auto`/`app_step_acc` STAY (they are what the `_unit` dischargers pay
with; app-echo.md's L2 retires them).  Reword the headers that describe round A's "everything"
license: AppInv.v :30-40 and :70-77, App.v :42-46, AppEcho.v :47-48, FsAbsInvFire.v :24-28,
InodeRegion.v at the deleted lemmas; `design/applications.md` §2 (the movers) and
`app-instances.md` §7's round-E line — state the as-built fact: every view move on a dispatched
path is an AU fire or a `_step`; the only `_same` movers are the ones between absent rows.

### Gate

Green; audit 13; both audited statements byte-identical; `grep -n "top_move\|retag_auto\|
app_top_update_auto" iris/*.v` empty.  Report: the two site diffs, the deletions, the reworded
notes.  Do not commit.  One or two VM builds (AppInv's cone is the whole application layer;
InodeRegion's is most of the fs).
