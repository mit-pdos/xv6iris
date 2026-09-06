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

## roundE2L-brief.md — BLOCKED (written 2026-09-05 after E2-D landed; blocker found the same day, see the end of this brief and roundE2L0-brief.md below)

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

## roundE2L0-brief.md — the missing invariant: HELD INUMS ARE POSITIVE (prerequisite of E2-L)

Add `0 < bv_unsigned inum` beside the upper bound in `IcacheHeld.inode_held` (and its one-unfold
view `inode_held_refp`), in `SpecIget`'s premise, and in every producer/consumer pattern.  Where it
is discharged: namex's root (`ROOTINO = 1`) and dirlookup's found arm (`DirView.dir_live data k :=
dir_inum data k <> bv_0 16` — the zero-extended halfword is positive), ialloc (`0 < bv_unsigned
inum < fsc_ninodes`, SpecIalloc.v ~318/516), the boot pins (INIT_INO/SH_INO/ROOTINO literals).
Sizing (2026-09-05): 67 files mention `inode_held`; the destructuring pattern `(%Hipe & %Hkk &
%Hinumc & …)` occurs 17 times in ProofIdup, ProofSysChdir, ProofSysOpenAUWalk, ProofSysChdirAU,
ProofSysLink, ProofSysOpen; every `iExists k, q, inum; iSplitR …` producer gains one pure conjunct.
Mechanical; batch the edits (the IcacheHeld cone is most of the syscall proofs).  Gate: green,
audit 13, both audited statements byte-identical, no Admitted/Axiom.  Do not commit.

## roundE2C-brief.md — NEXT, in parallel with E2-L (written 2026-09-05)

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
