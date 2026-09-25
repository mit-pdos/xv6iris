# Worklist: seccomp -- the bump to a083670 and `seccomp x` in the union theorem

Design of record: [`../design/seccomp.md`](../design/seccomp.md).
Opened 2026-09-25.  Read `xv6-bump-playbook.md` before lane K or U.

## RESUME HERE  (written for a FRESH agent; the session that started this may have died)

OWNER'S CHECKPOINTS (2026-09-25): (1) a CLEAN BUMP to upstream `verified`
7b2c1b1, the whole tree green, audits 13/13/14, `check-decode`,
`check-ucode`, `vtest-check-ci`; `sys_seccomp` and `syscall()` at the
modest specs of design section 4 (a blocked call is the unknown-number
call; sys_seccomp ands the mask and returns 0); the seccomp user program
DUMPED AND CATALOGUED BUT NOT VERIFIED and not in the union app -- that
is lanes K + U merged, committed and PUSHED TO main.  (2) then the
theorem: lane M's model, the universe slot (S1), the claim arm (S2), the
seccomp program (S3), the round and the knob (S4).

WHERE THINGS ARE (verify with the commands; do not trust this text over
`git log`):
- `main` (local and origin) is still at the OLD pin 3e9926e (92cd62067).
- Branch `secc/bump`, checked out in `/shared/xv6iris-3`: base
  6c97101b7 (pin a083670, dumps, generated decode layer), c2ee5c64c (pin
  7b2c1b1: FsImgRaw.v), notes commits, then LANE K's commits (prefix
  "WIP:" while red).  `git status` there shows lane K's uncommitted
  sweep edits if it died mid-way; `git diff --stat` says how far.  Its
  VM tree is /mnt/rocq/trees/_shared_xv6iris-3 (log names in the Lane K
  status line below; `gcp-rocq/run-on-gcp -q --no-sync bash -c 'ls -t
  /tmp/*.log | head; tail -3 /tmp/<name>.log'`).
- Branch `secc/user`, worktree `/shared/xv6iris-3-lanes/secc-user`:
  DONE (e4a5502f5), rebased on c2ee5c64c: the user-tier relayout, the
  seccomp binary's dumps/catalog/ELF/fs.img lemmas, `fsimg_live_set` 23.
  To be MERGED into secc/bump when K's kernel tier is green (`git merge
  secc/user` in /shared/xv6iris-3; then TreeImg.v's `<=? 22` -> 23 if K
  has not done it).
- Branch `secc/model`, worktree `/shared/xv6iris-3-lanes/secc-model`
  (from 92cd62067, the OLD pin): LANE M in flight (design section 3;
  status line below); its VM tree is
  /mnt/rocq/trees/_shared_xv6iris-3-lanes_secc-model.  NOT part of
  checkpoint 1; rebase onto main after the push.
- Old dumps for the relayout tools: `git show 92cd62067:kernel-rocq/
  KernelSyms.v` etc. (the scratchpad copies die with the session);
  `RELAYOUT_OLD_REV=92cd62067`.

HOW TO FINISH CHECKPOINT 1 if lane K died: read its status line, `git
log secc/bump`, `git status`; continue its list (section "Lane K" below)
in /shared/xv6iris-3 with `gcp-rocq/vmbuild.sh xv6iris-3 <log>`; merge
secc/user; green; the five checks; then `git checkout main && git merge
--ff-only secc/bump` (or a merge commit if main moved: `git fetch
origin && git rebase origin/main secc/bump` first), `git push origin
main`.  Then write `claude-notes/completed/xv6-bump-7b2c1b1.md` from the
Lane K/U status lines and prune this file's checkpoint-1 text.

THEN CHECKPOINT 2: rebase secc/model onto main; then S1-S4 per design
sections 5-7 (briefs to be written into this file; the design sections
are detailed enough to brief from).

## Lane K -- the kernel bump and the mask (design §4)

Base state: the pin, dumps and generated layer are already in the tree
(`make xv6-rev-check`, `make check-decode` show the bump's own diff).
Old dumps for the tools: `$SCRATCH/old/OldKernelInstrs.v`,
`OldKernelSyms.v` (the scratchpad path is in the brief).

1. Playbook §1-§3: `fix_proof_imms.py --old-image`, `relayout_batch.py`
   (`--skip` the four reshaped Code files: Syscall, Userinit, Kfork; and
   there is no old CodeSysSeccomp), the `.rodata` content sweep, the
   `.data`/`.bss` remap (everything from `started` to `proc` moved +0x30,
   `tickslock`..`end_` +0x230; SWEEP DECIMAL AND PRE-DIVIDED FORMS), the
   stride 360 -> 368 wherever a proof spells it (`ProcGeom.proc_size`
   and any literal 360/`0x168`; the `proc[]` loops in procinit, allocproc,
   wakeup, kkill, scheduler, procdump, kexit's reparent, kwait).  ONE
   PASS EACH, from the pre-bump text.
2. §4's semantic changes: `pv_secc`, `proc_fields`, `uvis_secc`,
   `skey_eq`, `usys_eff`, `sysc_raw`/`sysc_num`, `uvis_num`,
   `usys_secc_ok` (LAST rows), `secc_all`, `uvis_num_full`, the pin in
   `UkRun.urun`, `USYS_seccomp`.
3. The four reshaped functions: `syscall` (the blocked arm at
   `sysc_num = 0`; the 23rd table entry), `userinit` (the store of
   `secc_all`), `kfork` (the copy), `sys_seccomp` (new Spec/Proof/Link/
   Code + manifest row + `_CoqProject`).  Stack budgets: re-derive from
   the image (`K_syscall` should not move).
4. `FsImgCheck`: 23 live inodes.
5. Build on the VM to green in the KERNEL tier; the user tier is lane U's
   and goes red only where the user images moved.  Then merge `secc/user`,
   build to green, `make check-decode`, `make check-ucode`, `make
   audit-all-only` (13 / 14), `make vtest-check-ci`.
6. Commit by explicit path; update `xv6-bump-playbook.md` with anything
   this bump taught; a `completed/xv6-bump-a083670.md` narrative.

STATUS, Lane K2 (merge of origin/main W2/W3, 2026-09-25): `origin/main`
6d48ce9d0 (filenames W2/W3) merged into secc/bump as 19ddc4d12 (a merge
commit; nothing under kernel-rocq/ or user-rocq/ moved).  Five files
conflicted, all resolved by carrying BOTH sides: UShCatFStage,
UkCatFEntries, UkUnionEntries (image_entry at `ProcDefs.secc_all` AND
W3's name/map arguments; echo's file entry keeps `%Hscw` and W3's
`efany_of .. nm s`), UkFileOpen (six `uvis_of_run .. false secc_all`
with W3's per-name family arguments), UkShRedirPaid (W3's general-name
diagnostic windows at the bumped sh's format address 0x12c8, including
W3's two new lemmas that auto-merged at the pre-bump 0x12b8).  No
design question arose; no semantic fallout outside the conflicts.
vmbuild k4r1: COMPILED=100, EXIT=0, zero `Error`, `make -n` 0 compiles
left.  Audits (/tmp/k4audit.log on the VM): system 13, union 14, tree
13, textually the baseline and identical to /tmp/k3audit.log.
`gen-ucode` on the VM: all nine UCode*.v unchanged (md5).  Local
`make check-decode`: passes.

## Lane U -- the user tier (design §0, §4 last bullet)

1. `make gen-ucode` on the VM against the OLD build (the remote tree's
   `.vo` are the old pin's; the generator needs only the model and
   `WpDecodeBridge`/`DecodeTotalU`/`WpRvcBridge`), diff the catalogs:
   every shift is +8 in text after `usys` and +0x10 in data.
2. Hand-written user proofs (`Uk*`, `USh*`, `UEcho*`, `UInit*`,
   `UkAbi`, `ElfUser`): every immediate that crosses the shift boundary
   (calls from main/ulib into printf/malloc, `auipc/addi` pairs at
   `digits`), every user DATA address literal, every ELF geometry
   constant (`sz`, data start, entry rows).  Verify each from the new
   dump, not by +8.
3. The seccomp binary: `USER_DUMPS += seccomp:Seccomp`, the four dumps
   in `user-rocq/_CoqProject`, `ElfUser.seccomp_elf`,
   `FsImgCheck.fsimg_seccomp_path/type/bytes` at inum 23, a
   `tools/ucode_seccomp.txt` (main, the stubs it issues, fprintf cone)
   and the manifest row, `UCodeSeccomp.v` generated.
4. Deliver as commits on `secc/user`; lane K merges and builds.

STATUS (2026-09-25): all four steps landed on `secc/user`.  Catalogs
regenerated (70 immediates, no shape change; ShK gains `uis_shk_1006`
because the stale page-straddle omit went away).  Hand-written relayout:
~4700 literal sites in ~70 files (pc/rodata remaps, `uis_*` renames, the
70 immediates at their proof sites, sh's two JUMP TABLES' entries --
data, pc-relative to the moved table -- and the text `filesz` of every
image).  Seccomp: dumps, `ElfUser.seccomp_elf`, `FsImgCheck` inum 23,
`UCodeSeccomp.v`.  Checked on the VM against the new dumps: every edited
file elaborates (`-vos`) except the 9 whose cone reaches K's three red
kernel proofs (ProofKvminit, ProofSysFork, ProofUserinit); the 57 whose
`.vo` cone has no kernel Proof/Link file were built as `.vo` (proofs
run).  `FsImgCheck.fsimg_live_set` 22 -> 23 was made here (a separate
commit) to build the seccomp byte lemmas; `TreeImg.v`'s `<=? 22` root
range (lines 27/206/213) is the same fs.img-count class and is K's.

## Lane M -- the pure model (design §3)

Worktree at the OLD pin, so the tree is green underneath.

1. `LineModel.lm_merge` line-indexed; port `lml_term_merge`,
   `lml_merge_prefix`, `lm_d4`, the determinacy section, `GenOut`,
   `PipesDisc`/`PipesDecE`/`UnionDisc`/`UnionDecU` instances.
2. `FileDisc.uline` gains `LSecc`; the parser; `uline_ws`/`line_body`/
   `line_file`; every `match` on `uline` in the pure files.
3. `UnionDisc`: `US`, codes mod 4, `uok`/`ucont`/`ustep`/`uterm`/
   `upanic`/`ufree`/`umerge`, `ulm adm adm_s`, laws, hooks, `ulmG` at
   the knob OFF.  `UnionDiscDec` decidability, `UnionDecU`'s decider
   (canonical `US []`), `UnionView.pview_union` (no pipeline at `LSecc`).
4. The Iris tier must stay green with the knob off: every law that cases
   on a `uline` refutes the `LSecc` arm from `uline_ok`; where a lemma is
   stated over an arbitrary line, add the admitted-line premise its
   callers already have.  `union_adequacy_closed`'s statement may change
   only through the model's definitions.
5. Demos (design §3 last bullet).  Build green, audits 13/14, commit on
   `secc/model`.

## S1-S4 (after K, U, M land) -- briefs written when they start.
