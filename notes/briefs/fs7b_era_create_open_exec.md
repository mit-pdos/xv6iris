> **COORDINATOR DECISIONS (Sept 25 2026):** D14 one era stage set generic in `npar` (mirrors the landed
> namex); D15 defer FsAbs.v's iProp half (record); D18 re-base kexec's user memory onto Lean's
> representation — the agent posts its plan first; D19, D20, D21 approved; D22: fix fs-rocq-summary §7.9.
> D16 / D17: pending the user.

> **COORDINATOR / USER DECISIONS PENDING.** §9 lists them (D14–D22). The definitional batch 7b-0
> (§8.1) needs **none** of them and can start now. The era walks need D14. kexec's contract needs D17
> and D18. D16 and D18 are process-layer decisions, so rule 3 sends them to the user too. D5 (make
> eb-generic) and D11 (drop the crash layer) from fs7 carry over unchanged.

# Brief: wave 7b: the ERA WALK LAYER, create, the path syscalls, and kexec

Read these first; their rules apply unchanged:
- notes/briefs/fs7_file_layer.md: the DECISIONS block at its top, §5.0 (the four facts), §5.1
  inventory, §8 (D1–D13), §9 risks. This brief is its §7.2 "Wave 7b", now surveyed.
- notes/briefs/fs0_common.md (porting rules).
- notes/briefs/fs1_leaves.md §1: the idioms, the vocabulary table, and the LAYERING rule. Stage files
  carry no `Proof` prefix, and exactly one `Proof<Fn>.lean` imports them.

## 0. Standing rules (verbatim; they bind every agent of this wave)

**User rules (verbatim, binding):** "for process abstractions in particular, look at how Rocq specs
are set up; don't reinvent the wheel." "the file system is a tricky piece of spec/proof. It's
important to consult the Rocq version whenever you might be possibly in doubt about the right way to
spec/prove something; it has the whole thing fully specified and proven." "some cleanup is helpful,
as there is a fair bit of gunk accumulated in the Rocq proofs, but the big ideas should be taken from
there." "it's ok to simplify the proof if you see a complete simplification, but it's not a good idea
to simplify without having the full picture or plan, because then the risk is, the simplification
will turn out to be at odds with some later part of the proof/spec."

**Session design rules (binding):** ONE capacity instance per camera type (never add a per-class
ghost field; shared ones live in Xv6G / MachGS); every NEW contract is interrupt-generic
("eb-generic": field `wp_X_eb` over `wp_X_eb_body`, `trapCsrsExt`/`cpuClaimExt` from
MachCSL/WpSmodeIntr.lean, `hnoff : k.noff = 0`, no hsie/hlocks; tactics `k_step_e`/`k_next_e`/
`k_ext_move`), as the landed fs cone is; REPORT (don't silently accept) every process-layer deviation
from Rocq; the sanctioned `procPrivExt` descriptor form; stage files WITHOUT the Proof prefix, one
Proof<Fn>.lean imports them (tools/check_layering.sh); prefix helpers with the function/area name and
check new top-level names don't clash in Xv6/ or MachCSL/; reuse the shared call-site files
(FsCallSites, FsCallSitesF, FsCallSitesI, FsWords, BlkmapBuf, DinodeSlot) instead of copying; proofs
FAST (no theorem over a few seconds); no `sorry`; live panics stay live.

**Main-tree agents:** build only your modules (`timeout 1800 lake build Xv6.<M>`), never a bare
`lake build`; no edits to existing files (report exact old→new); no Xv6.lean edits (report imports);
no git. **Worktree agents:** `git fetch origin && git reset --hard origin/lean-v2` first, seed .lake
from /shared/lean-xv6/.lake if cold, full build `timeout 3500 lake build Xv6 MachCSL` +
tools/check_layering.sh + sorry grep after each logical commit, commit on your branch (do NOT push),
messages ending with:
`Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`

**Report:** files/commits, contract shapes (old → new for edits), the Rocq lemmas mirrored,
deviations (process-layer ones flagged), cleanups with checked uses, reused names, what's left.

**Rules specific to this wave:**
1. **One Lean file per Rocq file, same name**, unless this brief names a split.
   - A PARTIAL port is allowed when part of a Rocq file waits on an unported layer. The header then
     says which sections are deferred and why. The rest is APPENDED later, by a worktree agent,
     because appending edits a landed file. `Xv6/FsAbsOpenFire.lean` is the precedent.
2. **Rocq's Proof files become stage files.** `ProofCreateAlloc.v` → `Xv6/CreateAlloc.lean`,
   `ProofSysOpenTails.v` → `Xv6/SysOpenTails.lean`, and so on. Only the seal is `Proof<Fn>.lean`.
   Rocq's `ProofNameiEra.v` imports `ProofNamei.v`, and Rocq's `ProofNparWrapEra.v` imports
   `ProofNameiparent.v`. Lean cannot do that (Proof→Proof). Restate the few pure lemmas under your
   own prefix (the `ProofNameiRoot.lean` precedent, :38–44), or see D19.
3. **Crash layer (D11):** drop `fs_crash_seam`/`gen_cert` from every frame and tail. Carry the
   SpecEndOp/SpecIreclaim deviation text.
4. **eb (D5):** Rocq pins `eb = true` on create, sys_open, sys_link, sys_unlink, sys_mkdir, sys_mknod,
   sys_chdir and sys_exec. Lean states each one eb-generic. Rocq threads `trap_csrs_ext`/
   `cpu_claim_ext` already on the sys_* frames. create does NOT: it discharges its callees' copies by
   `rewrite Heb /trap_csrs_ext` at 13 sites (ProofCreateAlloc:1454,1875; ProofCreateFound:637,781,
   …). So Lean's create gains `trapCsrsExt cpu k.sie`/`cpuClaimExt cpu k.sie k.proc` in and out,
   threaded to every callee. Every callee is already `_eb`. Record "stronger than Rocq" in each
   header.
5. **The slot supplies are being renamed by C0.** In-flight worktree
   `.claude/worktrees/agent-a25155d0dd14a3fba`, new `Xv6/SlotSupply.lean`:
   - `fdSlot γ` → `fdSlot`, `bslots γ n` → `bslots n`;
   - new name-only classes `[FdslotG GF] [BioslotG GF]`;
   - `NPROC`/`NOFILE` move out of ProcDefs.

   Any new file whose STATEMENTS name `fdSlot`/`fdSlots`/`bslots` starts after C0 merges, or is
   written against the C0 names and built after the merge. This affects SpecCreate (`bslots 3`),
   SpecSysOpen (`fd_slot`), the kexec phases and the dormant material. Definitional files in §8.1
   mention none of them.

## 1. Where 7b starts from (verified against the tree, Sept 25 2026, `d95468f12`)

**Landed, eb-generic, and usable as callees:**
- all of fs.c: bmap(+noalloc), ialloc, iupdate (incl. `wp_iupdate_link`/`_unlink`, SpecIupdate:62,65),
  ilock, iunlock, iput, iunlockput (`_dep_gen`, `_tx`), itrunc, readi (kernel+user exact), writei,
  dirlookup, dirlink (`wp_dirlink_gen_eb`, SpecDirlink:361), namex+namex_root, namei(+root),
  nameiparent, ireclaim, fsinit;
- begin_op, end_op, filealloc, filedup, fdalloc, argfd, argstr, argint, argaddr, fetchaddr, fetchstr,
  kalloc, kfree, memset, copyout, safestrcpy, strlen, proc_pagetable, proc_freepagetable, walkaddr,
  flags2perm, uvmalloc, uvmclear, uvmcopy, uvmfree, uvmunmap, uvmcreate, panic, printk, myproc.

**Landed definitional files:**
- `FsReady` (426).
- `FsAbsDefs` (659): the PURE half of Rocq FsAbs.v.
- `FsAbsDelta` (737): `deltaCreate`, `crePre`, `acreBump`, `dotsDelta`, `deltaArm/Unarm/Dots/Ent`,
  `deltaTrunc`, `deltaUnlink*`, `deltaLink*`.
- `FsAbsOpenFire` (151): section 0 ONLY.
- `FsAbsReadFire`, `FsAbsWriteFire`, `PieceFam`, `UserOff`, `AppInv`, `AppCfg`, `FsTree`, `DirView`,
  `PathElems`.
- `FsStateDefs/Bitmap/Inode/InodeOwned/Link/Top`.
- **`FsStateEraPure/Res/ResB`: Rocq FsStateEra.v complete** (dead code dropped with grep checks).
- `FileDefs`/`FilePay` (`inodePay_alloc` FilePay:161), `OffBox` (`offPublishPark` :627).
- `ProcInv` (`cwdRefAt`:74, `procPrivCwd`:132, `procPrivCwd_split`, `procPrivCwd_cwd`:188, the chdir
  swap).
- `SpecNamei.namei_procPrivCwd_rows` (:279), the block → namex-rows bridge.
- `ProcPriv` has `fdg cwi gen chg pvLazy` (ProcDefs:104–158).
- `InodeRegionSlot` has `iregLnk_tok_nz` (:863) and `iregLnk_toks_agree` (:891). These are part of
  Rocq IregLinkNz.v.

**In flight (worktrees / untracked); the flag waits in §3–§7 refer to these:**

| item | where | what 7b needs from it |
|---|---|---|
| **C0** (block P2 + fixed-name slot supplies + dormant allowances) | worktree agent-a25155d0… (`SlotSupply.lean`, 370 files touched) | the ONE block `proc_priv = core ∗ procOfiles` with `pvFdg` (sys_open's `fd_frags (pv_fdg ..)`, every sys_* frame); `fdSlot`/`bslots` names (rule 5) |
| **W7-B** fileclose re-spec | worktree agent-a3c9bbbf… (`SpecFileclose`, `FilecloseParts`) | sys_open's F-FAIL tail only (`fileclose_env_none`, the FD_NONE arm) |
| **filestat** | untracked `SpecFilestat`, `FilestatParts`, `FilestatCalls` | nothing in 7b |
| **D8** generation machinery | untracked `ChildTok` (733; `myPay`:234, `genKq`:287), `FirstTok` (`firstTok`:387), `SlotGen`, `UserChildren` | kexec/sys_exec `my_pay` (the AU); `first_tok` inside Rocq's `proc_priv` (every sys_* frame binder) |
| **I/O trace** | worktree agent-ae7de476… (`MachCSL/ObsTrace.lean`) | nothing in 7b (printk arms only through `printkEnv`) |

**Corrections to notes/fs-rocq-summary.md.** The coordinator should apply these; this brief is
read-only.
- §7.9 calls the era layer "consumed by the FsAbs*/App* application layer … Skip". That is **wrong**.
  sys_open, sys_chdir, create (→ mkdir, mknod), sys_unlink and kexec link against it. §7.9 also omits
  NparEra/NparWrapEra.
- The Rocq "Tr" family (`SpecNamexTr.v`, `SpecNameiTr.v`, `ProofNamexTr.v`) that SpecNamexEra.v's
  header cites **no longer exists**. Only stale `.vo/.glob` remain, and no `.v` requires it.
  `ex_hops_from` etc. live in FsAbsEra.v over `FsAbs.ax_hop`/`ax_hops_from`. **Nothing from Tr is
  ported.**

## 2. What changes the plan (the survey's findings)

1. **sys_link needs NO era and NO create.** `LinkSysLink.v:31` uses the plain `Namei Nameiparent`,
   which are landed. It can go end-to-end as soon as the block form is settled (D18). It is the
   earliest syscall of the wave.
2. **The era layer's definitional base is small.** The walks need only these parts of FsAbsEra.v:
   §1 (pure), lend (`elend`, `elend_frag`, `elend_intro`), hops (`ex_hop`, `ex_hops_from`,
   `ex_hops_cons`, `*_is_ax_hop(s)`), fire (`elend_of_era`, `era_half_split`, `elend_fire_hit/miss`),
   §6 Npar (`np_elems`, `ep_hop(s_from)`, `np_dead*`) and §7 Start (`um_start_of`, `ex_start`,
   `ep_start`, `ax_hops_triv`, `ep_start_triv`). They also need FsAbs.v's `ax_hop`/`ax_hops_from`
   only. **FsAbs.v's iProp half (`nview`/`astate`, `lend_agrees`, `apn_*`/`apr_*`) is needed by no
   kernel proof of 7b.** It serves only `*_pinned` lemmas, sys_mknod's "stable" add-on and
   FsAbsEra §0/§5, and those have no kernel consumers. D15.
3. **ProofNamexEra is ProofNamex with a small diff**, and so is ProofNparEra (Rocq's own headers;
   `diff` is −800/+381 and −358/+502, mostly the dropped counted seal). The changes:
   - the loop carries a cursor `dcur` with `inodeHeldAt ipv dcur ∗ P k dcur ∗ ex_hops_from … k`;
   - dirlookup's continuation fires `elend_fire_hit/miss` on the payload's `topFrag` leg;
   - the exits read the new arms;
   - the start fires `ex_start` at ROOTINO or idup's inum.

   The landed Lean namex is ONE proof for both `npar` arms (`NamexArgs.npar`). That shapes D14.
4. **kexec is mostly era-free.** Only `ProofKexecA.v` calls `NE.wp_namei_era` (:480). ACode (the
   code walk, :589) uses the PLAIN `Namei.wp_namei_gen`, and B, B2, B3, C and D are era-free. So all
   phase proofs can be ported against landed callees. **But SpecKexec's statement imports `UexecSlot`
   (`uvis`, a PURE record of the user-visible resume state), `ChildTok.my_pay` (D8), `UserFd` (only
   for a section binder), `FsAbsEra` and `SysOpenDefs`.** Its `S` is a PARAMETER, not
   `UexecRet.uslot` (SpecKexec.v:65–67), so the user-mode return layer itself is NOT needed. D17.
5. **Lean's user memory is a different representation.** It is a per-page view
   `M : Nat → List (BitVec 8)` and `UPtd`, where Rocq uses `gmap Z (bv 8)` and `uperm`. So KexecBuilt
   (2051) and KexecPtImage (541) are RE-BASED ports, not transcriptions. D18.
6. **FsAbsInvFire (476), PinnedOpen (306), FsSyscalls (576), ElfKernel/ElfUser/ElfLoadable and
   Exec{Bundle,Entry,Run}** are user-lane/dispatch/boot material and have no kernel consumer in 7b.
   They are out of scope (D20). ExecCommon.v is unrelated (Sail step helpers).
7. **FsLookup.v (996) and FsRep.v (372) are dead** for this wave. FsLookup is imported by nothing,
   and FsRep only by FsLookup. Do not port them.

## 3. The era walk layer (D9: PORT)

### 3.1 Rocq inventory

| Rocq file | lines | project imports (non-machine) | content | Link |
|---|---|---|---|---|
| FsAbs.v | 1000 | FsTree Xv6Cameras FsState FsAbsDefs FsBlocks FsBytesGamma InodeRegion | §1–2 pure (**landed** as FsAbsDefs); §3 carrier `nview_dq/nview/astate_q/astate` :175–383; §4 walk `ax_hop`:398, `ax_hops_from`:409, `lend_agrees`:417, `alend`, `apn_*`; §4b `apr_*` :721–909; §5 `ftop_*` :929–1000 | — |
| FsAbsEra.v | 1007 | DinodeEnc DirView ByteBuf DirentEnc FsTree PathElems InodeInv InodeLock IrefSlots FsBlocks FsBytesGamma FsStateEra IcacheRefDefs IcacheEscrow Xv6G FsImg FsAbs CtxIdDefs | §0 seam :145–292 (nview; not on the walk's path); §1 :169–213; lend :305–390; hops :396–437; fire :440–525; §5 `apn_walk_era` :534–583 (no users); §6 Npar :586–809; §7 Start :812–1007 | — |
| FsAbsNpar.v, FsAbsStart.v | 9 each | `Require Export FsAbsEra` stubs, imported by nothing | — | — |
| SpecNamexEra.v | 312 | …IcacheHeld IcacheInv IcacheEscrow FileInvDefs SpecDirlink SpecNamex FsAbsEra ProcAvail Xv6G FsCfg | `namex_era_post`:139, `wp_namex_era_body`:201 (`a1 = 0`:246, `ex_start fsc_fs (pv_cwi ..) P Pmiss pl`:285), `NAMEX_ERA`:294 | — |
| ProofNamexEra.v | 5335 | Spec{Myproc,Idup,Iget,Memmove,Ilock,Iunlock,Iunlockput,Iput,Dirlookup}, CodeNamex, SpecNamex, FsAbsEra, SpecNamexEra, ProofDirlookupParts, ProofNamexParts, IregLinkNz (only `ireg_root_ROOTINO`), IgetLic, DirView, FsTree, OffBox | pure `nx_*` :188–709 (byte-identical to ProofNamex); `wp_namex_era` :761–5333 | `NamexEraProof Myproc Idup Iget Memmove Ilock Iunlock Iunlockput Dirlookup Iput` |
| SpecNparEra.v | 369 | as SpecNamexEra + SpecDirlookup | `inode_held_ty_at`:151 (+ forget lemmas :162/182/189), `npar_era_post`:209, `wp_npar_era_body`:267 (`a1 ≠ 0`, `ep_start` over `np_elems pl`), `NPAR_ERA`:351 | — |
| ProofNparEra.v | 5898 | as ProofNamexEra + SpecNparEra | `wp_npar_era` :774–5896 | `NparEraProof` (same nine) |
| SpecNparWrapEra.v | 259 | …SpecDirlookup SpecDirlink SpecNamex FsAbsEra SpecNparEra | `K_nameiparent := 118`:89, `wp_npar_wrap_era_body`:97, `NPAR_WRAP_ERA`:241 | — |
| ProofNparWrapEra.v | 509 | CodeNameiparent, FsAbsEra, SpecNparEra, SpecNparWrapEra, **ProofNameiparent** (`npi_*`) | the 24-byte wrapper | `Module NparWrap := NparWrapEraProof NparEra` |
| SpecNameiEra.v | 294 | …FsTree SpecNamex **SpecNamei** FsAbsEra | `wp_namei_era_body`:118, `NAMEI_ERA`:234, the `NameiEraCursor` section :272–294 (used only in its own file) | — |
| ProofNameiEra.v | 580 | CodeNamei, IcacheHeld, FsAbsEra, SpecNameiEra, SpecNamexEra, **ProofNamei** (`nam_*`) | the 26-byte wrapper | `Module NameiEra := NameiEraProof NamexEra` |

**eb:** all four Specs are eb-generic (`cpu_own 0 eb ∗ trap_csrs_ext ∗ cpu_claim_ext`, crossing
`wp_next true`), as is the Lean SpecNamex. The comment at ProofNamexEra.v:790 ("still carries
`eb = true ->`") is stale.

**Budgets:** the era walks reuse `K_namex` = 116, `walk_need` and `walk_spend`, so there is no
`K_namex_era`. In Lean these are `namexSlots` (SpecNamex:26), `nameiSlots` = 120, `nameiparentSlots`
= 118, `walkNeed`/`walkSpend`.

**Process touch points** (the same in all four): `proc_priv_bare pj pidv Upr` and
`inode_held_at (pv_cwd ..) (pv_cwi ..)` in and out, plus `pv_cwi` as the argument of
`ex_start`/`ep_start`. Nothing else: no fd, no `my_pay`, no `first_tok`. **Lean form:** SpecNamex
deviation 3's rows `wordPointsTo (pPid k.proc) 4 dqp pidv ∗ wordPointsTo (pCwd k.proc) 8 dqc cwdv ∗
inodeHeldAt cwdv cwi`, with `exStart fscFs cwi P Pmiss (bview plen pfun)`. Callers bridge from
`procPrivCwd` via `namei_procPrivCwd_rows`. No new process-layer deviation: this is SpecNamex's
recorded one.

**Consumers (Rocq):**
- SpecNameiEra → ProofKexec(A), ProofSysOpen(Full, Walk), ProofSysChdir.
- SpecNparWrapEra → ProofCreate(Found), ProofSysUnlink(W1).
- SpecNparEra → ProofSysUnlinkW1, W2.

### 3.2 What Lean reuses from the landed namex

Lean's namex stages are built around `NamexArgs` and fixed bundles (`namexWalk` holds
`inodeHeld ipv`, `namexInv` has no cursor, `namexPostA`/`namexArm`; NamexDefs:112–335).

**Reuse unchanged:**
- NamexParts (`namex_*`, incl. `namex_nlink_nz`:169, `namex_drop_cons`:219, `namex_wi_*`), NamexFrame,
  NamexScan, DirlookupParts;
- NamexCalls (`namex_ilock/iunlockput/iunlock/iput/dirlookup`, over `{A with npar := …}`);
- from NamexElem: `namex_path_window`, `namex_name_window`, `namex_memmove`, `namex_win_nonul`;
- from NamexStart: `namex_consts`, `namex_root_held`, `namex_heldAt_slot`, `namex_cwd_cell`,
  `namexKeep_open`;
- from NamexLook: `namex_found_held`;
- from NamexExit: `namex_ctx_ret` and the `br`/`ret` constants;
- `NamexStart.namex_root_lic`:128, which is Rocq's `ireg_root_ROOTINO`.

**Need era variants:**
- NamexDefs: walk, inv, arm, out, post, loop;
- NamexStart: `namex_abs/rel/entry`. `namex_rel` already builds `inodeHeldAt (ientry ck) cwi` and then
  forgets it (:327–329);
- NamexLevel;
- NamexLook: `namex_look`, plus a `namex_loaded_open` variant that hands OUT the
  `topFrag (fsGammaL γfs) inum (eraNode dn bm data)` leg of `icLoadedFlatBody`
  (IcacheEscrowDep.lean:384; today it stays inside the rebuild wand, NamexLook:47–72);
- NamexExit's `call_iup/fail_out/notdir/nlink/miss/par/done`;
- NamexElem's `rest/long/short/elem`;
- NamexLoop, NamexTail.

About 2.3–2.5k Lean lines per walk if copied. See D14 for the shape.

**Missing in Lean:** `inodeHeldTyAt` (IcacheHeld has `inodeHeldTy`:139 and `inodeHeldAt`:182). Put it
in `SpecNparEra.lean`, with the three forget lemmas, so that no landed file is edited.

### 3.3 Lean file plan

**Definitional (can start NOW):**
- **`Xv6/FsAbsWalk.lean`**: FsAbs §4's `axHop`/`axHopsFrom` only, over `FsAbsDefs` + `FsStateTop`. It
  is a PARTIAL port of FsAbs.v under a new name, because FsAbsDefs already holds FsAbs's pure half and
  §3/§4-rest/§4b/§5 are deferred (D15). The header records this.
- **`Xv6/FsAbsEra.lean`**: §1, lend, hops, fire, §6, §7. §0, the lend laws and §5 are deferred with
  D15 (partial-port header). `rootino_agree` is trivial at `Nat` ROOTINO.

**Specs (after FsAbsEra):** `SpecNamexEra.lean`, `SpecNparEra.lean` (+ `inodeHeldTyAt`),
`SpecNameiEra.lean` (drop or port the `NameiEraCursor` section: grep shows no outside use),
`SpecNparWrapEra.lean`. The four are small (~1.2k Rocq total) and belong to ONE agent.

**Walks (after the Specs; shape per D14):**
- (b) recommended: `NamexEraDefs`, `NamexEraStart`, `NamexEraLevel`, `NamexEraLook`, `NamexEraExit`,
  `NamexEraElem`, `NamexEraLoop`, `NamexEraTail`, each generic in `npar` with the arms selected as
  Lean's landed namex does. `ProofNamexEra.lean` seals NAMEX_ERA and `ProofNparEra.lean` seals
  NPAR_ERA. Two thin Proof files import the same stages; that is allowed by check_layering, and the
  stages belong to one C function.
- (a) instead: the same set twice, with an `NparEra` infix for the second.

**Wrappers:** `ProofNameiEra.lean`, `ProofNparWrapEra.lean`, copying `ProofNamei.namei_main`/
`ProofNameiparent.nameiparent_main` (~140 lines each) against the era Specs; the pure lemmas are
restated (rule 2).

**Links:** `LinkNamexEra`, `LinkNparEra`, `LinkNameiEra`, `LinkNparWrapEra`, following the
LinkNamex/LinkNamei pattern. Lean Link theorems take COPYOUT etc. as arguments (`Namei (CO)`).

## 4. create, sys_mkdir, sys_mknod

### 4.1 Rocq inventory

Image: `create` 0x80004caa, 356 B; `sys_mkdir` 0x80005362, 72 B; `sys_mknod` 0x800053aa, 96 B.
`jal create` sites: sys_open, sys_mkdir, sys_mknod.

| Rocq file | lines | non-machine imports | content | Lean |
|---|---|---|---|---|
| FsAbsCreateFire.v | 924 | DinodeEnc DirView FsTree FsBlocks FsBytesGamma BlkmapDefs IrefSlots FdSlots FileInvDefs FsStateEra InodeRegion Xv6G FsAbsDelta AppInv PieceFam **FsAbs** (not FsAbsEra) | `create_made`:131, `cre_c0/cre_child`:157–202, `caf_era_*`; commits `cre_arm_fired`:271, **`dlookup_commit_at`:277**, `acre_commit_at(_gen)`:316/336, `aarm/adots/aunarm_commit_at`:363–402, `cre_child_unfired/_pair`:468; `_unit`s :485–568; **§1c :583–700 `mkf_auth_frag`/`mkf_auth_nview`/`*_pinned` (nview; D15)**; fires `caf_arm/dots/unarm_fire*`:709–898 | absent; deps landed (`iregArm/Disarm`, `iregTopRetag_armed_gen`, `ftopInv`/`ftopBody` InodeRegionInv, `appStep`, `pfAt`, `eraNode`) |
| SysMknodDefs.v | 116 | FsAbsCreateFire PathElems FsTree FsAbsDefs FsAbsDelta | `dev_arg`:83, `abs_of_create_dev`:102, `npar_elems`:115 | absent |
| FsAbsMknodFire.v | 844 | …SysMknodDefs FsAbsCreateFire FsAbs PathElems **FsAbsEra** | §2 rows `mkf_*`:149–222 (`mkf_era_is_dir` = landed `opfEra_is_dir`); §3 `mkf_dlookup_fire`:231; §4 `mkf_split16/low16_mod/dev_arg`:276–330; **§5 `npar_walk_pre_era/_dead_era`:339–410 (era)**; **§6 `np_*_mknod`:412–540 (era)**; §7 `caf_acre_*`, `caf_made_row*`:541–832 | absent |
| FsAbsEraMknod.v | 9 | re-export stub | — | skip |
| CreateBudget.v | 491 | LogInv SpecIput SpecWritei SpecDirlink | pure audit (`cr_budget_*`, `*_busts`); **no consumers** | optional |
| SpecCreate.v | 1316 | …ProcInv SpecDirlookup SpecIput FsBytesGamma AppInv FsTree PathElems DirView FsAbsCreateFire SysMknodDefs **FsAbsEra** FsAbsMknodFire PieceFam FsAbsDefs OffBox | `K_create := 128`:391 (10 + 118), `create_slots := 3`:398, `create_units := MAXOPBLOCKS`:402; `create_locked`:442; `cre_dots_leg`:564, `cre_commits`:588, `cre_ok_arms`:631, `cre_fail_arms`:657 (`npar_walk_dead_era`), `cre_ok_pure`:696; `wp_create_sconf_body`:1061–1288 (PARKING PREMISE :1138, NO trap_csrs_ext; `proc_priv` whole :1178; `log_opS`, `log_tx`, `iref_slots ns`, `bslots 3`, `ep_start … (pv_cwi ..)`:1216; `pf_at (dlookup_commit_at ..)`, `cre_commits`; exact ledger :1254); `CREATE`:1290 | absent |
| ProofCreateParts.v | 668 | …SpecIalloc FsAbsCreateFire SpecCreate ProofNamexParts BvShift KernelRvcDecode Spec{Nameiparent,Ilock,Dirlookup,Iunlockput,Iupdate,Dirlink} | `cr_setf*`, dot windows, `cr_trange*`, `cr_frm1..8`, `cr_kb`, `cr_K_value` | uses only `K_create`/`create_slots` from SpecCreate |
| ProofCreateFreshTy.v | 705 | SpecIalloc SpecIlock CodeCreate ProcInv OffBox AppCfg (no SpecCreate, no era) | `create_fresh_ty`:401: the ialloc+ilock stretch at +0xac; PARKING :182; `proc_priv_bare` | — |
| ProofCreateShared.v | 3229 | all fs-state + Spec{Bmap,Writei,Iput,Dirlookup,Dirlink,Namex,Create}, FsAbsEra, FsAbsMknodFire, FsAbsCreateFire, ProofCreate{FreshTy,Parts} | regs/arith `cr_*`:222–1600; `cr_dirty*`; `cr_fail_of_*`/`cr_ok_of_*`; bodies `cr_cont/tail/alloc/mkdir/fail/fail_mkdir_body`:1925–2974; `proc_priv(_bare)`, `pv_cwd` | — |
| ProofCreateFound.v | 2577 | … | `cr_found_half`:208; **`NP.wp_npar_wrap_era`**, dirlookup, ilock_dep, iunlockput_dep_gen; `proc_priv_bare_cref`, `cwd_ref_at` ×2 | — |
| ProofCreateAlloc.v | 1999 | … | `cr_alloc_half`:202; ialloc (via FreshTy), dirlink_gen, iupdate_link, iunlockput | — |
| ProofCreateFail.v / FailMkdir.v | 914 / 815 | … | `cr_fail_half` / `cr_fail_mkdir_half` | — |
| ProofCreateMkdir.v | 3082 | …SpecBmap SpecWritei **IregLinkNz** (`ireg_toks_agree`, `ireg_tok_nz`) | `cr_mkdir_half`:205 | IregLinkNz partly landed as `iregLnk_*` (InodeRegionSlot) |
| ProofCreate.v | 271 | — | `CreateProof (NP : NPAR_WRAP_ERA) IL IUP DL IA IU DLK : CREATE`:162 | — |
| LinkCreate.v | 34 | — | `Create := CreateProof NparWrap Ilock Iunlockput Dirlookup Ialloc Iupdate Dirlink` | — |
| SpecSysMkdir.v | 456 | …**FsCrash** ProcInv SpecCreate AppInv FsAbsEra FsAbsMknodFire PieceFam FsAbsDefs | `K_sys_mkdir := 146`:182; `mkdir_au_pre`:214 (`npar_walk_pre_era`, `dlookup_commit_at`, `cre_commits` at T_DIR); `mkdir_arms`:253; body :283 (PARKING :330; trap_csrs_ext :339; seam/cert :349); `SYSMKDIR`:433 | — |
| ProofSysMkdir.v | 1534 | — | `SysMkdirProof BeginOp Argstr Create Iunlockput EndOp`:558; `proc_priv_bare_acc` ×5 | — |
| SpecSysMknod.v | 856 | as mkdir + SysMknodDefs ArgPath FsAbs | `K_sys_mknod := 148`:243; `mknod_au_pre`:269, **`mknod_au_at`**:292, `mknod_arms`:415; frame :572 / body :715 (PARKING :613); `SYSMKNOD`:791; **stable add-on `mkr_*`, `wp_sys_mknod_stable_body` :461–547/760 (nview; no consumers; D15)** | — |
| ProofSysMknod.v | 2504 | … VcGen (`add_vec_off2`, `trunc32_unsigned`), ProofKforkParts (`proc_priv_tfp_valid`) | `SysMknodProof BeginOp Argint Argstr Create Iunlockput EndOp`:812; stable add-on :2104–2504 (defer) | — |

### 4.2 Process-layer touch points (FLAG)

- **create** takes `proc_priv` WHOLE and returns it unchanged. It uses only the cwd piece
  (`proc_priv_bare_cref`/`_acc`, `proc_priv_cwd_pid`, `cwd_ref_at`, `pv_cwi`) and touches no fd.
  **Recommended Lean form: `procPrivCwd` (or the SpecNamex rows) plus `cwi`**, framed. That is a
  contract over LESS than Rocq's block (stronger by the frame rule), and a process-layer deviation to
  report (D16).
- **sys_mkdir / sys_mknod** take the whole block and return it at `us_upt U P'` (argstr's
  `uptd_ext_sz`, i.e. Lean `procPrivExt`). Their frame waits on C0's P2 block. sys_mknod also needs
  `proc_priv_tf`/`proc_priv_tfp_valid` (ProofKforkParts in Rocq; absent in Lean → a ProcInv accessor,
  coordinate with C0).

### 4.3 Lean file plan

**NOW:**
- `FsAbsCreateFire.lean` without §1c.
- `SysMknodDefs.lean`.
- `FsAbsMknodFire.lean`, PARTIAL: §2–4 and §7 now; §5–6 are appended after FsAbsEra.
- `CreateDefs.lean`: NEW NAME. It hoists from SpecCreate what names no era and no slot supply:
  `createSlots` (= Rocq `K_create` = 128, the Lean `namexSlots` convention),
  `createIrefSlots` (= Rocq `create_slots` = 3), `createUnits`, `createLocked`, `creDotsLeg`, `creCommits`,
  `creOkPure`, and the unit/dev/file lemmas. That lets CreateParts and FreshTy start. Record it as a
  split of SpecCreate.v.
- `CreateParts.lean`.
- `CreateFreshTy.lean` (eb-generic, over `procPriv`).
- `IregLinkNz.lean`: grep `iregLnk_*` first and port ONLY what is missing: `ireg_tok_root_le`,
  `ireg_boot_no_claim` if absent.
- `CreateBudget.lean`: optional, since it has no consumers.

**After the era Specs + C0:**
- `SpecCreate.lean`;
- `CreateSharedRegs.lean` (pure `cr_*` helpers, can start earlier) and `CreateSharedBody.lean`
  (a split of the 3229-line ProofCreateShared.v);
- `CreateFound.lean` (needs NPAR_WRAP_ERA's Spec only), `CreateAlloc.lean`, `CreateFail.lean`,
  `CreateFailMkdir.lean`, `CreateMkdir.lean`;
- `ProofCreate.lean`, `LinkCreate.lean`.

**After LinkCreate + C0:**
- `SpecSysMkdir`/`ProofSysMkdir`/`LinkSysMkdir`;
- `SpecSysMknod`/`ProofSysMknod`/`LinkSysMknod`, with the stable add-on deferred (D15).

## 5. sys_link, sys_chdir, sys_unlink, sys_open

### 5.1 Rocq inventory (definitional / Spec / Budget / Fire)

Image: `sys_link` 0x80004f68, 292 B; `sys_unlink` 0x8000508c, 384 B; `sys_open` 0x8000520c, 342 B;
`sys_chdir` 0x8000540a, 128 B.

| Rocq file | lines | key non-machine imports | content | Lean |
|---|---|---|---|---|
| SysUnlinkDefs.v | 355 | FdSlots IrefSlots FileInvDefs ProcInv FsTree FsBytesGamma AppInv FsAbsDefs CtxIdDefs FsAbsDelta | `dots_only`:173, `unl_pre(_ne)`:179/192, `delta_unlink_split/last_file/last_dir`:204–235, `uent/utgt/dmiss_commit_at`:268/290/309 + `_unit`s | absent; **all deps landed** (`deltaUnlink*` FsAbsDelta:466–610) |
| SysUnlinkBudget.v / SysLinkBudget.v | 284 / 228 | LogInv SpecIput SpecWritei SpecNamex (SpecDirlink) | pure `su_*`/`sl_*`; `sys_unlink_slots = 2` | absent; deps landed. Grep for consumers before porting |
| SysOpenBudget.v | 268 | LogInv SpecIput SpecNamex **SpecCreate** SpecItrunc | `so_u0 = 10`, `so_join = 3`, `so_trunc_*`, `so_create_need`(uses `create_units`), `so_namei_arm_closes` | absent; all but `create_units` landed (use `CreateDefs`) |
| SysOpenDefs.v | 777 | …ProcInv SpecFdalloc PathElems FsTree SysWriteDefs **FsAbsEra** ArgPath **FsAbsMknodFire** AppInv PieceFam **FsAbs** FsAbsDelta | §1 `om_*`:196–207; §2 `aopen_commit_at`:281, `atrunc_commit_at`:322, `open_trunc_piece`:400–424; **`namei_walk_pre_era/_dead_era`:437/455 (era)**; `open_au_pre_plain/create`:485/498, `open_au_*_at`:537/546 (era + create); **`open_fd_ok`:686 (`proc_priv`, `fd_frags (pv_fdg ..)`: C0)**, `open_fd_rcpt`:726, `open_fd_ok_split`:739 | absent |
| FsAbsOpenFire.v | 424 | …SpecItrunc FsAbsDelta SysOpenDefs FsAbsEra FsAbsMknodFire | §0 **landed**; §1 `opf_start_of_open`:293 (era); §2 `opf_open_fire(_1)`:308/344; §3 `opf_atrunc_fire`:368 | append §2–3 after SysOpenDefs §2; §1 after era |
| FsAbsUnlinkFire.v | 530 | …FsStateInode FsStateEra InodeRegion FsAbsDelta FsAbsMknodFire SysUnlinkDefs AppInv PieceFam | `uf_*` rows :120–209; `uf_dmiss_fire`:265; **`uf_dex_fire`:314 (needs `mkf_dlookup_fire` + `dlookup_commit_at`)**; `uf_uent_fire`:376; `uf_utgt_fire`:477 | absent; all but `uf_dex_fire` can start now (`iregTopRetag_*` InodeRegionInv:832–910) |
| SpecSysLink.v | 634 | …FsCrash ProcInv SpecDirlink FsTree AppInv SysUnlinkDefs PieceFam FsAbsDefs | `K_sys_link = 158`:213, slots 3; `link_tgt_ok`:264, `ltgt/lent_commit_at`:294/315, `link_commits`:357, `*_fired`, `link_arms*`:420–464; body :478 (PARKING :519; seam/cert :539); `SYSLINK`:616 | absent; `deltaLink*` FsAbsDelta:636–655 |
| FsAbsLinkFire.v | 371 | …FsAbsUnlinkFire SpecSysLink | `lf_*` rows, `lf_tgt_fire`:245, `lf_ent_fire`:307 | absent |
| SpecSysChdir.v | 547 | …ProcInv SpecDirlink PathElems FsTree AppInv **SysOpenDefs** PieceFam | `K_sys_chdir = 140`:208, iref 2; `sys_chdir_post`:223 (**`pv_cwd` and `pv_cwi` change**); `chdir_au_pre`:249 (= `namei_walk_pre_era` + `pf_at aopen_commit_at`); `chdir_arms*`; frame :410 (PARKING :440; seam :453); `SYSCHDIR`:531 | absent |
| SpecSysUnlink.v | 681 | …SysUnlinkDefs SysMknodDefs FsAbsMknodFire AppInv | `K_sys_unlink = 148`:350, slots 2; `unlink_au_pre`:420 (`npar_walk_pre_era` + uent/utgt/`dlookup_commit_at`/dmiss); `unlink_arms*`; frame :546 (PARKING :580; seam :593); `SYSUNLINK`:662 | absent |
| SpecSysOpen.v | 1687 | …FileInv ProcInv SpecDirlink SpecFdalloc **SpecCreate** ConsoleInv SysMknodDefs FsAbsMknodFire ArgPath SysOpenDefs PieceFam UserFd (section binder only; unused: drop) | `K_sys_open = 152`:364, slots 3; `sys_open_post`:422 (`fd_slot`); `open_arms_plain/create`:506–748; `open_in/arms/receipt*`:901–1051; `cre_fail_to_open`:1404; frame :1466 (PARKING :1501; seam :1528); bodies :1570–1630; `SYSOPEN`:1667 | absent |

### 5.2 Rocq proof files (they become Lean stage files)

| family | Rocq files (lines) | notes |
|---|---|---|
| sys_link (7363) | ProofSysLinkParts 973 (pure/frame, no process), ProofSysLinkTails 2309 (`proc_priv` ×12, seam ×6; imports SysUnlinkDefs, FsAbsUnlinkFire, IregLinkNz), ProofSysLink 4081 (walk + seal; `proc_priv_split_cwd` ×9, `cwd_ref_at_of_held_at` ×8) | Link `SysLinkProof Argstr BeginOp Namei Nameiparent Ilock Iunlock Iupdate Dirlink Iput Iunlockput EndOp`: **all landed**. Split ProofSysLink into `SysLinkWalkA` (+0x00..+0x66) / `SysLinkWalkB` / `ProofSysLink` |
| sys_chdir (2498) | ProofSysChdir 2498 (frame to 482, epilogue to 701, M1 tail to 889, body to 2496; `pv_cwd` ×16, `proc_priv` ×22, `pv_fdg` ×7; fires `opf_open_fire_1` at SpecNameiEra) | Link `SysChdirProof Myproc BeginOp Argstr NameiEra Ilock Iunlock Iput Iunlockput EndOp`. Lean: `SysChdirParts`, `SysChdirTails`, `ProofSysChdir`; the swap is `procPrivCwd_cwd` |
| sys_unlink (12501) | Parts 1272, Pure 438 (imports SysReadDefs, W32Arith), Shared 359, Tails 1635, W1 968 (prologue, argstr, begin_op, NparWrapEra/NparEra; `first_tok`), W2 1461 (dmiss), W3 1941 (isdirempty; `uf_dex_fire`), W5F 1887, W5D 2268, ProofSysUnlink 272 | Link `SysUnlinkProof Argstr BeginOp NparWrap Ilock Namecmp Dirlookup MemsetArray Readi Writei Iupdate Iunlockput EndOp Panic` (Lean `MEMSET`). Lean: `SysUnlink{Parts,Pure,Shared,Tails,W1,W2,W3,W5F,W5D}` + `ProofSysUnlink` |
| sys_open (11896) | Parts 1520 (`so_publish`:930 → `inodePay_alloc`), Bits 324, Tails 2307 (F-FAIL fileclose :1640–1860, `fileclose_env_none`), Shared 628, Walk 965 (NameiEra; `proc_priv_split_cwd`, `first_tok`), Join 570, Alloc 1003 (`fd_slot`, `proto_store_free`:944), Stores 970 (`opf_atrunc_fire`, itrunc ×14), Pub 442 (`proc_priv_settle`, `off_pub_park`; `proto_publish` ported HERE, FileDefs deviation 3), ProofSysOpen 916 (plain arm), CreArm 484, EntryC 840 (create at T_FILE), Full 927 (13-arg seal) | Link `SysOpenProof Argint Argstr BeginOp NameiEra Ilock Iunlock Iunlockput EndOp Fileclose Itrunc Filealloc Fdalloc Create`. Lean: `SysOpen{Parts,Bits,Tails,Shared,Walk,Join,Alloc,Stores,Pub,Plain,CreArm,EntryC}` + `ProofSysOpen` (the FULL seal; Rocq's plain-arm file becomes the stage `SysOpenPlain`) |

**Budgets:**

| | K | iref | other |
|---|---|---|---|
| open | 152 | 3 | `bslots 3`, 1 `fd_slot`, `so_join = 3`, trunc `it_entry false 1 = 3` |
| link | 158 | 3 | `sl_u3 ≥ 7`; the found arm busts the counted form by one (SysLinkBudget:196): use the set form |
| chdir | 140 | 2 | — |
| unlink | 148 | 2 | `su_u2 ≥ 5` |

### 5.3 Process-layer touch points (FLAG)

- All four Rocq frames take ONE `proc_priv γf pj pid U`, which carries `first_tok` and a `GenId`
  binder (D8). **sys_open needs the cwd AND the fd table at once** (`fd_frags (pv_fdg ..)`,
  `proc_priv_settle`). Its frame therefore waits on C0 P2, and its `first_tok` part on D8.
- sys_link, sys_chdir and sys_unlink touch only the cwd (plus `pv_fdg` pass-through in chdir). Their
  frames can be drafted over `procPrivCwd` now and re-cut to the P2 block, or can wait (D16).
- **sys_chdir WRITES `pv_cwd` and `pv_cwi`**. syscall's post later reads
  `(num = 9 ∧ ret = 0) ∨ pv_cwi' = pv_cwi`. The Lean swap is `procPrivCwd_cwd` (ProcInv:188).
- New ProcInv accessors needed: `proc_priv_settle` (sys_open Pub), `proc_priv_tf`/
  `proc_priv_tfp_valid` (sys_mknod, kexec, sys_exec). **ProcInv is C0's file**: report the exact
  statements to the coordinator; do not add them from a main-tree agent.

### 5.4 Lean file plan

**NOW (all deps landed):**
- `SysUnlinkDefs`;
- `SysUnlinkBudget`, `SysLinkBudget` (if consumed);
- `SysOpenBudget` without the create lemmas, or with them via `CreateDefs` once that exists;
- `FsAbsUnlinkFire` PARTIAL (no `ufDex_fire`);
- `SysLinkDefs.lean`: NEW NAME, SpecSysLink's commit/arm definitions (`linkTgtOk`, `ltgt/lentCommitAt`,
  `linkCommits`, `*_fired`, `linkArms*`), so that FsAbsLinkFire can start without the frame. Record
  it as a split of SpecSysLink.v;
- `FsAbsLinkFire`;
- `SysOpenDefs` PARTIAL: §1 `om*`, §2 `aopenCommitAt`/`atruncCommitAt`/`openTruncPiece`, pure
  `openFdRcpt`;
- pure stage files `SysOpenBits`, `SysLinkParts`, `SysUnlinkParts`, `SysUnlinkPure`.

**Worktree appends** (landed files):
- FsAbsOpenFire §2–3 after SysOpenDefs §2;
- §1 + SysOpenDefs §3 (`nameiWalkPre/DeadEra`, `openAu*`) after FsAbsEra/FsAbsMknodFire §5;
- FsAbsUnlinkFire `ufDex_fire` after FsAbsMknodFire §3 + FsAbsCreateFire;
- `openFdOk*` after C0.

**Then the chains.** Link:
- sys_link: after C0 (D16): `SpecSysLink` → `SysLinkTails` → `SysLinkWalkA/B` → `ProofSysLink` →
  `LinkSysLink`.
- sys_chdir: after NameiEra + C0: `SpecSysChdir` → stages → seal.
- sys_unlink: after NparWrapEra + create's defs + C0.
- sys_open: after NameiEra + LinkCreate + C0 + W7-B.

## 6. kexec and sys_exec

### 6.1 Rocq inventory

Image: `kexec` 0x800048b6, 858 B, **loadseg inlined** (only its panic string exists, 0x800075c8);
`sys_exec` 0x8000548a, 268 B, 480-B frame. Budgets: `K_kexec = 188` (68 + namei 120),
`K_sys_exec = 248`.

| Rocq file | lines | needed by the kernel contract? | non-machine imports / notes | start |
|---|---|---|---|---|
| ElfEnc.v | 266 | yes | RiscvModelBytes; `le_at`, `eh_*`, `ph_*`, `ELF_MAGIC` (use `nthByte`/`bytesToWord`) | NOW |
| ElfFile.v | 803 | yes | pure: `elf_bytes`, `elf_parse_*`, `elf_loads`, `elf_entry`, `elf_image`, `elf_wf` | NOW |
| ElfBridge.v | 513 | yes | ElfEnc ElfFile InodeDefs FsTree; `kxq_entry_of_ehdr` | NOW |
| KexecDefs.v | 582 | yes | SchedCtx FsCrash(drop) IcacheEscrow UserPtTree ProcDefs FsReady; `MAXARG`, `USERSTACK`, `K_kexec`, `kxc_*` stack algebra, `kxc_tf`:406, **`kexec_ok`:417** (last row `pv_lazy V' = false`:490), **`fs_fabric`:494** (= `fs_ready ∗ printk_env ∗ procs_inv ∗ disk_geom ∗` virtio lock) | NOW (add `tfEpcIdx`) |
| KexecOkQ.v | 441 | yes | ProcInv KexecDefs ElfEnc; `kexec_ok_q`:103, `kexec_ok_qf`:216, **`kexec_closer`:323** (over `proc_priv`) | after C0 (the block) |
| KexecBuilt.v | 2051 | yes | UserBits PageGeom UmodeAbi ElfEnc ElfFile ElfBridge UserPerm UserPtTree ProcDefs KexecDefs; `kexec_built`:2021 (S8 `lazy_free`) | NOW, **re-based** (D18); S6/S7 `perm_of` rows with D17 |
| KexecImageAlg.v | 283 | yes | KexecBuilt + SpecKexec's PURE §1b | after KexecLoad |
| KexecPtImage.v | 541 | yes | KMap PtTree PtBuild UptTree ProcPtOwn UmCovered; restate over `procPtAt` (UPtDefs:148)/PtOwn | NOW, re-based |
| KexecBridge.v | 355 | yes | …UexecSlot SpecKexec; `exec_built_Q`, `exec_image_ok_of_built` | after D17 |
| SpecKexec.v | 1368 | the seal | …**UserFd ChildTok UexecSlot FsAbsEra SysOpenDefs**…; §1b pure :326–777 (`kexec_loadable`:344, `exec_fail_cause`:428, …; `kexec_image_ok`:403 and `exec_key`:479 need `uvis`); AU :778–1216 (`exec_slot_pre`:861 with `my_pay (uvis_gen W') Q`, `exec_au_pre`:904 = `ex_start` + `aopen_commit_at`, `exec_arms`:1107); `wp_kexec_frame`:1217, `KEXEC`:1346, **eb-generic** | §1b NOW as `KexecLoad.lean`; the rest last |
| SpecKexecB2.v | 907 | internal phase seal | ElfEnc W32Arith KexecDefs KexecOkQ ProofKexec{Parts,Tail,Seam} KexecPtImage KexecBuilt; `KEXECB2`:862, loadseg loop | stage (Lean: `KexecB2Spec.lean`, since it imports Proof-derived stages; no `Spec` prefix) |
| ProofKexecParts / Tail / Seam | 586 / 2231 / 1224 | stages | frame, `bad:` blocks, `kxc_at_12c/1a2`, `kxc_grow_inv` | Parts NOW; Tail/Seam after KexecBuilt |
| ProofKexecACode | 2370 | stage | +0x000..+0x08e; **plain `wp_namei_gen`**; `kxc_phaseA`:2168 | after C0 |
| ProofKexecA | 1251 | stage | **the ONLY `wp_namei_era` call (:480)**, `kxa_receipt` | after NameiEra + D17 |
| ProofKexecB / B2 / B3 | 1334 / 1884 / 4440 | stages | proc_pagetable, phdr loop + inlined loadseg, walkaddr, flags2perm, uvmalloc; panic live | after C0 |
| ProofKexecC | 5377 | stage | user stack, uvmalloc, uvmclear, argv loop (strlen, copyout) | after C0 |
| ProofKexecD | 2496 | stage | commit: `upd_exec`, name loop (safestrcpy), `proc_freepagetable` of the old table, **`pv_lazy := false`** | after C0 |
| ProofKexec | 1063 | seal | `KexecProof`:141 | last |
| SysExecDefs.v | 180 | yes | `K_sys_exec = 248`:158, `sys_exec_post` (`kexec_ok ∗ proc_priv`; `first_tok` note :164) | pure part NOW |
| SpecSysExec.v | 499 | seal | `exec_args_shape/_of`:165–196 (pure, NOW); `SYSEXEC`:480 PARKING :429, `my_pay`:450 | last |
| ProofSysExecParts / ProofSysExec | 4784 / 793 | stages / seal | argaddr, argstr, memset, fetchaddr, kalloc, fetchstr, kfree; `proc_priv_tfp_valid` | Parts after C0 |
| ElfKernel, ElfUser, ElfLoadable, Exec{Bundle,Entry,Run} | 201/504/153/1078 | **no** (boot/user lane) | — | out (D20) |

**Links:**
- `Kexec := KexecProof Myproc BeginOp Namei NameiEra Ilock Readi Iunlockput EndOp ProcPagetableGen
  ProcFreepagetable Walkaddr Flags2perm Uvmalloc Uvmclear Strlen Copyout Safestrcpy Panic`;
- `SysExec := SysExecProof Argaddr Argstr MemsetArray Fetchaddr Kalloc Fetchstr Kfree Kexec`.

Lean's Link theorems will also thread COPYOUT/COPYIN.

### 6.2 Process-layer touch points (FLAG every one)

| Rocq | Lean | action |
|---|---|---|
| `upd_exec` (sz, upt, tf, name; **`pv_lazy := false`**) | `pvLazy` exists (ProcDefs:158); no updater | record update `{ V with …, pvLazy := false }`; no ProcDefs edit needed |
| ProcInv accessors `proc_priv_newspace`(×8)/`addrspace`/`name`/`tf`/`trapframe`/`lazy`/`copy`/`cwd_pid`, `proc_priv_tfp_valid` | absent | ProcInv additions (C0's file): report exact statements; land after C0 |
| `proc_priv` with ofiles + `first_tok` (77 uses) | `procPriv` has neither | C0 P2 + D8 |
| `my_pay (uvis_gen W') Q`, `gen_kq` | `ChildTok.myPay`:234 (untracked, D8) | wait for D8 to land |
| `uvis`, `uvis_of`, `tf_w`, `tf_resume_*` (UexecSlot.v 378; imports UserPtTree, SpecUserret, UserPerm, FdSlots) | absent | D17 |
| `fs_fabric` | `FsReady` + `procsInv` + disk lock | KexecDefs |
| sys_exec's pinned eb | kexec is already generic | eb-generic (D5) |

### 6.3 The early landing (recommended)

The phases A-code, B, B2, B3, C and D compose into a landed WP over the plain `NAMEI` with the
`kexec_ok_q`/`kexec_closer` exits. That is Rocq's `kxc_phaseA` ∘ B..D, without the AU wrapper. Port
it as the internal stage `KexecCore.lean`, which is NOT a seal, so Rocq's single `KEXEC` seal stays
the only public contract. The era/AU layer (`KexecA`, SpecKexec AU, `KexecBridge`, `ProofKexec`) then
adds ~2.6k Rocq lines on top once NameiEra, D8 and D17 land.

## 7. Dependency DAG

```
LANDED: FsAbsDefs FsAbsDelta FsStateEra* FsStateTop FsTree PathElems DirView AppInv PieceFam FsReady
        FilePay OffBox UserOff ProcInv(procPrivCwd) namex/namei/nameiparent + all fs.c + non-fs callees

── era ─────────────────────────────────────────────────────────────────────────────────────────
FsAbsWalk ─→ FsAbsEra ─┬→ SpecNamexEra ─┬→ [NamexEra stages] ─→ ProofNamexEra ─→ LinkNamexEra ─┐
                       │                └→ SpecNameiEra ─→ ProofNameiEra ─→ LinkNameiEra ◄──────┘
                       └→ SpecNparEra ──┬→ [NparEra stages] ─→ ProofNparEra ─→ LinkNparEra ─┐
                                        └→ SpecNparWrapEra ─→ ProofNparWrapEra ─→ LinkNparWrapEra
── create ──────────────────────────────────────────────────────────────────────────────────────
FsAbsCreateFire(-§1c) ─→ SysMknodDefs ─→ FsAbsMknodFire(§2-4,§7) ─→ (+FsAbsEra) §5-6 append
CreateDefs ─→ CreateParts ─→ CreateFreshTy
SpecCreate ◄─ CreateDefs, FsAbsMknodFire§5-6, SpecNparWrapEra, [C0 names]
  ─→ CreateShared{Regs,Body} ─→ {CreateFound, CreateAlloc, CreateFail, CreateFailMkdir, CreateMkdir}
  ─→ ProofCreate ─→ LinkCreate (needs LinkNparWrapEra)
LinkCreate + C0 ─→ sys_mkdir chain, sys_mknod chain
── path syscalls ───────────────────────────────────────────────────────────────────────────────
SysUnlinkDefs ─→ FsAbsUnlinkFire(-dex) ─┐    SysLinkDefs ─┴→ FsAbsLinkFire
SysOpenDefs(§1-2) ─→ FsAbsOpenFire §2-3 append
C0 ─→ SpecSysLink ─→ SysLinkTails, SysLinkWalkA/B ─→ ProofSysLink ─→ LinkSysLink     (NO era)
LinkNameiEra + C0 ─→ SysOpenDefs(§3) , FsAbsOpenFire §1 ─→ SpecSysChdir ─→ … ─→ LinkSysChdir
LinkNparWrapEra + FsAbsMknodFire§3 + FsAbsCreateFire + C0 ─→ ufDex append ─→ SpecSysUnlink ─→ … ─→ LinkSysUnlink
LinkNameiEra + LinkCreate + C0 + W7-B ─→ openFdOk ─→ SpecSysOpen ─→ SysOpen* ─→ ProofSysOpen ─→ LinkSysOpen
── kexec ───────────────────────────────────────────────────────────────────────────────────────
ElfEnc, ElfFile ─→ ElfBridge ─┐
KexecDefs ────────────────────┼→ KexecBuilt(re-based) ─→ KexecImageAlg ◄─ KexecLoad(SpecKexec §1b)
KexecPtImage(re-based)        │
KexecParts ─→ KexecTail, KexecSeam ─┬→ (C0) KexecACode, KexecB, KexecB2Spec→KexecB2→KexecB3, KexecC, KexecD
                                    └→ KexecCore (landed WP over plain NAMEI)
C0 ─→ KexecOkQ;  SysExecDefs ─→ (C0) SysExecParts
LinkNameiEra + D8(ChildTok) + D17(uvis) ─→ KexecA, SpecKexec(AU), KexecBridge ─→ ProofKexec ─→ LinkKexec
LinkKexec ─→ SpecSysExec ─→ ProofSysExec ─→ LinkSysExec
```

**Critical path:** FsAbsWalk → FsAbsEra → SpecNparEra → NparEra walk (Rocq 5.9k) → NparWrapEra →
create (Rocq 14.3k) → sys_open (Rocq 11.9k). The kexec phases (Rocq ~24k) are the parallel long pole.
Its tail (KexecA/AU) joins after NameiEra, D8 and D17.

**Sizes (Rocq proof lines):**

| area | Rocq proof lines |
|---|---|
| era | 12.3k |
| create | 14.3k |
| mkdir + mknod | 4.0k |
| link | 7.4k |
| chdir | 2.5k |
| unlink | 12.5k |
| open | 11.9k |
| kexec | 24.3k |
| sys_exec | 5.6k |
| **total** | **~95k**, plus ~16k definitional/Spec |

## 8. Batch schedule

Main-tree agents only ADD files. Worktree agents edit landed files (the partial-file appends, the
ProcInv accessors). One family per agent. Wait messages say what to wait for.

### 8.1 Batch 7b-0: definitional, START NOW (no decision needed, no in-flight dependency)

| agent | files (in order) | notes |
|---|---|---|
| **E0** | `FsAbsWalk`, `FsAbsEra` (walk sections only) | the critical path's head. Check `eraNode_rec`, `dirEntries_eraNode` (FsStateEraPure:311/741), `icLoadedFlatBody` (IcacheEscrowDep:384), `topFragQ_split/agree` (FsStateTop) |
| **C-A** | `FsAbsCreateFire` (−§1c), `SysMknodDefs`, `FsAbsMknodFire` (§2–4, §7) | partial-port headers |
| **C-B** | `CreateDefs`, `CreateParts`, `CreateFreshTy`, `IregLinkNz` (missing lemmas only), `CreateBudget` (optional) | CreateFreshTy is the first eb-generic create piece |
| **O-A** | `SysUnlinkDefs`, `FsAbsUnlinkFire` (−dex), `SysLinkDefs`, `FsAbsLinkFire`, `SysUnlinkBudget`/`SysLinkBudget` (if consumed) | |
| **O-B** | `SysOpenDefs` (§1–2 + `openFdRcpt`), `SysOpenBudget` (−create lemmas unless CreateDefs has landed), `SysOpenBits`, `SysLinkParts`, `SysUnlinkParts`, `SysUnlinkPure` | pure stage files are a separate commit set from the defs |
| **K-A** | `ElfEnc`, `ElfFile`, `ElfBridge`, `KexecDefs`, `SysExecDefs` (pure), `KexecLoad` (SpecKexec §1b minus `uvis`), `KexecParts` | |
| **K-B** | `KexecBuilt`, `KexecPtImage` (re-based, D18), then `KexecImageAlg` | design-heavy. Post the representation plan to the coordinator before writing more than the stack algebra |

### 8.2 Batch 7b-1: after E0 lands (main tree)

- **E1 (one agent):** `SpecNamexEra`, `SpecNparEra` (+ `inodeHeldTyAt`), `SpecNameiEra`,
  `SpecNparWrapEra`. Small. Freeze and announce the four statements.
- **Worktree W-A (small):** append FsAbsMknodFire §5–6 and FsAbsOpenFire §2–3 (+ §1 after E1). Append
  SysOpenDefs §3 once §5–6 exist.

### 8.3 Batch 7b-2: after E1's statements are frozen (parallel)

- **E2 / E3: the era walks**, per D14.
  - (b): E2 builds the shared `NamexEra*` stages and the `ProofNamexEra` seal; E3 starts once E2's
    `NamexEraDefs` is frozen and does `ProofNparEra` plus any npar-only exits.
  - (a): E2 does NamexEra and E3 does NparEra, independently.
- **E4:** `ProofNameiEra`, `ProofNparWrapEra` + the four Links, as soon as E2/E3 land. Each wrapper
  needs only its walk's Spec to be written; its Link needs the walk's Link.
- **C-C:** `SpecCreate` (after E1 + C0 merge), `CreateSharedRegs`, then `CreateSharedBody`.
- **L-A: sys_link end-to-end** (after C0 merges): `SpecSysLink`, `SysLinkTails`, `SysLinkWalkA/B`,
  `ProofSysLink`, `LinkSysLink`. It has no era dependency, so it is the first syscall of the wave.
- **K-C (after C0 merges):** `KexecOkQ`, `KexecTail`, `KexecSeam`. Then in parallel, 4–5 agents:
  {`KexecACode`}, {`KexecB`}, {`KexecB2Spec`, `KexecB2`, `KexecB3`}, {`KexecC`}, {`KexecD`}. Then
  `KexecCore`. Also {`SysExecParts`}.
- **Worktree W-P (after C0 merges):** the ProcInv accessors: `procPriv_settle`, `procPriv_tf`,
  `procPriv_tfpValid`, the kexec `newspace` family. Rocq-literal statements; report them as
  process-layer additions (rule 3).

### 8.4 Batch 7b-3: after the Links of the era walks and `SpecCreate`

- **C-D (5 parallel agents on disjoint files):** `CreateFound` (needs SpecNparWrapEra),
  `CreateAlloc`, `CreateFail`, `CreateFailMkdir`, `CreateMkdir`. Then one agent for
  `ProofCreate`/`LinkCreate`.
- **H-A: sys_chdir** (after LinkNameiEra).
- **U-A..C: sys_unlink**, in three agents after LinkNparWrapEra + the `ufDex` append: {W1, W2},
  {W3, Shared, Tails}, {W5F, W5D}, then the seal.

### 8.5 Batch 7b-4: after LinkCreate

- **M-A:** sys_mkdir. **M-B:** sys_mknod (stable add-on deferred).
- **S-A..D: sys_open** (also after W7-B merges and the `openFdOk` worktree append). The disjoint
  stage sets are {Parts, Pub}, {Walk, Join, Shared}, {Alloc, Stores, Tails}, and {Plain, CreArm,
  EntryC}, then the seal.
- **K-D:** `KexecA`, SpecKexec AU, `KexecBridge`, `ProofKexec`, `LinkKexec`. This needs LinkNameiEra,
  D8 landed and D17. Then `SpecSysExec`, `ProofSysExec`, `LinkSysExec`.

**Parallelism.** 7 agents in 7b-0. About 9 in 7b-2, including the kexec fan-out. About 9 in 7b-3 and
about 8 in 7b-4.

## 9. Decisions for the coordinator (and, where marked, the user)

| # | decision | recommendation |
|---|---|---|
| **D14** | Shape of the two era walk proofs (Rocq: two ~5.5k-line copy-adapts of ProofNamex; Rocq's header calls copy-adapt "transitional by design") | **(b) one era stage set generic in `npar`, two Specs, two thin seals**. The landed Lean namex is already one proof for both arms, so this keeps Rocq's big idea (the lent era fragment, `elend_fire_hit/miss`, `ex_start`/`ep_start`) and changes only file layout. It touches no landed file and saves ~2.5k lines. (a) Rocq-literal twin copies is the safe fallback. (c) Generalising the LANDED namex stages with a trace hook would retire the duplication but edits landed proofs. Defer (c) as an optional cleanup |
| **D15** | FsAbs.v's iProp half (`nview`, `astate`, lend laws, `apn/apr`), FsAbsEra §0/§5, FsAbsCreateFire §1c, sys_mknod's stable add-on | **Defer and record** (the FsAbsReadFire §3 precedent). No kernel proof in 7b consumes them; their consumers are `*_pinned` lemmas / the stable add-on (none) and the user lane |
| **D16** (process, → user) | Block form of the 7b contracts | fs-internal contracts (era walks, create) state the SpecNamex rows / **`procPrivCwd`**, not Rocq's whole `proc_priv`: frame-stronger, the landed fs convention. **Flag** create as a deviation. The sys_* frames take **C0's P2 block** (Rocq's `proc_priv`) and are written after C0 merges. D8's `first_tok`/`GenId` enter through the block when D8 lands. Record which D8 conjuncts are absent at landing time |
| **D17** (scope, → user) | SpecKexec needs `UexecSlot.uvis` (a pure record; imports UserPerm's `uperm`, SpecUserret's resume helpers), `ChildTok.my_pay` (D8) and a `UserFd` section binder. `S` is a parameter, so NOT `uslot` | **Port a minimal `UexecSlot.lean` (the `uvis` record, `uvis_of`, `tf_w`, `tf_resume_*`) plus the `uperm`/`perm_of` subset of UserPerm** as definitional files in 7b. Drop the unused `ufdG` binder (record). The rest of the user-mode layer stays in wave 8 (D12). Alternative: land `KexecCore` only and defer the KEXEC seal to wave 8 |
| **D18** (representation) | KexecBuilt/KexecPtImage over Rocq's `gmap Z` user memory and `perm_of` vs Lean's per-page `M : Nat → List (BitVec 8)`, `UPtd`, `procPtAt` | **Re-base onto the Lean representation**, recorded as a deviation in each header. K-B posts the plan first. It must match what landed `uvmalloc`/`copyout`/`walkaddr` Specs already say |
| **D19** | Rocq ProofNameiEra/ProofNparWrapEra import ProofNamei/ProofNameiparent (Proof→Proof) | Restate the ~6 pure lemmas locally (`nameiEra_*`, the ProofNameiRoot precedent). Promoting them into `NameiFrame` is the alternative (landed edit, worktree) |
| **D20** | Out of 7b: FsAbsInvFire, PinnedOpen, FsSyscalls, ElfKernel/ElfUser/ElfLoadable, Exec{Bundle,Entry,Run}, FsLookup, FsRep | **Out.** FsAbsInvFire/FsSyscalls go with the dispatch/user lane (wave 8). FsLookup/FsRep are dead |
| **D21** | New file names that split one Rocq file: `CreateDefs` (from SpecCreate), `SysLinkDefs` (from SpecSysLink), `KexecLoad` (SpecKexec §1b), `FsAbsWalk` (FsAbs §4 partial), `KexecB2Spec` (SpecKexecB2 as a stage), `KexecCore` | Approve. Each header names its Rocq origin; the one-file-per-Rocq-file rule is otherwise kept |
| **D22** | fs-rocq-summary.md §7.9 is wrong (era "optional"; omits NparEra/NparWrapEra; the Tr family is gone) | Coordinator edits the notes (this brief is read-only) |

D5 (eb-generic: create, sys_open/link/unlink/mkdir/mknod/chdir/exec) and D11 (drop the crash
layer) carry over from fs7 and are applied by every 7b agent without further asking.

## 10. Risks

1. **C0's slot-supply rename** (rule 5) and the P2 block. Any Spec that states `fdSlot`/`bslots`/the
   block before C0 merges must be re-cut. Hold every sys_* frame, SpecCreate and KexecOkQ until C0
   merges.
2. **The era lend leg.** `elend_fire_hit/miss` needs the payload's `topFrag` leg OUT of the loaded
   bundle at dirlookup's continuation. The landed NamexLook keeps it inside the rebuild wand. The era
   Look stage must open `icLoadedFlatBody` itself. Check that ilock/dirlookup's landed posts give
   enough of the bundle to do it, before writing the loop.
3. **Relative-path start.** Some Rocq headers say the relative start is "refuted". That is stale:
   both walks fire `ex_start` at idup's inum (ProofNamexEra :4986/:5171, ProofNparEra :5541/:5727).
   Port both starts.
4. **create's eb generalisation** touches every callee call in five stage files (13 Rocq `rewrite
   Heb` sites). Budget the `k_ext_move` threading into C-D.
5. **The kexec representation re-base (D18)** is the single riskiest design item in 7b. K-B must not
   transcribe `gmap` lemmas.
6. **Stale Rocq prose:** ProofNamexEra:790 (eb), the relative-start comments, and SpecNamexEra's
   header (Tr, `dv_half`, retired 2026-08-30). The CODE and the Spec bodies are the reference.
7. **Budget clash.** sys_link's found arm busts the COUNTED namei form by one (SysLinkBudget:196).
   Use the set-form (`_gen`) callees throughout, as Rocq does.
8. **Rebuild cost.** Every appended landed file (FsAbsOpenFire, FsAbsMknodFire, FsAbsUnlinkFire,
   SysOpenDefs, ProcInv) should be ONE worktree commit per append wave, not one per section.

## 11. Report (per agent)

As fs1 §7 and fs7 §10, plus:
- for each Rocq file: the sections ported and the sections deferred (with the reason and the
  consumer grep);
- every eb generalisation (Rocq pin → Lean generic);
- every process-layer touch (Rocq name → Lean form → reason), flagged;
- every statement that names a C0/D8 object, with the in-flight file it was checked against.
