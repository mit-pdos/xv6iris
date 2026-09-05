# Round E2 — design proposal (2026-09-05): AU forms for create's legs, link, mkdir, iput's free, write; the view; the rulings needed

STATUS: PROPOSAL awaiting the owner's rulings on Q-a..Q-i (last section).  Produced read-only against HEAD 668441141 after round E1's census; every claim carries file:line.  Design of record: design/applications.md §2/§6 L3; rounds record: app-instances.md §7 E.


Scope: app-instances.md §6 ruling 4 / §7 E, applications.md §2 + §6 L3, fs-syscall-specs.md §4/§7.
Census input: roundE1-census.md (22 helper-level sites = 17 `_auto` + 5 `_armed_auto`).  All line
numbers below are at HEAD 668441141 (E1 shifted two census rows: #21 6630→6621, #26 6910→6901).

Three measured facts that shape everything below:

- F1. `abs_view I := abs_of <$> I` over the whole region map (FsAbsDefs.v:381; `app_dom I` = the
  region, AppInv.v:200).  The W lane RECORDED this as a deliberate deviation from doc §4: "`∃ i ∉ dom
  av` UNSTATABLE over the landed astate (the authority rows the whole region) — replaced by the
  minted-orphan observation" (projects/fs-syscall-specs.md:418-420).  That observation is
  `cre_pre`'s third conjunct `av !! i = Some (MkAnode c 1)` (SpecSysMknodAU.v:305-309): the create
  fire is honest ONLY because the child's leg was already moved by `_auto` retags before it
  (`delta_create_dev` collapses the fused delta to the parent row, SpecSysMknodAU.v:322-336;
  FsAbsMknodFire.v:431-443 `Hpre`/`Hdelta`).
- F2. The dispatcher runs write/link/close/mkdir/exit on `_sconf` (ProofSyscall.v:4402, 4947,
  5052, 5504, 4239) and unlink/mknod/open/chdir/exec on AU (4847, 5622, 5779+5800, 4707, 4041).
  The non-AU unlink arm is WITHDRAWN (3943-3949 comment).
- F3. Every generic discharger of the six AU fires pays its `app_step` off the PARKED LICENSE via
  `app_step_acc` (FsAbsMknodFire.v:220/281, FsAbsInvFire.v:217, FsAbsWriteFire.v:477,
  SpecSysUnlinkAU.v:517/528, SpecSysOpenAU.v:493/511; `syscall_env_fsabs` = `app_inv`,
  FirstTok.v:345).  So `app_auto`/`Happ_auto` (App.v:174-175) are the dispatcher's ONLY step source
  until L2 gives it a per-ecall one.  E2 can delete `top_move`, `ireg_top_retag_auto`,
  `_armed_auto` and `app_top_update_auto`; it CANNOT delete `app_auto`/`Happ_auto` without L2.
  applications.md §2/§6 L3 say "then … `Happ_auto` are deleted" — that clause belongs to L2.

## 1. The 22 sites: view change, dispatcher arm, twin, liveness

Notation: `c0(ty)` = `AFile []` / `ADir ∅` / `ADev 0 0` (ialloc zeroes the record: `fresh_shape`,
ProofIlock.v:1233-1246).  `free(d)` = `abs_of (free_node d)` = `MkAnode (ADev ma mi) 0` with the
CORPSE's major/minor (InodeRegion.v:481-482; FsAbsDefs.v:82-87).  "live" = on a dispatched path.

| # | HEAD site | anode before → after | reached via (dispatcher arm) | AU twin of the same path | live? |
|---|---|---|---|---|---|
| 1 | EscrowDeposit.v:243 (`ireg_free_deposit_au`, :62) | orphan `MkAnode c 0` → `free(dn')` | every iput: close sconf (5052→ProofSysClose.v:861 fileclose→iput), exit sconf, unlink AU's own `iunlockput(ip)` (SpecSysUnlinkAU.v:50-62), chdir AU (ProofSysChdirAU.v 1 iput), namex/open/exec/link/mkdir tails | none (no iput AU) | LIVE |
| 2 | ProofIlock.v:1271 (ilock at `ClaimK ty`, SpecIlock.v:329/567) | `free(d)` → `MkAnode c0(ty) 0` | every create: mknod AU, open AU create, mkdir sconf | it IS the only form | LIVE |
| 3 | ProofSysOpen.v:1199 (`so_stores`, :580) | `AFile bs` → `AFile []` (trunc) | non-AU open (not dispatched) | `so_stores_au` (ProofSysOpenAUStores.v:169) fires `opf_atrunc_fire` | DEAD |
| 4 | ProofSysLinkTails.v:1438 (`sl_tail_bad`, :1027) | target nlink+1 → nlink (undo) | link sconf (4947) | none | LIVE |
| 5 | ProofFilewrite.v:2314 | `AFile bs` → `AFile (splice…)` | write sconf (4402) → ProofSysWrite → ProofFilewrite | `wp_sys_write_au` (SpecSysWriteAU.v:661) NOT dispatched (§7) | LIVE |
| 6 | ProofFilewriteAU.v:2971 (`rz ≠ c` arm) | short chunk: bytes moved; `rz=-1`: unchanged | write AU (not dispatched) | it IS the AU form; the partial arm `fw_au_raw_spend_part` (SpecFilewriteAU.v:330) hands `awrite_part_at` = OFFSET ONLY, no state fire (FsAbsWriteFire.v:425-428) | DEAD today, live once §7 lands |
| 7 | ProofCreateAlloc.v:1244 (`cr_alloc_half`, C-OK-FILE arm) | parent ents += nm | non-AU create's non-dir arm: only non-AU open/mknod (not dispatched; mkdir leaves at +0xca into `cr_mkdir_half`, ProofCreate.v:227) | `mkf_acre_fire`/AUF fire | DEAD |
| 8 | ProofCreateShared.v:1634 `cr_dirty_arm` ← ProofCreateAlloc.v:453 | `MkAnode c0 0` → `MkAnode c 1` (+major/minor) | mkdir sconf (before the type branch) | ProofCreateAU/AUF's own copies (#18/#23) | LIVE |
| 9 | ProofCreateShared.v:1649 `cr_dirty_retag` ← ProofCreateMkdir.v:2510 | child `ADir{.,..}` nlink 1 → nlink 0 (parent-append failed) | mkdir sconf | none (no T_DIR AU) | LIVE |
| 10 | same helper ← ProofCreateMkdir.v:2648 | child `ADir{.}` nlink 1 → 0 (".." failed) | mkdir sconf | none | LIVE |
| 13 | ProofCreateShared.v:1665 `cr_dirty_clear` ← ProofCreateMkdir.v:2344 | `ADir ∅` → `ADir{.,..}` at nlink 1 | mkdir sconf | none | LIVE |
| 13b | same helper ← ProofCreateFailMkdir.v:494 (NOT in the E1 table) | dotless child nlink 1 → 0 (mkdir A-FAIL) | mkdir sconf | none | LIVE |
| 14 | ProofCreateMkdir.v:2110 | parent ents += nm AND nlink+1 (fused) | mkdir sconf | none | LIVE |
| 16 | ProofCreateFail.v:474 (`cr_fail_half`) | child nlink 1 → 0 (non-dir dirlink failed) | non-AU open/mknod only | AU fails #21/#26 | DEAD |
| 18 | ProofCreateAU.v:1718 `cr_dirty_arm` ← :4873 | as #8 | mknod AU | — | LIVE |
| 21 | ProofCreateAU.v:6621 | child nlink 1 → 0 | mknod AU (dirlink failed) | — | LIVE |
| 23 | ProofCreateAUF.v:1739 `cr_dirty_arm` ← :5155 | as #8 | open AU create | — | LIVE |
| 26 | ProofCreateAUF.v:6901 | child nlink 1 → 0 | open AU create (dirlink failed) | — | LIVE |
| 28 | ProofSysLink.v:1934 | target nlink+1 | link sconf | none | LIVE |
| 29 | ProofSysLink.v:3091 | parent ents += nm | link sconf | none | LIVE |
| 31 | ProofSysUnlinkW5File.v:1391 | parent: entry deleted | non-AU unlink (withdrawn arm) | `uf_uent_fire` (FsAbsUnlinkFire.v:359) | DEAD |
| 32 | ProofSysUnlinkW5File.v:1777 | target nlink−1 | non-AU unlink | `uf_utgt_fire` (:457) | DEAD |
| 33 | ProofSysUnlinkW5Dir.v:1971 | parent: entry deleted, nlink−1 | non-AU unlink | AU W5D | DEAD |
| 34 | ProofSysUnlinkW5Dir.v:2402 | child dir nlink−1 (→0) | non-AU unlink | AU W5D | DEAD |

Summary.  LIVE: #1, #2, #4, #5, #8, #9, #10, #13, #13b, #14, #18, #21, #23, #26, #28, #29 (16 rows;
helper-level: Shared's arm/retag/clear + AU's arm + AUF's arm + 9 direct sites).  DEAD-for-the-theorem
(reachable only through a non-dispatched contract): #3, #6, #7, #16, #31–#34 (8 rows).  The non-AU
write's retag (#5) IS live — `wp_sys_write_sconf` is what the theorem runs.  Consumers of the dead
forms outside their own Spec/Proof/Link files: none (`wp_sys_unlink_sconf`, `wp_sys_open_sconf`,
`wp_sys_mknod_sconf` have zero external consumers; `wp_create_sconf` has SysOpenBudget.v:12 as a
comment only).  The non-AU unlink W-files are imported only by ProofSysUnlink.v (dead);
`ProofSysOpen.v` stays because the AU open reuses `so_entry_n`/`so_join` (ProofSysOpenAUWalk.v:2,
ProofSysOpenAUJoin.v:2) but `so_stores` itself has no AU caller.

## 2. The child leg of create

What the machine does to the map, in order (`ialloc; ilock; nlink=1,iupdate; [dots]; dirlink(dp)`):
(i) the CLAIM at ilock (#2: row appears typed at nlink 0), (ii) the ARM (#8/#18/#23: nlink 0→1,
major/minor), (iii) for T_DIR the dot writes (#11 same, #13 D), (iv) the PARENT fire (`mkf_acre_fire`
/ AUF / #7 / #14).  Three view moves on the child's key before the parent's, each at its own instant,
each a kernel-truth map move (the map follows the disk write: durable-disk 2b-inode-3; the commit's
collection reads the map, `app_dom`).

- (a) Two-key step at the fire.  IMPOSSIBLE without rewriting the map discipline: at the fire the
  child's row is ALREADY `MkAnode c 1` (F1; `Hlkc`/`Habsc`, FsAbsMknodFire.v:430-433).  A two-key
  insert would need the map to lag the disk between ialloc's write and dirlink's commit, i.e. the
  ilock/iupdate/dot movers would have to stop retagging.  Rejected.
- (b) Separate steps per leg, carried by the same contract.  This is UNLINK'S PRECEDENT: "THE DELTA IS
  TWO INSTANTS" (`delta_unl_ent`/`delta_unl_tgt` fired separately, `delta_unlink_split` ties the
  fused doc delta to the halves, SpecSysUnlinkAU.v:73-108, 387-391; ProofSysUnlinkAUW5F.v:1-30).
  Create becomes "THREE INSTANTS": `delta_claim i c0`, `delta_arm i c` (child → `MkAnode c 1`),
  `delta_ent d nm i` (parent, with `acre_bump`), and `delta_create_split : cre_pre-free premises →
  delta_create d nm i c av = delta_ent d nm i (delta_arm i c (delta_claim i c0 av))`.  The contract
  bundle gains `aclaim_commit_at` and `aarm_commit_at` beside `acre_commit_at`; the claim step rides
  ilock's `ClaimK ty` payload (§8), the arm step is a premise of `cr_dirty_arm` (→ `_armed_step`).
  Cost: FsAbsDelta +~120 lines (pure), SpecCreateAU/AUF/SpecCreate + SpecSysMknodAU/OpenAU bundles
  +2 commits each, three `cr_dirty_arm` bodies (1-line change each) and their 3 callers, ilock's
  ClaimK payload (SpecIlock/ProofIlock/ProofCreateFreshTy), dispatcher: nothing (the dischargers
  are `_unit`-shaped off the license, F3).  Mechanical once the deltas exist.
- (c) Redefine the view to allocated rows only.  This is what doc §4 SAYS (`∃ i ∉ dom av`; `δ_free i:
  delete i from aview`) and the W lane's reason for deviating is gone once the view (not the
  authority) filters: `astate Γ av := ∃ I, auth I ∗ ⌜av = abs_view I⌝` (FsAbsReadFire.v:21) is
  statable at a filtered `abs_view`.  Cleanest cut: `abs_of : fs_node → option anode` (None at
  `fn_type = 0`), `abs_view I := omap abs_of I`; `_same` keeps its statement (`abs_of n = abs_of n'`
  as options), `nview` becomes `⌜abs_of n = Some a⌝`, `abs_of_dev` gains `fn_type n ≠ 0`.  Ripple:
  36 files name `abs_of` (FsAbsDefs 27 uses, the four fires 13-18 each, FsAbs 15, FsAbsReadFire 14,
  the rest ≤9), 33 name `abs_view`; every use is a row-reading lemma, none inspects a free row (the
  pins FsInitPin/FsShPin/SpecKexecPin/FdRowMint read typed nodes).  What it buys: `delta_claim` =
  "i appears at `MkAnode c0 0`", `delta_free` = `delete i` — the doc's words; without it `delta_free`
  must expose the corpse's major/minor (`free(d)`), and the claim step's before-row is
  record-dependent (a T_DEVICE child from a zeroed corpse is even `_same`).  What it does NOT buy:
  fewer steps — (i), (ii), (iv) and the free stay view changes.  Under (c) they land exactly where
  they land today.

RECOMMENDATION: (b), with (c) adopted FIRST as its own lane (E2-V) so the new deltas are minted in
the doc's vocabulary.  (b) without (c) is the fallback (same site work, uglier deltas).

## 3. Failure arms (child nlink 1→0 after a failed dirlink / mkdir dot)

Sites #9/#10/#13b/#16/#21/#26 (and #4 for link).  Net view across the syscall is unchanged only
AFTER the tail's `iunlockput(ip)` frees the child (#1) — the machine really exposes `MkAnode c 1`,
then `MkAnode c 0`, then the free, at three instants, and a concurrent `ilock` of the inum can see
each.  Restructuring so the child is exposed only after success is not available: the code order is
`ialloc; iupdate(nlink=1); [dots]; dirlink`, and the map must follow each write (§2(a)).

Proposal: a do-then-undo pair in the contract.  The create bundle's FAIL arm (`cau_fail`,
SpecCreateAU.v:166-183 — today it returns the UNFIRED `acre_commit_at`) additionally carries
`aunarm_commit_at` (`delta_unarm i` : `MkAnode c 1 → MkAnode c 0`), fired at the `sh zero,74(s3)`
retag; the child's subsequent free is #1's step (§6).  For the generic app the discharger is the
usual `_unit`.  For a real application the pair is what it is: it admits "a typed row appears and
disappears" — an application whose claim is "the visible tree equals X" pays these trivially only if
its predicate ignores nlink-0 rows without an entry, which is the application's business (echo pays
by taint anyway).  `cr_dirty_retag` (#9/#10) becomes `_armed_step` with the same unarm step (the dot
entries ride along in the same node: `delta_unarm` is stated as "nlink → 0, content free").

## 4. Link

Code: `ilock(ip); nlink++; iupdate; iunlock` (instant 1, #28) — `nameiparent; ilock(dp); dirlink`
(instant 2, #29) — on failure `ilock(ip); nlink--; iupdate` (instant 3, #4).  Doc §4 puts "the AU on
the SECOND instant"; the machine has the target's count up BEFORE the entry exists and a concurrent
observer sees it (same stance as unlink's two instants, SpecSysUnlinkAU.v:95-108).  So the honest AU
form mirrors unlink: `delta_link_tgt t` (nlink+1), `delta_link_ent d nm t` (entry), the fail arm's
`delta_link_untgt t` (nlink−1), and `delta_link d nm t = delta_link_ent ∘ delta_link_tgt` with
`delta_link_split` under `link_pre` (target is a file/dev, `ents !! nm = None`).  Three fires
(`FsAbsLinkFire.lf_tgt_fire / lf_ent_fire / lf_untgt_fire`, copies of `uf_utgt_fire`/`uf_uent_fire`
FsAbsUnlinkFire.v:359-489), each carrying `app_step` at its key; the cross-of-life arm (target
unlinked between instants) is statable because instant 1 has its own receipt.

Structure/cost.  `ProofSysLink.v` is ONE lemma `wp_sys_link_sconf` (749→3891, ~3.1k lines) plus six
tails in ProofSysLinkTails.v (`sl_tail_b/c/d/bad/f/e2`, 141-1967) — MONOLITHIC, not W-staged.  The
AU unlink twin cost ~9.4k lines of copy-adapt (AUW1 964 + AUW2 1458 + AUW3 1928 + AUW5F 1863 +
AUW5D 2484 + Parts 405 + AU 267).  An R10 parallel twin of link would be ~5k lines AND would not
retire #4/#28/#29 (they stay in the sconf proof, which must also lose `_auto`).  `wp_sys_link_sconf`
has no consumer but the dispatcher.  RECOMMENDATION: convert IN PLACE — `SpecSysLink` gains the
three-commit bundle (`alink_commits`), the three retags become the three fires, the dispatcher passes
the `_unit` dischargers (as it does for unlink, ProofSyscall.v:4847-4855).  Cost: SpecSysLink +~60
lines, FsAbsLinkFire ~350 lines (new, cloned), three site edits + two tails' binders; one owner
waiver of R10 for link (Q-c below).

## 5. Mkdir

`wp_sys_mkdir_sconf` → `Create.wp_create_sconf` at `SpecCreate.T_DIR_ty_ok` (ProofSysMkdir.v:1185-
1193).  The AU create is pinned at `ty = T_DEVICE` (SpecCreateAU.v:32-42, :238) and its twin at
`T_FILE` (SpecCreateAUF.v:17-24); BOTH refute the mkdir arm ("the [beq s4,1] … never takes the
directory arm").  Measured: the AU create does NOT support T_DIR; `om_create`/`cr_dirty_*` for dirs
exist only in the non-AU `cr_mkdir_half` (ProofCreateMkdir.v:201) and `cr_fail_mkdir_half`.  A third
twin at T_DIR would be ~7.5k lines (each twin: ProofCreateAU 7140 / AUF 7419) PLUS the mkdir body
(2867 + FailMkdir) — the cross-product the guiding principle forbids.

The fused delta already exists: `delta_create d nm i (ADir dots)` with `acre_bump (ADir _) = 1`
(FsAbsDelta.v:48-70).  At #14 the child is `MkAnode (ADir {.,..}) 1` so `cre_pre` holds and
`delta_create_parent` gives `nl + 1` (FsAbsDelta.v:72-81) — the parent fire is `mkf_acre_fire`'s
shape at `c := ADir dots` verbatim; the dot write #13 is a child-key step `delta_dots i` (`ADir ∅ →
ADir {".":=i, "..":=d}` at nlink 1) fired at `cr_dirty_clear`.  RECOMMENDATION: dispatch mkdir
through the GENERAL create by strengthening `wp_create_sconf` in place (it is the only create over
an unpinned `ty`): its contract gains the create bundle (claim/arm/[dots]/ent + unarm), all 8 of its
movers become fires or `_step`, `wp_sys_mkdir_sconf` threads the bundle, the dispatcher passes
`_unit`.  Later (not E2) the two pinned twins are instances of it and can be deleted (−14.5k lines;
their era-walk/trace shape has to be folded into the general contract first — an owner-scoped lane).

## 6. `iput`'s free (#1)

Who pays: whoever's syscall runs the LAST iput of an nlink-0 inode — close/exit (fileclose), unlink's
own tail, chdir's old cwd, namex's intermediate `iput`s, open/exec failure paths, link/mkdir tails.
The unlink AU's `delta_unl_tgt` covers nlink−1 ONLY; the free is a separate instant inside
`iunlockput(ip)` and the contract says so ("NOTHING ABOUT δ_free … IPUT's business", SpecSysUnlinkAU.v
:50-62; doc §7's close/iput row).  Under §2(c) the step is `app_step i I (delete i (abs_view I))`
(`delta_free`); without (c) it is the corpse row `free(d)`.  Under (c) the free is NOT `_same`
(orphans are IN the view by doc §1 ruling and by `SpecSysReadAU.v:725`'s `⌜av !! i = Some (MkAnode
(AFile bs0) nl)⌝` on an unlinked fd); only a view filtered by `nlink > 0` would make #1 AND #2 `_same`,
and that contradicts doc §1 — listed as Q-b, not recommended.

Proposal: `SpecIput` gains `afree_commit_at Γ appE Φ` (mold: `uf_utgt_fire`'s two phases), fired in
`ireg_free_deposit_au` in place of EscrowDeposit.v:243 (`FsAbsFreeFire`, ~250 lines); the arm is
taken only on the free path (nlink 0 ∧ ref 1), elsewhere the commit is returned unfired (the `cau_fail`
shape).  Threading: `wp_iput_*` has 14 caller files (LinkIput, ProofDirlink, ProofFileclose,
ProofIunlockput, ProofIreclaim, ProofKexit, ProofNparEra, ProofIput, ProofSysChdir(AU), ProofNamex,
ProofSysLink, SpecIunlockput, SpecIput) — each contract gains the commit as a pass-through premise, and
every syscall contract that may iput gains it (close, exit, chdir AU, unlink AU, open AU, exec AU,
link, mkdir, mknod AU); the dispatcher passes `afree_commit_at_unit`.  Alternative (Q-d): a
PERSISTENT per-process give parked in the ecall payload (L2's "deposit shape") read off `proc_priv`
at iput — no threading, but a new read path for an application resource inside a kernel callee (a
design change, not E2's).  RECOMMENDATION: thread (the mechanism the six fires already use); L2
connects the process's give to the same bundle later.

## 7. Non-AU write, open-trunc, AU short chunk (#5, #3, #6)

- `wp_sys_write_au` is the FD-ROW form: it needs `arg_fd v (pv_ofile (us_V U)) = Some (fd, fv)` and
  the process's `fd_st … (FdOpen rb true (FdInode i γo))` fragment (SpecSysWriteAU.v:588-660, items
  33/46), so it covers FD_INODE only; pipe/device arms live in the sconf (and SpecSysWriteConsAU).
  It lacks nothing as a proof (0 admits) — it lacks a DISPATCH: the generic arm must case-split on
  the fd's state, which the dispatcher CAN do (`proc_priv_lend` hands `fd_st_auth` at an existential
  `stf`, ProofSysWriteAU.v header item 2).  RECOMMENDATION (W1): the write arm splits `arg_fd`/`stf`:
  FdInode → `wp_sys_write_au` with `_unit` chain; else → `wp_sys_write_sconf`.  #5 then leaves the
  theorem's path but stays in the build: `SpecFilewrite`'s inode arm gains a raw step premise
  (`∀ I off bs, app_step i I (delta_write i off bs (abs_view I))`) and #5 becomes `_step`; the
  dispatcher's non-inode calls supply it trivially.  (W2, in-place bundle on the sconf and deleting the
  ~9k-line AU twin, is the guiding-principle end state but re-cuts the fd-row pilot's contract — Q-e.)
- #3: `so_stores` is dead (the AU open has `so_stores_au` firing `opf_atrunc_fire`,
  ProofSysOpenAUStores.v:169; FsAbsOpenFire.v:329 pays `app_step_at`).  DELETE `so_stores` and the
  non-AU open walk's callers of it (ProofSysOpen keeps `so_entry_n`/`so_join` for the AU walk).
- #6: a REAL contract hole.  The short-chunk arm (`0 < rz < c`) moved bytes but `fw_au_raw_spend_part`
  hands only `awrite_part_at` = the offset half's move with no state fire (FsAbsWriteFire.v:425-428;
  ProofFilewriteAU.v:2971-2985).  Fix: the chain node's partial arm becomes an `awrite_commit`-shaped
  fire at the SHORT run (`delta_write i off (take rz bs)`) plus the offset move; the `rz = -1`
  sub-arm keeps `Hjoin`'s equalities (ProofFilewriteAU.v:2676-2684 currently drops `dn' = dnl` etc.)
  and takes `_same`.  Cost: SpecFilewriteAU chain (+1 arm), FsAbsWriteFire (+1 lemma), one site split.

## 8. `ProofIlock.v:1271`

The fill of a FRESH inode at `ilock` when the withdrawn fragment is a claim box: `n0` (∃, the region's
free-row fragment from `ireg_withdraw`) → `era_node dn bm_empty zeros` where `dn` is the record ialloc
wrote (type `ty`, everything else 0: `fresh_shape`, ProofIlock.v:1233-1246, `Hlocbox`).  View:
`free(d)` → `MkAnode c0(ty) 0` (under (c): row appears).  It fires only on the `ClaimK ty` index —
"create's child fill, and the only site that can present" it (SpecIlock.v:329, :567); the payer is
create, through `ireg_wd_lic (ClaimK ty)` (ProofCreateFreshTy.v:587-588).  Proposal: the `ClaimK`
payload carries `aclaim_commit_at` (`delta_claim i c0(ty)`), ProofIlock fires it at :1271, the three
creates (ProofCreateAlloc via FreshTy, ProofCreateAU, ProofCreateAUF) take it from their bundle
(§2(b)).  Non-create callers of ilock are at other indices and owe nothing.

## 9. Order and cost (each lane a green gate; GCP builds)

| lane | what | files (≈lines) | kind |
|---|---|---|---|
| E2-V | view := allocated rows (`abs_of` → option, `abs_view := omap`) | FsAbsDefs, FsAbs, 4 fires, ~30 consumers (premise/1-line each) | mechanical AFTER ruling Q-a |
| E2-D | deltas: `delta_claim/arm/unarm/dots/free/link_tgt/link_ent/link_untgt/link`, `delta_create_split`, `delta_link_split`, `fs_delta` union | FsAbsDelta (+~250), SpecSysUnlinkAU's split as mold | mechanical, pure |
| E2-C | create legs: `FsAbsClaimFire`/arm/unarm/dots lemmas; ClaimK payload; `cr_dirty_{arm,retag,clear}` → `_armed_step`; bundles in SpecCreate/AU/AUF, SpecSysMknodAU/OpenAU | ProofIlock, SpecIlock, FreshTy, 3 Shared-copies, ProofCreate{Alloc,Mkdir,Fail,FailMkdir,AU,AUF}, 2 spec bundles (#2,#7,#8,#9,#10,#13,#13b,#14,#16,#18,#21,#23,#26) | mechanical after Q-c waiver for SpecCreate |
| E2-F | iput AU: `FsAbsFreeFire`, `afree_commit_at` in SpecIput, deposit fire, 14-file threading, dispatcher `_unit` | EscrowDeposit, SpecIput, 12 callers, 9 syscall specs (#1) | mechanical after Q-d |
| E2-L | link in place: `FsAbsLinkFire`, `alink_commits` in SpecSysLink, 3 sites (#4,#28,#29) | SpecSysLink, ProofSysLink, ProofSysLinkTails, dispatcher | mechanical after Q-c |
| E2-W | write: dispatcher fd case-split → AU; #5 `_step` premise; #6 partial-arm fire + `_same`; delete `so_stores` (#3) | ProofSyscall write arm (~150), SpecFilewrite, ProofFilewrite, SpecFilewriteAU, FsAbsWriteFire, ProofFilewriteAU, ProofSysOpen | needs Q-e; #6 fix is a contract change |
| E2-X | delete the dead non-AU unlink walk (#31–#34: ProofSysUnlink + W1/W2/W3/W5File/W5Dir/Tails/Shared/Parts, LinkSysUnlink) and non-AU mknod (ProofSysMknod, LinkSysMknod) | ~10 files, −~10k lines | needs Q-f |
| E2-Z | delete `top_move`, `ireg_top_retag_auto`, `_armed_auto`, `app_top_update_auto`; `app_auto`/`Happ_auto` STAY (F3) with the doc corrected | InodeRegion, AppInv, applications.md §2/§6, app-instances.md §7 | mechanical |

Suggested order: Q-a..Q-f rulings → E2-V → E2-D → E2-C → E2-F → E2-L → E2-W → E2-X → E2-Z.  E2-C/F/L
are independent after E2-D and can run as parallel lanes on the VM.

## Open questions for the owner

- Q-a (choice).  View = allocated rows only (`abs_of : fs_node → option anode`), per doc §4's `∃ i ∉
  dom av` / `δ_free = delete`, retiring the W lane's recorded deviation?  RECOMMEND YES, first lane
  (E2-V); cost ~36 files mechanical, one design change in FsAbsDefs.  NO = mint `delta_claim`/
  `delta_free` over the whole-region view (corpse major/minor exposed in the free delta).
- Q-b (yes/no).  Filter the view by `nlink > 0` instead (makes #1 and #2 `_same`)?  RECOMMEND NO: it
  contradicts doc §1 ("orphans are IN the map") and unspecifies read on an unlinked fd
  (SpecSysReadAU.v:725).
- Q-c (yes/no).  Waive R10 (parallel forms) for the contracts with no consumer but the dispatcher —
  `wp_sys_link_sconf`, `wp_sys_mkdir_sconf`, `wp_create_sconf`, `wp_iput_*`, `wp_sys_close_sconf` —
  and strengthen them IN PLACE with commit bundles?  RECOMMEND YES: twins cost ~5–9k lines each
  (unlink's did 9.4k) and do not retire the `_auto` sites in the originals.
- Q-d (choice).  The free step reaches `iput` by THREADING a commit premise through 14 caller files
  and 9 syscall specs, or by a per-process PERSISTENT give read off `proc_priv` inside iput (L2's
  shape, a new read path)?  RECOMMEND threading (E2-F, mechanical); L2 attaches to the same bundle.
- Q-e (choice).  Write: W1 = dispatcher case-splits the fd and runs `wp_sys_write_au` for FdInode
  (sconf keeps pipe/device; #5 gets a raw step premise); W2 = the sconf write gains the AU bundle in
  place and the AU twin (~9k lines) is deleted later.  RECOMMEND W1 now (the AU form is the fd-row
  pilot's contract and belongs on the theorem's path); W2 as a later consolidation.
- Q-f (yes/no).  Delete the dead non-AU unlink walk and non-AU mknod (E2-X, −~10k lines, retires
  #31–#34) rather than converting them?  RECOMMEND YES (guiding principle: no near-duplicate walks).
  Also delete `so_stores` (#3).
- Q-g (yes/no).  Correct applications.md §2/§6 L3 and app-instances.md §7 E: E deletes `top_move` and
  the `_auto` MOVERS; `app_auto`/`Happ_auto` are deleted by L2 (the generic dischargers' only step
  source is the parked license, F3).  RECOMMEND YES — otherwise E2-Z cannot close green.
- Q-h (yes/no).  Accept the do-then-undo step PAIR for the failure arms (§3) as the honest form, i.e.
  no restructuring of create's exposure order?  RECOMMEND YES (the alternative rewrites the map
  discipline; §2(a)).
- Q-i (yes/no).  Accept that the AU write's short-chunk arm needs a CONTRACT change (#6: a state
  fire at the short run) — SpecFilewriteAU's chain gains an arm?  RECOMMEND YES; it is a hole, not a
  proof gap.
