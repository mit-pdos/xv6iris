# fs-sysfile — the syscall layer campaign (file.c's last 2 + sysfile.c's 11)

OPENED 2026-08-11, immediately after the fs-namei campaign closed fs.c
at 24/24 (final gate green, 1001 vo, coverage 163/188 = 87%).
User-standing instruction: run this campaign, then shut the EC2 box
down. Targets: filewrite (308B) + filestat (98B) in file.c, then
sysfile.c's create (312B), sys_read (72B), sys_write (72B), sys_fstat
(58B), sys_open (342B), sys_link (254B), sys_unlink (384B), sys_mkdir
(72B), sys_mknod (96B), sys_chdir (128B). sys_exec (268B) is DEFERRED
to the exec campaign (its tail is kexec, 860B untouched). After this
campaign file.c is 7/7 and sysfile.c is 15/16 (sys_exec pending).

## THE INHERITANCE (the fs-namei close-out's 8 items, restated as work)

1. **ialloc's payout is raw**: `inode_ref kslot q dev inum` +
   `inum < 16*nib`; create builds `inode_held` itself (it owns the
   device ties); `dn' = ialloc_fresh ty` is documentation — ilock's
   THIRD FILL ARM (§16.5) is what actually hands create the fresh
   record.
2. **dirlink's short-write holes** (§15.1(i)): on the kernel arm
   either_copyin cannot fail, so the honest fix is `dist = 0` —
   strengthen SpecWritei's kernel arm, then re-derive SpecDirlink's
   third arm's range clause. Without it create cannot re-park its
   directory (`dir_ok` underivable on the middle-slot arm).
3. **The linked-inum range premise** is missing from SpecDirlink
   (the existing one is the DIRECTORY's inum); the writer-side dir_ok
   proof adds `bv_unsigned inum < 16*nib` for the linked child.
4. **The stat hole**: SpecStati.stat_at omits bytes 12..15; filestat
   owns them separately to copyout all 24.
5. **The fd-type fact**: FileInv's payload is `inode_ref` only on
   FD_INODE/FD_DEVICE; `f->off` is NOT zero for FD_PIPE/FD_DEVICE
   (sys_open only assigns it on the inode path). filewrite's contract
   needs the type discipline sys_open maintains.
6. **The 35-slot boot accounting** and **SpecFsinit's image premises**
   (incl. `hdr_n bs_hdr = 0`) are the BOOT CLIENT's, not this
   campaign's — listed so nobody re-threads them here.
7. **Two standing threaded obligations**: panic_wp_any (resource) and
   printk_gen_contract (Prop, two deep via ireclaim) — sysfile
   functions that reach them thread them the same way.
8. **fileclose leaks one iref_slot per closed inode file** (recorded
   pre-campaign) — sys_close's cone may want the per-ofile descriptor
   ghost SpecFileclose's header owes; scope at S0-stage per function,
   do NOT fix ambiently.

## The stage ladder

- **S1** (agent): the DECODE stage — 13 Code files (the 12 targets +
  CodeSysExec for the future) via tools/gen_code.py, FULL-generator-
  into-scratch recipe (durable-notes; never --only), manifest rows,
  all 32 shards, scratch-verified, near-full rebuild lands with it.
- **S2** (agent): the dist=0 retrofit — SpecWritei kernel arm +
  ProofWritei + SpecDirlink third-arm re-derivation + the linked-inum
  premise (items 2+3). Touches proven files; ends in a full gate.
- **S3** (agent): filestat (stat_at + the hole + copyout) and
  filewrite (the loop over writei inside its own transaction;
  fd-type premise per item 5). file.c 7/7.
- **S4** (agent): sys_read/sys_write/sys_fstat — argfd + the file.c
  contracts; thin shells.
- **S5** (agent): create — the writing half's boss: namei/nameiparent
  + ialloc + ilock's third arm + dirlink (+ the "." and ".." links on
  the mkdir path) + the found-arm early exit. Its contract's
  found/created arms mirror dirlink's.
- **S6** (agent): sys_open (create arm + open-existing arm + the
  device checks + fdalloc/filealloc) + sys_mkdir + sys_mknod +
  sys_chdir (idup/iput of cwd — inode_held swap via proc_priv).
- **S7** (agent): sys_link + sys_unlink (nlink writei choreography,
  the record zeroing, isdirempty for unlink's dir arm — check decode:
  isdirempty may be a separate static fn or inlined).
- Final gate → coverage ~178/188 → EC2 SHUTDOWN (user-standing).

Per-stage discipline unchanged from fs-namei: coordinator designs and
merges, Opus agents prove in isolated worktrees against the EC2
mirror, specs frozen before proofs, park-green protocol, stop-and-
report on design surprises, lemma_diff + Print Assumptions gates,
NEVER scp _CoqProject, no coordinator gates while an agent is live.
The ~50 recorded traps live in projects/fs-namei.md's stage ledgers.
