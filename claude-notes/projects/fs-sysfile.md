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
   **DONE in S2.**
3. **The linked-inum range premise** is missing from SpecDirlink
   (the existing one is the DIRECTORY's inum); the writer-side dir_ok
   proof adds `bv_unsigned inum < 16*nib` for the linked child.
   **DONE in S2.**
4. **The stat hole**: SpecStati.stat_at omits bytes 12..15; filestat
   owns them separately to copyout all 24. **DISSOLVED in S3** — the
   buffer is filestat's own frame, so no contract clause is needed at
   all; see the S3 section.
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

## S1 — the decode layer LANDED (13 Code files, all 32 shards)

Full-generator-into-scratch recipe: the baseline run reproduced all 188
generated files BYTE-IDENTICALLY, and the run with the 13 new manifest
rows left the 155 sibling Code files + the facade byte-identical, added
13 files, and touched the 32 shards as PURE ADDITIONS (+394 lemmas,
+1970 lines, zero removed lines, zero lost lemmas). No AST head form new
to the layer appeared; the single new `SHIFTIWOP` (in filestat) picked
`decode_bridge_ms_bv` correctly, so the durable-notes sraiw trap did not
fire.

| file | symbol | addr | size | instrs | prefix | width |
|---|---|---|---|---|---|---|
| CodeFilewrite.v  | filewrite  | 0x80004258 | 308 | 118 | `fwri_`  | 3 |
| CodeFilestat.v   | filestat   | 0x80004132 |  98 |  40 | `fsti_`  | 2 |
| CodeCreate.v     | create     | 0x80004ab2 | 312 | 111 | `cri_`   | 3 |
| CodeSysRead.v    | sys_read   | 0x80004c36 |  72 |  25 | `sri_`   | 2 |
| CodeSysWrite.v   | sys_write  | 0x80004c7e |  72 |  25 | `swri_`  | 2 |
| CodeSysFstat.v   | sys_fstat  | 0x80004d0a |  58 |  21 | `sfsi_`  | 2 |
| CodeSysOpen.v    | sys_open   | 0x80004fc2 | 342 | 117 | `soi_`   | 3 |
| CodeSysLink.v    | sys_link   | 0x80004d44 | 254 |  87 | `slki_`  | 2 |
| CodeSysUnlink.v  | sys_unlink | 0x80004e42 | 384 | 126 | `suli_`  | 3 |
| CodeSysMkdir.v   | sys_mkdir  | 0x80005118 |  72 |  26 | `smdi_`  | 2 |
| CodeSysMknod.v   | sys_mknod  | 0x80005160 |  96 |  32 | `smni_`  | 2 |
| CodeSysChdir.v   | sys_chdir  | 0x800051c0 | 128 |  45 | `schdi_` | 2 |
| CodeSysExec.v    | sys_exec   | 0x80005240 | 268 | 101 | `sxi_`   | 3 |

Width follows the documented rule (`3` at or above 256 bytes) — note
sys_link at 254B is width 2. Every function's symbol range is FULLY
code (no alignment padding truncates a range), and **no function
contains an out-of-function `c.j`**: each is self-contained, one entry,
no tail-call arrangement to model.

### What the decode says, for S3–S7

- **`isdirempty` IS INLINED** — no symbol in the image. Its body is
  sys_unlink's `readi` at +0x112 with the two panics at +0x136/+0x142
  ("isdirempty: readi" / the dirlookup one) and the loop back. S7 gets
  no separate contract; it is a block inside sys_unlink's WP.
- **filewrite carries the ONLY indirect call in the batch**: `c.jalr a5`
  at +0x7e, the `devsw[f->major].write(...)` dispatch. It is also the
  only function in the batch with TWO returns (`c.jr ra` at +0x108 and
  +0x124). S3 needs the device arm's dispatch shape, the same one
  fileread's proof already carries (its consoleread axiom).
- **Only filewrite and sys_unlink reach `panic`** (filewrite +0x11e;
  sys_unlink +0xf4, +0x136, +0x142) — those two thread the standing
  `panic_wp_any` obligation, the other eleven do not. **create calls no
  panic at all**, so its dirlink failures are ordinary error arms.
- **create's `ret` sits at +0x74**, only a quarter into a 312-byte body:
  the early-return path is hot and every cold arm is laid out after it.
  Same shape in sys_open (ret at +0xd0 of 342B, with `itrunc` at +0x150
  *after* the return) and sys_unlink (ret at +0x16e of 384B). Expect to
  prove these back-to-front, not top-to-bottom.
- create's 19 direct calls are the boss list: nameiparent, ilock×3,
  dirlookup, iunlockput×6, ialloc, iupdate×3, dirlink×4 (one for the
  entry, three for `.`/`..`/the parent link on the mkdir path).
- sys_exec's tail is `kexec` at +0xca (plus argaddr/argstr/memset/
  fetchaddr/kalloc/fetchstr/kfree×2) — its Code file lands now, its
  proof waits on the exec campaign as planned.
- Loop counts (backward branches/jumps): filewrite 5, create 6,
  sys_open 8, sys_unlink 6.

Mirror evidence: all 45 files compiled, exit 0, no `Error` in any log
(32 shards ~7 s each, 16-wide, 15 s wall; 13 Code files 3.4–10.8 s,
11 s wall). Eight sibling Code files across the changed shards
(CodeNamex, CodeReadi, CodeVirtioDiskRw, CodeKfork, CodePrintk,
CodeIreclaim, CodeUsertrap, CodeBalloc) recompiled exit 0 against the
new shards. `lemma_diff.py --ref HEAD`: 45 files, CLEAN.

## S2 — the dist=0 retrofit LANDED (inheritance items 2+3, and item 4's bonus)

Full write-up in `design/fs-icache.md` §15.2. Headlines:

- **The D1 kernel-arm verdict is EXACTNESS CONFIRMED.** either_copyin's
  kernel post is a bare `⌜r = 0⌝` (SpecEitherCopyin.either_copyin_post),
  so writei's committed-partial-chunk break at +0xb0 is unreachable for
  `user = false`. No other mechanism touches bytes above `off+tot`: the
  bmap-returns-0 break stops before any copy, and both framed exits pass
  `dist := 0%nat` literally. §15.1(i)'s ruling stands as written.
- SpecWritei gains ONE clause, `⌜user = false -> dist = 0%nat⌝`.
  SpecDirlink drops `dist`/`dstb` from its postcondition binder and its
  range clause is now two-way. SpecDirlink gains the linked-inum premise
  (unused by dirlink itself — `clear`ed with a comment).
- **`DirView.dir_ok_dirlink` is proved**, Closed under the global
  context. §15.1(i)'s obstacle is gone; S5's create can re-park.
- Gate: EXIT=0, **1021 vo**, zero `Error`. lemma_diff CLEAN over the 5
  changed files. Print Assumptions on `Writei.wp_writei_sconf` and
  `Dirlink.wp_dirlink_sconf`: 5 platform axioms + funext, each.

TRAP FOR LATER STAGES (new): the mirror's Code `.vo` from before S1's
shard edits are STALE and `make` will not notice — a `one.sh` on any
proof over a touched Code file dies with *"makes inconsistent
assumptions over library xv6iris.KernelDecodeNN"*. Run `full.sh` once
after a git-sync before iterating.

## S3 — filestat's spec + the stat-buffer bridge LANDED; filewrite BLOCKED

### What landed (green on the mirror, lemma_diff clean but the seal)

- **`iris/SpecFilestat.v`** — FROZEN and compiling. Two arms, no device arm,
  no panic. `filestat_stack = 10 + 50` (copyout dominates ilock's 44).
- **`iris/ProofFilestatParts.v`** — the stat-buffer bridge, all lemmas PROVEN:
  the five `st_*` field addresses as `pa_add`; the two-byte alignment pair
  (`fst_aligned8_aligned2`, `..._hi` — InstrBytes' `z_rem8_*` helpers are
  `Local`, so the arithmetic is redone); the narrow analogues of
  `bytes_own_slot` (`fst_bytes_w4`, `fst_bytes_w2`); and the two conversions
  `fst_bytes_stat` (3 frame slots -> `stat_at` + the hole) and
  `fst_stat_bytes` (back again).
- `ProofFilestat.v` / `LinkFilestat.v` NOT written — parked green.
  **(Both landed in S3b; see that section.)**

### INHERITANCE ITEM 4 IS DISSOLVED, not solved

The stat hole needs **no contract clause at all**. `struct stat` is filestat's
OWN 24-byte stack local at `s0-72` = frame slots 9/8/7
(`StackBytes.slots3_bytes_own` at `k = 9` fits it exactly). So bytes 12..15 are
frame bytes, existential in `stack_own`, never written by stati, and copyout's
contract says nothing about what the user pages end up holding. There is no
resource anywhere in the cone that could record them. SpecFilestat says
nothing about the buffer at all; a caller owes the SLOTS and nothing else.

### Decode corrections to S1 (read off the tracked `xv6-riscv/kernel/kernel.asm`,
which matches the Code files byte-for-byte at a base 14 bytes lower)

1. **The `panic("filewrite")` at +0x11e is the ELSE arm** — the type is none of
   FD_PIPE/FD_DEVICE/FD_INODE — exactly like fileread's. It is **not** a
   short-write panic. A short write (`r != n1`) `break`s the loop at +0xc0 and
   the tail `ret = (i == n ? n : -1)` at +0xf4 answers -1. S1's guess was
   wrong; the `panic_wp_any` threading is unaffected.
2. **`devsw[major].write` is at offset 8**, not 0 (`.read` is first). So
   filewrite's cell is `devsw + 16*mj + 8`, NOT fileread's `a_devsw_read`.
3. **filewrite returns `n`, never a partial count, on the inode arm** —
   `ret = (i == n ? n : -1)`. Still inside `pipe_rw_ret n r`.
4. filewrite's `!writable` early return at +0x00/+0x04 is **before the
   prologue**; its `ret` at +0x124 runs with sp untouched.
5. filestat's dispatch is a single **unsigned range test** `type - 2 <=u 1`
   (`bltu a4,a5` — AST order is `(imm, rs2, rs1, op)`, confirmed against the
   Sail `execute_BTYPE`). Reading it the other way inverts the dispatch.
6. filestat's `sraiw a0,a0,31` at +0x4a is the `< 0 ? -1 : 0` idiom over
   copyout's own two-valued result; step it with `ProofBallocParts`'
   `wp_sraiw_s_sconf`.
7. `max = ((MAXOPBLOCKS-1-1-2)/2)*BSIZE = 3072`, materialised twice
   (`lui`/`addi` into s7 and s9) at +0x42..+0x4e.

### THE BLOCKER: filewrite cannot rebuild `ic_loaded` (STOP-AND-REPORT)

`SpecIunlock` takes `IcacheEscrow.ic_loaded`, which carries
`⌜DirView.dir_ok icfg_nib dn data⌝`. `dir_ok` is conditional on
`di_type dn = T_DIR`, and it constrains the file's **data bytes**
(`dir_inums_ok`: every live record's inum is in range). writei cannot change
`di_type`, so a directory going in is a directory coming out — and an
**arbitrary user write into a directory's byte range breaks `dir_inums_ok`**.
Therefore filewrite's FD_INODE arm is **unprovable without a not-a-directory
premise**, and there is no resource in the file-table or icache layer that
says so. `dn` is ilock's OUTPUT, so the fact cannot be stated as a premise
about a caller-held record.

This is the exact shape of inheritance item 2 (dirlink's short-write holes)
that S2 had to retrofit, and it needs the same kind of ruling. Options:

1. **(RECOMMENDED)** Add `⌜bv_unsigned (di_type dn) <> T_DIR_z⌝` to the
   FD_INODE arm of `FileInv.file_payload` / `inode_pay`. This IS the real xv6
   invariant: sys_open refuses `O_RDWR` on a directory, so a writable
   FD_INODE file is never one. Costs: sys_open (S6) establishes it;
   fileread/fileclose/filedup carry `inode_pay` inside `file_ref` without
   inspecting it, so the change is additive to them. Touches `FileInvDefs.v`,
   which is frozen — hence the coordinator's call, not an agent's.
2. Pin the loaded type per icache slot in `ic_escrow` so a caller can hold a
   persistent agreement fact. Bigger change, and the escrow does not do this
   today.
3. Weaken `ic_loaded`'s `dir_ok` conjunct — NOT viable, it is load-bearing for
   dirlookup/namei.

Until this is ruled on, **SpecFilewrite.v is deliberately NOT frozen**:
encoding the fact provisionally in filewrite's own environment would create
exactly the retrofit S2 just finished paying for. Everything else about
filewrite's contract is settled and recorded above.

Mirror evidence: `SpecFilestat.v` and `ProofFilestatParts.v` each `DONE = 0`,
zero `Error`. `lemma_diff.py --ref HEAD`: 2 files, one NEWAXIOM, the
`Module Type FILESTAT` seal.

## S3b — filestat PROVEN AND LINKED; §17 STOPPED-AND-REPORTED

### What landed

- **`iris/ProofFilestat.v` + `iris/LinkFilestat.v`** — filestat is proven and
  linked, `Print Assumptions Filestat.wp_filestat_sconf` = **5 platform axioms
  + funext**, nothing else.  All five callees are real proofs (myproc, ilock,
  stati, iunlock, copyout), so unlike LinkFileread this cone assumes nothing:
  filestat has no device arm and reaches no allocator.  **file.c is 6/7**
  (filewrite is the last).
- **`iris/ProofFilestatParts.v` grew an S3b half**: the ten-slot frame
  (`fst_push_80`/`fst_pop_80`/`fst_fp_80`, `fst_frm1..6`, `fst_stbuf` for
  `&st = s0-72 = pa_stk sp0 9`), the dispatch arithmetic, the two `sraiw`
  values, `fst_bytes_name24`, and the shared epilogue `fst_epi` at +0x52.
- Decode corrections 1–7 in the S3a section all held up under the proof; none
  needed revision.

### Three things worth keeping from the proof

1. **The dispatch is `1 <u (int)(type - 2)`, and the honest way to prove the
   "neither" arm is to decompose it.**  `fst_bltu_in` is two `vm_compute`s
   (types 2 and 3 are literals); `fst_bltu_out` goes
   `fst_addiw_m2` (the `c.addiw` leaves `t + (2^32 - 2)` at width 32, via
   `trunc32_add`/`trunc32_sext`) → `fst_sub2_eq` (a difference of 0 or 1 pins
   the type at 2 or 3) → `fst_gt1_of_ne` (`1 <u X` for any 64-bit `X ∉ {0,1}`,
   which needs no signedness reasoning at all).  Do NOT try to characterise
   `uint (sign_extend' 64 w)` by cases on the sign bit; the ∉{0,1} route is
   three lines and needs no `bv_swrap`.
2. **`Z.mod_small` TAKES BOTH `a` AND `b` EXPLICITLY.**  `Z.mod_small (u + c)
   ltac:(lia)` passes the tactic as the MODULUS, and the failure surfaces as
   `Tactic failure: Cannot find witness` from a `lia` running on an open goal —
   i.e. it reads exactly like the `bitvector.tactics` zify-hook trap and is
   not one.  Spell `Z.mod_small a b ltac:(lia)`.  (The real hook trap is also
   here: the modular reasoning is factored into `fst_mod32_sub2` over plain
   `Z` variables, because `lia` does answer "Cannot find witness" on a goal
   mentioning `bv_unsigned`.)
3. **`n%: tac` GOAL SELECTORS RENUMBER.**  `split_and!` on `callee_saved`'s
   thirteen conjuncts followed by `4-5: …` then `7-13: …` fails with
   *"No such goal"*: the first selector SOLVES its goals and the rest shift
   down.  Run the selectors HIGHEST-FIRST (`7-13:` then `4-5:`), which is what
   `fr_epi` does and why it reads oddly.
4. **An explicit `rget_ne X R ltac:(…)` does not survive a callee's
   `wp_next` boundary** (durable-notes) — every such site after ilock /
   stati / iunlock / copyout had to become the ambient `rgne`, and the error
   is a *"does not match any subterm"* on a term you can see in the goal.

### THE §17 RULING DOES NOT CLOSE — see design/fs-icache.md §17.1

Summarised there in full.  The three-line version: `ic_id` is unreadable from
a file payload (which holds only `inode_shr_held`), so no generation counter
on it can reach filewrite; a PERSISTENT witness cannot assert that its
generation is the current one, because persistence is exactly
non-revocability; and the generation therefore has to ride §14.6's liveness
pool — which is capacity for `live_frac` (an existential keeps its arity and
every statement over it) but NOT for `ic_loaded`, which travels out of the
escrow and so must carry a self-contained, TIMELESS "this is the current
generation's type".  The only timeless shape that works gives `ic_loaded` a
pool slice of its own and re-scales §14.6's mass conservation.  That is a
coordinator ruling (§17′) and a stage of its own; `SpecFilewrite.v` stays
unwritten, exactly as S3a left it.

### Mirror evidence

`ProofFilestatParts.v`, `ProofFilestat.v`, `LinkFilestat.v` each `DONE = 0`,
zero `Error`.  **TRAP OBSERVED: the mirror was `git pull`ed mid-stage** (it
moved a73e9e5a → 95956162, two unrelated commits on `WpNext.v` and
`ProofIreclaim.v`), which silently REVERTED the tracked `ProofFilestatParts.v`
under a `.vo` built from the agent's version — the exact stale-`.vo` false
green the notes warn about, arriving from a direction nobody was watching.
Re-check the md5 of every tracked file you have scp'd before believing a gate,
not just after the scp.

## S3c — §17' RETROFIT: piece 1 LANDED and full-gated; pieces 2+3
## STOPPED-AND-REPORTED (design/fs-icache.md §17.3)

**Landed (piece 1, whole, exactly as §17.2 ruled).**  `IcacheRef.v` only:

- `iliveUR := gmapUR nat (prodR fracR (agreeR (leibnizO gname)))`;
  `live_gen k s g` is the new primitive, `live_frac k s := ∃ g, live_gen k s g`
  the arity-preserving wrapper.  `live_gen_agree` (two slices of one slot name
  one generation) is the mechanism the whole of §17' runs on; `live_gen_split`
  / `live_gen_join` / `live_gen_halve` / `live_gen_bound` are its family, and
  `live_frac_split` survives as a `⊣⊢` COROLLARY (the ⇐ direction now goes
  through `live_gen_agree`, which is the only proof in the file that got
  longer).
- The one-shot's vocabulary beside it, modelled on `KptGhost.v`'s and named
  to match: `ityR := csumR (exclR unitO) (agreeR (leibnizO (bv 16)))`
  (`DinodeEnc.di_type`'s width), `ity_pending` / `ity_shot` / `ity_shoot` /
  `ity_shot_agree` / `ity_pending_excl` / `ity_pending_shot_excl`, with
  `ity_shot` PERSISTENT and both TIMELESS.  `icacheG` gains `icache_ityG`
  and `icacheΣ` a `GFunctor ityR`.
- `live_boot_map` takes the boot generation as a parameter; ONE gname serves
  all fifty slots (the agreement is per-KEY, every slot is FREE at boot, and
  no free slot carries a one-shot obligation).  `icfg_alloc` mints it and
  now returns it; `live_boot_split` is unchanged in force.

**THE RIPPLE WAS ZERO FILES.**  `IcacheRef.v` is the only file that moved:
the arity-preserving claim in §17.2 piece 1 held exactly, and no `iref_tok`,
`inode_ref`, `inode_shr`, `inode_ref_short`, `inode_held*` or Spec over them
changed a character.

**Not landed, and why (full argument in design §17.3, both verified against
the code rather than reasoned about):**

- **(A)** §17.2 piece 3's placement of the ½ slice INSIDE `ic_loaded` makes
  `IcacheEscrow.ic_open_auth_ref`'s REF-1 refutation of the OUT/`DepShr` arm
  unprovable: the live mass in hand drops from `q + (1-q) + s` to
  `q + (1/2-q) + s = 1/2 + s`, and §14.8's inventory of alternative
  discriminators is already recorded exhausted.  Repair: the ½ lives in the
  ARM (all four live arms), `ic_loaded` stays untouched, the generation and
  the type witness go on `ic_payload` instead — which is named in 3 files
  where `ic_loaded` is named in 19.
- **(B)** §17.2 piece 2's parking of the pending one-shot on the `v = false`
  polarity is refuted by `ProofIput.v:1965-1990`: iput's free path retypes in
  place and re-parks UNLOADED inside the SAME generation, after ilock's fill
  has already spent that generation's one-shot — a shot→pending transition.
  Repair: park the pending with `ipool_shape`'s ALLOCATED disjunct inside
  `ic_unloaded`, which is §17's own sentence and is exactly what the code
  does (`ProofIput.v:1989` is `rewrite /ipool_shape. iRight.`, the marker).

**Gate.**  Mirror `full.sh` `EXIT=0`, **1025 `.vo`** (unchanged).
`tools/lemma_diff.py --ref HEAD`: CLEAN — nothing dropped, nothing admitted,
no new assumption.  `Print Assumptions` on all eight cones (Ilock, Iget,
Iput, Iunlock, Fileread, Namex, Fileclose, Kexit): each exactly the 5
platform axioms + `functional_extensionality_dep`, with Fileread's known
`Consoleread.wp_consoleread_sconf` — every set unchanged.
`iris/IcacheRef.v` md5 `d62349202b867501f9b3ae709c5b192f`, verified equal on
both sides after the scp and re-verified after the gate.

## The stage ladder

- **S1** (agent): the DECODE stage — 13 Code files (the 12 targets +
  CodeSysExec for the future) via tools/gen_code.py, FULL-generator-
  into-scratch recipe (durable-notes; never --only), manifest rows,
  all 32 shards, scratch-verified, near-full rebuild lands with it.
- **S2** (agent) **— LANDED**: the dist=0 retrofit — SpecWritei kernel
  arm + ProofWritei + SpecDirlink third-arm re-derivation + the
  linked-inum premise (items 2+3) + `DirView.dir_ok_dirlink`.
- **S3** (agent) **— PARTIAL**: SpecFilestat + ProofFilestatParts landed;
  filewrite BLOCKED on the dir_ok ruling (see the S3 section). Its Spec is
  deliberately unfrozen; ProofFilestat is parked. file.c stays 5/7.
- **S3c** (agent) **— PARTIAL**: §17' piece 1 (the liveness generation +
  the one-shot algebra) LANDED and full-gated with a ZERO-file ripple;
  pieces 2+3 STOPPED-AND-REPORTED (design/fs-icache.md §17.3 has both
  findings and both repairs, each checked against the code).  filewrite
  is still blocked and still unspecified.
- **S3b** (agent) **— PARTIAL**: filestat PROVEN AND LINKED (file.c 6/7);
  §17's fd-type witness STOPPED-AND-REPORTED as unimplementable in the ruled
  shape — design/fs-icache.md §17.1 has the finding and the repair (§17′) to
  rule on. filewrite is still blocked and still unspecified.
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
