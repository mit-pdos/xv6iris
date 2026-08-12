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

## S3d — §17' PIECE (A) LANDED AND FULL-GATED; PIECE (B)
## STOPPED-AND-REPORTED (design/fs-icache.md §17.5)

**Landed (§17.3 (A), whole).**  The restated mass ledger and the
arm-resident liveness slice, across ten files:

- `IcacheInv.live_slot`'s live case is `1/2 - qt` — literally
  `islot_rest_at`'s shape, so the liveness ledger and the identity
  ledger are now ONE shape.  `live_slot_alloc` is a fupd at `q < 1/2`
  that mints the slot's fresh generation and its pending one-shot;
  `live_slot_incr` (hence `iref_incr_store_au`, `iref_upgrade_store_au`)
  tightens to `qt + qn < 1/2`; `live_slot_close_last`,
  `iref_close_last_step`, `iref_close_last_store_au` and
  `live_whole_share_absurd` each gain a `live_frac k (1/2)` premise.
  New: `live_gen_bump` / `live_frac_bump` (IcacheRef),
  `live_slot_live_gen` / `live_pool_live_gen` / `iref_live_gen_load_au`
  (the generation-named guard read SpecIlock v4 needs).
- `IcacheRef.ic_dep` gains a `gname` field and `ic_dep_gname` is the pure
  side condition the two swap lemmas carry;
  `inode_shr_gen` / `inode_ref_gen` / `inode_shr_held_gen` are the
  generation-named forms, each an `⊣⊢` with the ∃-form so a caller moves
  between them with one `iExists`.
- `IcacheEscrow`: `ic_parked` binds `∃ g` over its payload AND a
  `live_gen k (1/2) g`; `ic_dep_res` splits into `ic_dep_own` (the
  depositor's part, generation-NAMED so `live_gen_agree` can pin the
  arm's half to it) and `ic_dep_half`, so **`ic_out`'s text does not
  move**; `ic_payload` gains the generation parameter and `ic_loaded`
  does not move at all — the "~23 `ic_loaded` sites" line stayed retired.
  `ic_swap_checkout` / `ic_swap_park` take `ic_dep_gname d = Some g` and
  trade in `ic_dep_own`.  `ic_open_auth_ref`'s REF-1 refutation of
  OUT/`DepShr` is back to `qt + (1/2 - qt) + 1/2 + s > 1`.
- `SpecIlock` v4 takes the share generation-named
  (`inode_shr_gen k s dev inum g`) and returns
  `ic_deposit cn k (DepShr s dev inum g)`; `SpecIunlock` /
  `SpecIunlockput` thread the same `g`.  Five consumers (fileread,
  filestat, namex, ireclaim, iunlockput) needed ONE line each —
  `iEval (rewrite inode_shr_gen_intro) in "Hshr"; iDestruct … as (gsh)` —
  plus the argument.

**The one place the build is smaller than the ruling, and it is forced
by the instruction stream.**  §17.3 says parked/mid/held all gain the
½.  MID and HELD do NOT: MID is sealed at iget's +0x72, four
instructions BEFORE the slot enters `M` at +0x78, so no unit has been
split yet and there is no ½ to put in it; HELD is iput's own window and
`ic_open_auth_ref` hands the parked ½ out with the payload.  Both
threads carry the ½ in hand across their window; the ledger balances at
every instant, and no opener's refutation of either arm uses liveness
(both die to a FULL `i_inum` cell).  Full analysis in §17.5.

**Not landed, and why: §17.3 (B) is refuted by §16.4's CLAIM BOX.**
(B) parks the pending one-shot with `ipool_shape`'s ALLOCATED disjunct
because "ilock's fill MUST take the allocated branch".  `ProofIlock`'s
`il_load` splits the pool shape THREE ways, and the third — a MARKER
over a NONZERO type, ialloc's claim, withdrawn through
`InodeRegion.ireg_withdraw` — COMPLETES the fill with no pending token
in sight.  Parking the pending on both disjuncts is what (B) refuted
from the other side (`ProofIput.v:1981` re-parks the marker inside a
generation whose shot is already out).  The two constraints are jointly
unsatisfiable for a per-generation one-shot, and the dead escapes are
enumerated in §17.5 along with three candidate repairs — (a) TYPE THE
MARKER in `InodeRegion` is the only one faithful to what is true.

So `ic_payload`'s witness conjunct, `SpecIlock`'s additive post,
`FileInv.inode_pay`'s witness and `SpecFilewrite` are all NOT in.  The
generation parameter on `ic_payload` is their landing site: the witness
is a one-line addition there plus one line in `SpecIlock`'s post.

**Gate.**  Mirror `full.sh` `EXIT=0`, **1032 `.vo`** (unchanged), zero
`Error`.  `Print Assumptions` on all eight cones (Ilock, Iget, Iput,
Iunlock, Fileread, Namex, Fileclose, Kexit): each exactly the 5 platform
axioms + `functional_extensionality_dep`, with Fileread's known
`Consoleread.wp_consoleread_sconf` — every set unchanged.
`tools/lemma_diff.py --ref HEAD`: one GONE, `ProofIget.ig_quarter_le`,
replaced by `ig_quarter_lt` because §17.3 (A2) tightens the first
reference's budget from `≤ 1/2` to `< 1/2`.  Nothing admitted, no new
assumption.

**sys_open's obligations for S6, as they stand.**  Unchanged from
§17.2's list (S3b (a)–(c)) and still owed, but they cannot be FROZEN
until (B) is re-ruled, because their resource form is exactly the
witness's: on the `O_CREATE` path the type is `T_FILE` by construction
(`ialloc_fresh`); on the open-existing path a `T_DIR` inode forces
`O_RDONLY`, i.e. `fc_wbool C = false`; and the fd's payload must record
the generation its share belongs to so filewrite's `ity_shot_agree`
fires.  Under repair (a) the first two are unchanged and the third
becomes "record the marker's type alongside".

## S3e — §17.5 RULED (DESIGN-ONLY): candidates (a) and (c) BOTH DIE; the
## mechanism is a SECOND GENERATION BUMP at iput's +0x54
## (design/fs-icache.md §17.6)

No `iris/` change; the deliverable is §17.6, worked to a mechanism against
the instruction streams rather than argued.

**The killer sequence is REACHABLE, in proven code.**  `ProofIget.v:1226`
(recycle at `g`) → `ProofIlock.v:974` (fill₁, `ty₁`) → fd published at `g`
→ `ProofIput.v:1366/1538/2013` (free path, re-park UNLOADED, **still `g`**)
→ `ProofIalloc.v:1454` (claim, buffer-serialised) + `:1625` (`iget` HITS
the still-cached entry, `ref` 1→2, so the slot never goes free) →
`ProofIlock.v:974`'s THIRD branch (`ireg_withdraw`) fills a second time at
`ty₂`, inside generation `g`.

**The fd-liveness verdict, honestly.**  A live fd's share IS refuted at the
free path — `IcacheInv.live_whole_share_absurd` (`:1345`), off
`ic_open_auth_ref`'s `M !! k = Some (q,1)` premise and `positiveR`'s
no-zero.  But that does NOT rescue a per-generation one-shot: `ity_shot` is
PERSISTENT, so a stale copy outlives every share and the second fill is
STUCK at the mint (not unsound — unprovable).  **The exclusion's real value
is the other direction**: the three summands `live_whole_share_absurd` adds
to a contradiction are, at the same instant, an ASSEMBLY of the slot's
whole liveness unit (closer's `qt` + arm's `1/2`, in iput's hand since
`ProofIput.v:1376` + table's `1/2 − qt`), and the whole unit is exactly
`live_gen_bump`'s premise.  So the exclusion is the PERMISSION SLIP for
revocation, and the itable lock (held from iput's `acquire` through +0x5c)
serialises it perfectly: every reference minted after the free path commits
— including ialloc's — is minted at the NEW generation.

**The mechanism (no new algebra).**  (i) the pending rides `ic_payload`'s
FALSE polarity and the shot its TRUE polarity — NOT `ic_unloaded` (which
`ic_mid_arm` holds directly, sealed at `ProofIget.v:1167` before any unit
is split) and NOT a pool disjunct (which is what §17.5 refuted); (ii) a new
`IcacheInv.live_slot_regen`, **PROVED on the mirror as a scratch probe,
first try, `DONE = 0`**; (iii) iput calls it at `ProofIput.v:1688`, where
`itable_half`, REF-1, `iref_tok` and the arm's `1/2` are all named already;
(iv) `ic_open_held` takes two gnames (free — `ic_payload_excl` is already
generic in both).  `ipool_shape`, `imark`, `InodeRegion` and `ProofIalloc`
are **untouched**, so §16's "ialloc reaches no cache resource" holds by
construction.  Boot: ZERO change (`ic_empty_arm` carries no payload).

**Blast radius:** IcacheInv +1 lemma; IcacheEscrow 3 small edits;
ProofIget ONE LINE; ProofIlock one `iMod` + one premise; ProofIput one
`iMod` + a `ga → ga'` rename over `:1688–2013`; SpecIlock +1 line additive,
SpecIunlock/SpecIunlockput +1 premise and five consumers one line each;
FileInvDefs/FileInv for `inode_pay`.  Untouched: IcacheBoot, InodeRegion,
ProofIalloc, IcacheRef, ProofIunlock, every `ic_loaded` consumer.
Constraint 8 closes for free — `SpecWritei.v:263`'s `wi_dinode` preserves
`di_type` definitionally.

**Recommended split:** S3f = the icache half (escrow/iget/ilock/iput +
SpecIlock's additive line), full-gated; S3g = `inode_pay` + SpecFilewrite +
Proof + Link.

**Mirror hygiene.**  Probe `S3eProbe.v` compiled at `b538f806`, then
deleted; mirror `git status` clean, 1032 `.vo` unchanged.  No tracked file
was touched on either side.

**sys_open's S6 obligations, restated under this ruling** (superseding the
"under repair (a)" line above): on `O_CREATE` the type is `T_FILE` by
construction (`ialloc_fresh`); on the open-existing path a `T_DIR` inode
forces `O_RDONLY`, i.e. `fc_wbool C = false`; and the fd's payload records
the SHARE'S GENERATION `g` plus `ity_shot g ty` — the marker's type never
enters, because the marker is never typed.

## S3f — §17.6 BUILT AND FULL-GATED; `inode_pay` LANDED; `SpecFilewrite`
## FROZEN (design/fs-icache.md §17.8)

**Part 1, the icache half — LANDED WHOLE, exactly as §17.6/§17.7 ruled.**

- `IcacheInv.live_slot_regen` — the second generation bump, at iput's REF-1
  free window.  Compiled first try from §17.6.3 (2)'s statement.
- `IcacheEscrow`: `ic_payload` carries `ity_shot g (di_type dn)` on TRUE and
  `ity_pending g` on FALSE; `ic_close_mid_to_parked` gains the pending as a
  premise (iget's recycler was DROPPING it); `ic_open_held` generalises to
  TWO gnames — **the §17.6.6 unprobed step resolved in favour of the
  generalisation, with no proof change; the pre-approved duplicated-lemma
  fallback is struck.**
- `ProofIget`: one line (`Hpend` into `ic_close_mid_to_parked`).
- `ProofIlock`: one `iMod (ity_shoot …)` — placed just after `clearbody dn`
  and BEFORE §16.4's three-way pool split rather than on each completing
  branch, which is one `iMod` instead of two and lets the type-0 panic
  branch carry a spent token into its divergence; plus `il_load`'s
  `ity_pending g` premise and four threading lines.
- `ProofIput`: one `iMod (live_slot_regen …)` at the +0x54 checkout and the
  `ga -> ga'` rename over `:1688–2013` (mechanical, five sites).
- `SpecIlock` +1 additive post line (`ity_shot g (di_type dn)`);
  `SpecIunlock` / `SpecIunlockput` +1 premise; five consumers one line each.

**Part 2a, `inode_pay` — LANDED.**  `fpnames` gains `fp_ig`; `inode_pay`
takes the generation and the writable bool and carries
`∃ ty, ity_shot g ty ∗ ⌜wr = true -> ty <> T_DIR⌝` beside a
generation-named share.  `inode_pay_alloc` had to change shape (the
publisher cannot name the generation before shedding — see §17.8), and
`FileInvDefs.inode_held_shed_gen` is the new shed.  **Ripple: two files**
(`ProofFileclose`, `ProofPipealloc`).  fileread / filestat / filedup /
kexit carry the payload opaquely and did not move — §17's audit, done by
the build.

**Part 2b, `SpecFilewrite.v` — FROZEN and compiling.**  Four arms, the
chunking loop, and S3a's four decode corrections built in (`!writable`
before the prologue; `devsw[mj].write` at OFFSET 8, `a_devsw_write`;
+0x11e is the ELSE-arm panic; `max = 3072`).  Two things worth keeping:

1. **filewrite does NOT inherit fileread's `MAXFILE*BSIZE + n < 2^31`
   premise.**  The chunking makes writei's joint bound a CLOSED fact
   (`fw_chunk_joint`: `n1 <= 3072` by construction, `off <= MAXFILE*BSIZE`
   by `off_wf`), so sys_write may take `n` straight from user input where
   sys_read cannot.  This is the one place the write side is better off.
2. The fs environment is fileread's plus the LOG and the ALLOCATOR
   (`log_ctx`, `fs_crash_seam`, `gen_cert`, `bitmap_res`, `sb.size`,
   `sb.bmapstart`, `printk_env` + `printk_gen_contract`), and the share is
   GENERATION-NAMED with the type witness beside it — `inode_shr_gen … g`
   plus `ity_shot g ty` and `⌜fc_wbool Cf = true -> ty <> T_DIR⌝`, i.e.
   exactly what an `inode_pay` holder already has, so sys_write owes
   nothing new.  `bitmap_res` comes back at an existential `used'` with
   `used ⊆ used'`.

**NOT WRITTEN, parked green: `ProofFilewrite.v`, `LinkFilewrite.v`,
`SpecConsolewrite.v`, `LinkConsolewrite.v`.**  filewrite is 308 bytes /
~100 instructions with a loop and six saved callee registers -- fileread's
2461-line proof plus a loop -- and the budget rule (spec frozen beats proof
parked) applies.  S3g picks it up with the contract fixed.

**Gate.**  Mirror `full.sh` `EXIT=0`, **1033 `.vo`** (1032 + the new
`SpecFilewrite.vo`), zero `Error`.  `Print Assumptions` on all eight cones
(Ilock, Iget, Iput, Iunlock, Fileread, Namex, Fileclose, Kexit): each
exactly the 5 platform axioms + `functional_extensionality_dep`, with
Fileread's known `Consoleread.wp_consoleread_sconf` — every set unchanged.
`tools/lemma_diff.py --ref HEAD`: 18 files, ONE NEWAXIOM, the
`Module Type FILEWRITE` seal (one seal per new Spec).  Nothing GONE,
nothing ADMITTED.

**`_CoqProject` note.**  `SpecFilewrite.v` was added to `iris/_CoqProject`
(after `LinkFilestat.v`); the mirror's copy was patched IN PLACE with `sed`
and its `CoqMakefile` regenerated — the file itself was never scp'd, per
the standing rule.

**sys_open's FINAL discharge obligations for S6, now that the resource
shapes are frozen.**  A publisher of an FD_INODE fd must, in this order:

  (a) hold `IcacheRef.inode_held v` for the inode (namei / create gives
      it), and run `FileInvDefs.inode_held_shed_gen` to obtain `Q`, the
      generation `g`, `inode_held_short v Q` and `inode_shr_held_gen v Q g`;
  (b) produce `IcacheRef.ity_shot g ty` for that same `g` — and the ONLY
      source is `SpecIlock`'s postcondition, so sys_open must ilock the
      inode (which it does anyway, to read the type) while holding a share
      generation-named at `g`.  `ty` is then `di_type dn`;
  (c) discharge `⌜fc_wbool C = true -> bv_unsigned ty <> T_DIR_z⌝`:
      * on the `O_CREATE` path the type is `T_FILE` by construction
        (`ialloc_fresh`), so the implication is vacuous on its conclusion;
      * on the open-existing path a `T_DIR` inode forces `O_RDONLY`, i.e.
        `fc_wbool C = false`, so it is vacuous on its hypothesis.  This is
        the branch that must be read off `sys_open`'s own
        `(ip->type == T_DIR && omode != O_RDONLY)` test;
  (d) `FileInvDefs.inode_pay_alloc` with those three, then install
      `MkFPNames … Q g` via `fpay_tok_update` at the `sd` that writes
      `f->ip`.

  The marker's type never enters — the marker is never typed (§17.6.5 (a)).
  These SUPERSEDE the S3b (a)–(c) list and the "under repair (a)" and §17.6
  restatements above; they are now stated over resources that exist.

## S3g — the device contract + filewrite's whole SCAFFOLD landed and
## full-gated; `ProofFilewrite` PARKED GREEN with the decode settled

**Landed, all three green on the mirror.**

- **`iris/SpecConsolewrite.v` + `iris/LinkConsolewrite.v`** — the assumed
  device contract, `SpecConsoleread`'s shape conjunct for conjunct with the
  copy direction reversed.  The shape is FORCED, not chosen:
  `SpecFilewrite.filewrite_dev_env` is ONE devsw cell, so the only resources
  the `c.jalr a5` at +0x7e can hand the callee are filewrite's own
  (`sie_cap_gpr`, `cpu_own`, text, `proc_priv`, `kalloc_env`, `procs_inv`,
  `panic_wp_any`).  Return bound `-1 <= r <= n`, deliberately WEAKER than
  the C's `0 <= i <= n`: under-promising costs filewrite nothing
  (`pipe_rw_ret` admits -1 anyway) and keeps the eventual discharge small.
- **`iris/ProofFilewriteParts.v`** — 1329 lines, the whole non-ghost half of
  filewrite: the 96-byte frame, all the arithmetic, SEVEN block lemmas, and
  the share-generation algebra.  `Print Assumptions` on `fw_epi` / `fw_pro` /
  `fw_panic`: 5 platform axioms + funext; on `fw_shr_regen`: **Closed under
  the global context**.

**NOT WRITTEN, parked green: `ProofFilewrite.v`, `LinkFilewrite.v`.**  What
is left is the control flow between the blocks plus the FD_INODE arm's ghost
work (peel/rebuild `ic_loaded`, `off_checkout`/`off_checkin`, writei's
fifteen post clauses, the log reservation per chunk, the type-witness join).
file.c stays 6/7.  The three landed files carry their own `_CoqProject` rows;
`ProofFilewrite.v` / `LinkFilewrite.v` do NOT (they do not exist yet).

### THE DECODE, READ OFF `CodeFilewrite.v` IN FULL — and one fact S3a missed

The tracked `xv6-riscv/kernel/kernel.asm` is not in this checkout, so the
control-flow graph below was reconstructed from `CodeFilewrite.v`'s 118 AST
lemmas.  S3a/S3f's four corrections all hold.  A FIFTH one does not appear in
any earlier list:

**5. THE FD_INODE ARM HAS A HOISTED ZERO-TRIP TEST.**  `bge x0,a2` at +0x32
   (`BTYPE (180, a2, zreg, BGE)`, i.e. branch when `0 >= n`) jumps to +0xe6,
   which sets `i = 0` and joins the tail at +0xf4 — so the `while (i < n)`
   loop body is entered only for `n >= 1`, and on the `n <= 0` path
   s1/s3/s7/s8/s9 are NEVER SPILLED (their `c.sdsp`s are at +0x36..+0x3e,
   AFTER the branch) and never restored.  gcc's loop rotation; it is a fifth
   arm-internal path, and it is why `fw_epi` takes seven frame slots as
   arbitrary words.

The full graph (offsets from `KernelSyms.filewrite`):

```
+0x00 lbu a5,9(a0)          f->writable
+0x04 beq a5,x0 -> +0x122   NOT writable: c.li a0,-1 ; c.jr ra at +0x124
                            (BEFORE the prologue -- sp untouched: note 1)
+0x08..+0x14  PROLOGUE      push 12; sdsp ra/s0/s2/s5/s6; addi4spn s0,sp,96
+0x16 c.mv s2,a0   s2 = f
+0x18 c.mv s6,a1   s6 = addr
+0x1a c.mv s5,a2   s5 = n
+0x1c c.lw a5,0(a0)         f->type
+0x1e/+0x20  li a4,1 ; beq -> +0x54   FD_PIPE
+0x24/+0x26  li a4,3 ; beq -> +0x5c   FD_DEVICE
+0x2a/+0x2c  li a4,2 ; bne -> +0x10a  ELSE: panic (note 3)
--- FD_PIPE ---
+0x54 c.ld a0,16(a0) ; +0x56 jal pipewrite ; +0x5a c.j -> +0xfc
--- FD_DEVICE ---
+0x5c lh a5,36(a0) ; +0x60 slli a3,a5,48 ; +0x64 c.srli a3,a3,48
+0x66 li a4,9 ; +0x68 bltu a4,a3 -> +0x126   (out of range: -1)
+0x6c..+0x78  &devsw[mj].write at OFFSET 8, and the slot   (note 2)
+0x7a c.beqz a5 -> +0x12a   (null slot: -1)
+0x7c c.li a0,1 ; +0x7e c.jalr a5 ; +0x80 c.j -> +0xfc
--- FD_INODE ---
+0x30 c.sdsp s4,48(sp)
+0x32 bge x0,a2 -> +0xe6    ZERO-TRIP (note 5)
+0x36..+0x3e  sdsp s1,s3,s7,s8,s9
+0x40 c.li s4,0             i = 0
+0x42/+0x44 lui/addi s7,3072    max          (note 4)
+0x48/+0x4a lui/addiw a5,3072 ; +0x4e c.mv s9,a5   max, twice
+0x50 c.li s8,1             writei's user_src, hoisted
+0x52 c.j -> +0xcc          the loop is BOTTOM-TESTED
  LOOP BODY @ +0x82
  +0x82 addiw s3,s3,0       sext.w n1
  +0x84 jal begin_op
  +0x88 c.ld a0,24(s2) ; +0x8c jal ilock
  +0x90 c.mv a4,s3   (n1) ; +0x92 c.lw a3,32(s2)  (f->off)
  +0x96 add a2,s4,s6 (addr+i) ; +0x9a c.mv a1,s8 (1) ; +0x9c c.ld a0,24(s2)
  +0xa0 jal writei
  +0xa4 c.mv s1,a0   r = writei(...)
  +0xa6 bge x0,a0 -> +0xb4     skip the offset update when r <= 0
  +0xaa c.lw a5,32(s2) ; +0xae c.addw a5,a0 ; +0xb0 c.sw a5,32(s2)
  +0xb4 c.ld a0,24(s2) ; +0xb8 jal iunlock ; +0xbc jal end_op
  +0xc0 bne s3,s1 -> +0xea     SHORT WRITE: break
  +0xc4 addw s4,s4,s1          i += r
  +0xc8 bge s4,s5 -> +0xda     i >= n: normal exit
  LOOP TEST @ +0xcc
  +0xcc subw a5,s5,s4 ; +0xd0 c.mv s3,a5     n1 = n - i
  +0xd2 bge s7,a5 -> +0x82                   n1 <= max
  +0xd6 c.mv s3,s9 ; +0xd8 c.j -> +0x82      n1 = max
--- the joins ---
+0xda..+0xe2 restore s1,s3,s7,s8,s9 ; +0xe4 c.j -> +0xf4
+0xe6 c.li s4,0 ; +0xe8 c.j -> +0xf4         the zero-trip path
+0xea..+0xf2 restore s1,s3,s7,s8,s9 ; fall to +0xf4
+0xf4 bne s5,s4 -> +0x12e    i != n: -1 (li a0,-1; ldsp s4; c.j +0xfc)
+0xf8 c.mv a0,s5 ; +0xfa c.ldsp s4,48(sp)
+0xfc..+0x108 EPILOGUE  restore ra/s0/s2/s5/s6 ; addi16sp 96 ; c.jr ra
+0x10a..+0x11e  the ELSE arm: six spills, then panic("filewrite")
```

The frame, in SLOTS off the entry sp (`pa_stk sp0 k = sp0 - 8k`):

| slot | disp | reg | spilled at | restored at |
|---|---|---|---|---|
| 1 | 88 | ra | +0x0a | +0xfc |
| 2 | 80 | s0 | +0x0c | +0xfe |
| 3 | 72 | s1 | +0x36 / +0x10a | +0xda / +0xea |
| 4 | 64 | s2 | +0x0e | +0x100 |
| 5 | 56 | s3 | +0x38 / +0x10c | +0xdc / +0xec |
| 6 | 48 | s4 | +0x30 / +0x10e | +0xfa / +0x130 |
| 7 | 40 | s5 | +0x10 | +0x102 |
| 8 | 32 | s6 | +0x12 | +0x104 |
| 9 | 24 | s7 | +0x3a / +0x110 | +0xde / +0xee |
| 10 | 16 | s8 | +0x3c / +0x112 | +0xe0 / +0xf0 |
| 11 | 8 | s9 | +0x3e / +0x114 | +0xe2 / +0xf2 |
| 12 | 0 | — | never | never |

### THE ONE DESIGN FINDING: `SpecIunlock`'s postcondition LOSES the generation

`SpecIlock` v5 takes `inode_shr_gen k s dev inum g` and returns
`ity_shot g (di_type dn)` at THAT `g`; `SpecIunlock` gives the share back as
the arity-preserving `inode_shr k s dev inum`, i.e. `∃ g'`.  filewrite is the
first caller that has to survive that: iteration 2 must feed ilock a
generation-named share and then join ilock's shot with the fd's own
`ity_shot fwn_g fwn_ty` through `ity_shot_agree`, which needs ONE gname.  The
same gap bites the CONTRACT: `filewrite_fs_out` demands
`inode_shr_gen … (fwn_g fn)`, which a single chunk could not produce either.

**It is provable without touching any frozen file, and the mechanism is in
`ProofFilewriteParts.v`.**  §17.6's argument — a generation bump needs the
slot's WHOLE liveness unit, which this caller's share denies — is true but
is not exposed by the contract, so filewrite proves it instead: it HALVES its
share (`fw_shr_gen_halve`), lends ilock `s/2`, keeps `s/2`, and when iunlock
returns `inode_shr k (s/2) …` the retained half's `live_gen` pins the
returned half's generation by `IcacheRef.live_gen_agree`
(`fw_shr_regen : inode_shr_gen k s1 … g -∗ inode_shr k s2 … -∗
inode_shr_gen k (s1+s2) … g`).  Rejoin, and the loop invariant carries the
share at `fwn_s` and `fwn_g` unchanged.  **`SpecIlock`'s `s` argument at the
call site is therefore `(fwn_s fn / 2)%Qp`, not `fwn_s fn`** — the checkout
descriptor pins whatever fraction it is handed (§14.8), so nothing else moves.
(A cleaner long-term fix is to add `g` to SpecIunlock's postcondition; that
touches five consumers and was out of S3g's scope.)

### WHAT `ProofFilewriteParts.v` GIVES THE CONTINUATION

Frame: `fw_push_96` / `fw_pop_96` / `fw_fp_96`, `fw_frm1..fw_frm11`
(displacement -> slot), `fw_frame_back`.
Values: `fw_lui1`, `fw_addi_m1024`, `fw_addiw_m1024` (the two 3072s),
`fw_li0`, `fw_addv32_moi2`, `fw_subv32_moi`, `fw_sextw_moi` (the +0x82
`sext.w` — NOT `RiscvExtras.sextw_moi`, which is stated at the other
spelling of a zero immediate), `fw_subw_moi`, `fw_addw_moi`, `fw_bge_moi`,
`fw_bge0_moi`, `fw_neq_moi`.
Blocks (all hart-generic):

- `fw_pro`   +0x08..+0x14, the prologue -> the twelve slots + the register map;
- `fw_epi`   +0xfc..+0x108, the epilogue, all six returning exits;
- `fw_rest5` the five `c.ldsp`s, over six literal pcs (+0xda and +0xea);
- `fw_m1j`   `c.li a0,-1; c.j +0xfc` (+0x126 and +0x12a);
- `fw_m1j4`  the same with s4's restore wedged in (+0x12e);
- `fw_devidx` +0x6c..+0x78, `&devsw[mj].write` at offset 8 and its value;
- `fw_panic` +0x10a..+0x11e, THE WHOLE ELSE ARM, closed by `panic_wp_any`.

`ProofFilereadParts.v` is IMPORTED rather than copied: the dispatch's `c.li`
immediates, the `short` zero-extension, the `devsw` index shift and the
`c.addw` store value are character-for-character fileread's.

### The loop, as designed but not yet built

Fuel = `n - i` (or the chunk count `⌈(n-i)/3072⌉`); the decrease is
`i += r` with `r = n1 >= 1` on every non-exiting iteration.  Invariant:
`0 <= i <= n`, `i` in s4, `n` in s5, 3072 in s7 and s9, 1 in s8, the share at
`fwn_s`/`fwn_g` (see above), `off_inv`, `bitmap_res` at a `used_i` with
`fwn_used ⊆ used_i`, and the twelve frame slots.  Per iteration:
`begin_op` mints `log_op γ MAXOPBLOCKS`; writei's `wi_cost off n1 <= MAXOPBLOCKS`
is the budget premise to discharge; `end_op` spends whatever is left.
`fw_chunk_joint` (SpecFilewrite) discharges writei's joint bound from
`n1 <= 3072` and `off_wf`; `fw_off_advance` keeps `off_wf` after the
`c.addw`/`c.sw` pair.  The re-park closes as §17.6 says: `wi_dinode`
preserves `di_type` definitionally, `ity_shot_agree` pins it to `fwn_ty`,
`fwn_ty <> T_DIR` makes `DirView.dir_ok` vacuous on the new data.

### Mirror evidence

`full.sh` `EXIT=0`, **1036 `.vo`** (1033 + the three new), zero `Error`.
`tools/lemma_diff.py --ref HEAD`: 3 files, TWO NEWAXIOMs and nothing else —
`SpecConsolewrite`'s `Module Type CONSOLEWRITE` seal (one seal per new Spec)
and `LinkConsolewrite`'s named `Axiom` (LinkConsoleread-precedented).  Nothing
GONE, nothing ADMITTED.  `Print Assumptions`: `Fileread.wp_fileread_sconf` =
5 platform axioms + funext + its known `Consoleread.wp_consoleread_sconf`
(unchanged); `Filestat.wp_filestat_sconf` = 5 + funext (unchanged);
`fw_epi` / `fw_pro` / `fw_panic` = 5 + funext; `fw_shr_regen` = Closed under
the global context.  md5s verified equal on both sides after every scp:
`SpecConsolewrite.v` `34877a4175cc4fcc0902ed48fbd971f1`,
`LinkConsolewrite.v` `5efab2a781630775cba1670b39ce6b83`,
`ProofFilewriteParts.v` `6064f0366771052eedbdec4e323aa0ae`,
`_CoqProject` `c831e4adb5f567c9765b87de4d8b958f` (patched IN PLACE on the
mirror with `sed`, never scp'd).  Mirror `git status`: `_CoqProject` modified
plus the three untracked new files, nothing else; no scratch left.

### Traps recorded

1. **`rget` lives in `HartTp.v`, not `RegFile.v`.**  A Parts file that spells
   a `c.slli`/`c.add` result symbolically needs `Require Import HartTp`; the
   failure is *"The variable rget was not found in the current environment"*,
   which reads like a section-variable problem and is an import problem.
2. **A `Context` for the icache's pure ghost lemmas still needs `riscvGS`.**
   `IcacheRef.inode_shr_gen` is `inode_ident` (a `↦₄`) beside `live_gen`, so
   `` `{ICFG : icfg, !icacheG Σ} `` alone leaves seven existential instances
   unresolved.  The error names `?Equiv : Equiv (iPropI ?Σ)` first, which
   points nowhere useful.
3. **`coq_makefile` does NOT need re-running after a `_CoqProject` edit on
   this tree.**  The generated `CoqMakefile.conf` computes its file list at
   make time (`$(COQMKFILE) -sources-of -f _CoqProject`), so the `sed` patch
   is the whole job; regenerating is harmless but S3f's extra step is not
   load-bearing.
4. **`c.lui` is `wp_clui_s_sconf`, not `wp_lui_s_sconf`** — the two differ
   only in the `instr`'s compressed flag, and +0x42 (`c.lui s7,0x1`) is
   compressed while +0x48 (`lui a5,0x1`) is not.  Same trap for
   `c.addw`/`addw` (`wp_addw_s_sconf` vs `wp_addw4_s_sconf`) at +0xae/+0xc4.

## S3h — STOPPED AND REPORTED: `SpecWritei`'s postcondition cannot rebuild
## `ic_loaded`.  `fw_tail` landed and full-gated; `ProofFilewrite` still unwritten

**The frozen `SpecFilewrite` is not provable against the frozen
`SpecWritei`.**  The FD_INODE arm's re-park needs
`IcacheEscrow.ic_loaded`, whose `⌜InodeLock.inode_ok cov logstart dn' bm'
data'⌝` conjunct has SEVEN components, and writei's postcondition
re-establishes only FIVE:

| # | `inode_ok` conjunct | after writei |
|---|---|---|
| 1 | `blkmap_wf cov logstart bm'` | post ✓ |
| 2 | `bm_covers bm' (di_size dn')` | post ✓ |
| 3 | `di_addrs dn' = bm_cells bm'` | post ✓ |
| 4 | `bv_unsigned (di_type dn') <> 0` | ✓ — `wi_dinode` keeps `di_type` DEFINITIONALLY |
| 5 | `bv_unsigned (di_size dn') <= MAXFILE*BSIZE` | **MISSING** — post gives only `< 2^31` |
| 6 | `blk_holes_zero bm' data'` | post ✓ |
| 7 | `inode_sized data'` | **MISSING OUTRIGHT** |

§17.6/§17.7's type witness is NOT the problem: conjunct 4 and `dir_ok` both
close exactly as `SpecFilewrite`'s header says (`ity_shot_agree` pins
`di_type dn = fwn_ty fn`, `fc_wbool` is true past +0x04, `dir_ok_not_dir`
finishes).  The blocker is the two *arithmetic/shape* conjuncts.

**Why no earlier caller hit it.**  fileread re-parks with the IDENTICAL
`data` and `dn` — readi changes no byte — so all seven conjuncts go back
verbatim (`ProofFileread.v` 1999–2010 and 2262–2273: `exact Hdok`,
`exact Hsized`, …).  dirlink, the only other writei caller, does not re-park
at all: it FORWARDS writei's postcondition into its own contract
(`SpecDirlink.v:395`).  **filewrite is the first re-parker of a CHANGED
payload**, which is why the gap is only visible now.

**Why (5) cannot be recovered at the call site.**  On the success arm
`dn' = wi_dinode dn bm' off tot`, whose size field is
`max (di_size dn) (off+tot)`.  `off <= MAXFILE*BSIZE` (`off_wf`) and
`n1 <= 3072`, so `off+n1` reaches 277504 > 274432 — reachable, and exactly
the case a file at maximum size produces.  `SpecFilewrite.fw_off_advance` is
stated to CONSUME `¬(MAXFILE*BSIZE < off+n1)`, and nothing supplies it:
writei's two-arm disjunction exposes the guard only as a CONSEQUENCE of
returning -1, never as an exclusion on the counting arm.  A case split on
`decide (MAXFILE*BSIZE < off+n1)` does not rescue it — in the "yes" branch
the contract still permits arm 2.

**Why (7) cannot be recovered at all.**  `inode_sized data'` is
`forall i < MAXFILE, length (data' i) = BSIZE`.  The range clause is about
`file_byte data' k = data' (k `div` BSIZE) !!! (k `mod` BSIZE)`, and
`list_lookup_total` returns the INHABITANT out of range, so a `data'` with
short lists satisfies it.  The resource cannot supply it either:
`inode_blocks` is a big-op of `blk_res`, `blk_res` is `True` at holes and
`fsblock ∗ blk_own` at allocated indices, and `FsBlocks.fsblock γ bno bs`
is `bno ↪[fs_L γ]{#(1/2)} bs` — a bare ghost_map half.  `InodeInv.v` 503–506
says this in prose already ("`FsBlocks.fsblock` is a bare ghost_map half
with no length side condition"), which is *why* conjunct 7 exists.  Holes
are fine (`blk_holes_zero` gives `replicate BSIZE`); allocated blocks are not.

### THE REPAIR (out of S3h's scope; ruling needed)

Two clauses on `SpecWritei`'s postcondition:

```coq
⌜bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
⌜inode_sized data'⌝ -∗
```

- **(5) is nearly free.**  `wi_loop` ALREADY takes
  `(off + n <= MAXFILE * BSIZE)%nat` as a premise (`ProofWritei.v:1598`) and
  the top-level proof already derives `Hrng : (off + n <= MAXFILE*BSIZE)%nat`
  the moment the guard at +0x2a falls (`ProofWritei.v:3736`).  It is a
  threading job, not a proof.
- **(7) is the real work.**  `inode_sized` appears NOWHERE in
  `ProofWritei.v`, so `wi_loop`'s invariant has to carry it and re-establish
  it at every block update.  `InodeInv.inode_sized_insert`
  (`inode_sized data -> length bs = BSIZE -> inode_sized (<[i := bs]> data)`)
  is exactly the tool, and the buffer writei installs is a bread'd BSIZE
  block, so the length is on hand.

**Ripple.**  `SpecWritei` (2 postcondition clauses), `ProofWritei`
(`wi_loop`'s invariant + the two return sites), and the three `ProofDirlink`
destructuring sites (1692 / 2060 / 2436) plus `SpecDirlink` if it forwards
them.  **Premise count is UNCHANGED** at every call site — both additions
are postcondition clauses, so only consumers' `iIntros` patterns widen by
two.  Nothing in the icache, the escrow or `SpecFilewrite` moves;
`SpecFilewrite` stays FROZEN exactly as it is, and `fw_off_advance` becomes
dischargeable because (5) makes the "yes" branch of the case split
irrelevant (the size cap comes from writei rather than from the guard).

### What DID land, green

**`ProofFilewriteParts.fw_tail`** — +0xf4 through the epilogue, i.e. the
FD_INODE arm's WHOLE tail, and the eighth block in the file.  All THREE
paths that reach +0xf4 (the zero-trip jump at +0xe8, the normal loop exit
through the five `c.ldsp`s at +0xda, the short-write break through the same
five at +0xea) arrive in ONE shape — s4 = i, s5 = n, s1/s3/s7/s8/s9 already
back at the caller's values — so the join is one lemma with `i` a parameter.
`bne s5,s4` then picks between `c.mv a0,s5 ; c.ldsp s4,48(sp)` into `fw_epi`
and +0x12e, which is `fw_m1j4`.  The postcondition is the disjunction
`rv = -1 ∨ (i = n ∧ rv = n)`, which a caller turns into `filewrite_ret` with
`filewrite_ret_m1` / `filewrite_ret_all`.  `Print Assumptions fw_tail`:
5 platform axioms + funext.  It needs NO ghost state and survives the repair
untouched.

### Traps recorded

1. **`ProofFilewriteParts.v` was missing `WpSconfBtype` from its imports** —
   it had `WpSconfAlu WpSconfMem WpSconfCtl` only, because S3g's seven blocks
   contain no full-width conditional branch (the panic arm and the epilogue
   are straight-line, and `fw_m1j`/`fw_m1j4` end in `c.j`).  Any block with a
   `beq`/`bne`/`bge`/`bltu` needs it; the failure is *"The variable
   wp_bne_fall_s_sconf was not found in the current environment"*.
2. **`fw_li0`'s comment mislabels it.**  The header says "[c.li s8,1] at
   +0x50", but the lemma is stated at the ZERO immediate — it is +0x40's
   `c.li s4,0`.  +0x50's `c.li s8,1` is `ProofFilereadParts.fr_li1`.
3. **`RTYPE`/`RTYPEW` argument order is `(rs2, rs1, rd, op)`**, not
   `(rs1, rs2, rd, op)`: `fwri_0cc = RTYPEW (Regidx 20, Regidx 21, Regidx 15,
   SUBW)` is `subw a5,s5,s4`, i.e. rs2 = s4 and rs1 = s5.  Reading it the
   other way inverts the loop's `n - i` into `i - n`.
4. **`fw_epi`'s `Hthr` does NOT exclude s4**, so anything that reaches +0xfc
   must already have restored it; `fw_tail` is where that happens (+0xfa on
   the full-write path, inside `fw_m1j4` on the short-write path).

### Mirror evidence

`full.sh` `EXIT=0`, **1036 `.vo`** (unchanged — one file edited, none added),
zero `Error`.  `tools/lemma_diff.py --ref HEAD`: *"1 file(s) checked --
CLEAN (nothing dropped, nothing admitted, no new assumption)"*.
`Print Assumptions fw_tail` = the 5 platform axioms + funext, checked in a
scratch file that was deleted afterwards.  md5 verified equal on both sides
after the scp: `ProofFilewriteParts.v` `3499da0354bcdf79e3fceef8ac8928d2`.
`_CoqProject` NOT touched (no new file).  Mirror `git status`:
`iris/ProofFilewriteParts.v` modified, nothing else; no scratch left.

## S3i — the `SpecWritei` repair LANDED AND FULL-GATED (as PRESERVATIONS, not
## facts); `ProofFilewrite` STOPPED AND REPORTED on the LOG BUDGET

### Part 1 — landed, full-gated

`SpecWritei`'s postcondition gains S3h's two clauses, placed right after
`bm_covers`, but **as PRESERVATIONS**:

```coq
⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
 bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
⌜inode_sized data -> inode_sized data'⌝ -∗
```

**S3h's "both are provable outright" is WRONG, and the implication form is
what makes the ruling's "premise counts unchanged everywhere" achievable.**
Neither clause holds unconditionally:

- **the size cap.**  `wi_dinode` installs `max(di_size dn, off+tot)`.  The
  +0x2a guard bounds `off+n`, and nothing in writei's premises bounds the
  CALLER's `di_size dn` below `MAXFILE*BSIZE` — the premise is `< 2^31`,
  which is 7800× weaker.  So the max can exceed the cap on the WRITING arm,
  and on the -1 arm `dn' = dn` outright.  S3h's "(5) is nearly free /
  a threading job" is true only of the `off+tot` half of the max.
- **`inode_sized`.**  writei touches only the blocks its range straddles;
  every other index keeps `data i`, whose length no resource in the cone
  constrains (`FsBlocks.fsblock` is a bare ghost_map half — InodeInv.v
  503-506, which is the very reason conjunct 7 exists).  And again
  `data' = data` on the -1 arm.

Stated unconditionally they would both have to become PREMISES, i.e. exactly
the ripple the ruling forbade: `SpecDirlink` would gain `inode_sized data`
(it already has the size cap at :265) and create/S5 would owe both.  The
implication form costs a re-parking caller nothing — filewrite holds both
antecedents already, out of the very `inode_ok` it is about to rebuild — and
costs dirlink nothing at all (`clear`ed at its boundary with a comment).

Threading, as built:

- `ProofWriteiParts`: `wi_size_cap` (the max, over `Z` throughout so the
  274432 literal is never unary), `wi_sized_bmap` (across bmap's deposit —
  the deposited block is a `replicate BSIZE`), `wi_sized_step` (deposit then
  block update; `wi_splice` is built from `seq 0 BSIZE`, so `wi_splice_len`
  is the length).
- `ProofWritei`: `wi_cont` +2 clauses; `wi_ret` +2 (the implications);
  `wi_join` / `wi_size` +2 each (`(off+tot <= MAXFILE*BSIZE)%nat` plus the
  `inode_sized` implication — wi_join DERIVES the size-cap implication from
  the former with `wi_size_cap`); `wi_loop`'s invariant carries
  `inode_sized data -> inode_sized dataI`.
- **FOUR top-level sites, not three.**  Besides `wi_ret`@3731 (the
  `off+n > MAXFILE*BSIZE` -1 exit), `wi_join`@3873 (the n=0 path) and
  `wi_loop`@4073, the `off > ip->size` -1 exit feeds `wi_cont` DIRECTLY with
  an inline `iApply ("Hcont" $! …)` at :3342 — no `wi_ret` — so a
  `grep "iApply (wi_ret"` sweep misses it.  It surfaces as
  *"iSpecialize: cannot instantiate"* with the residual wand printed, ~450
  lines below the sites you did edit.
- `ProofDirlink`: **ONE** consumer site, not three (the S3h ripple estimate
  of ":1692/:2060/:2436" is stale — `grep -rl wp_writei_sconf` gives exactly
  `ProofDirlink.v`).  Its `iIntros` widens by two and the pair is `clear`ed.

### Part 2 — STOPPED AND REPORTED: the FD_INODE loop cannot pay for a chunk

**`begin_op` pays `log_op γ MAXOPBLOCKS` = 10 units.  writei's budget premise
for the chunk the code hands it is up to 25.**  All figures machine-checked
in a scratch probe (compiled `DONE = 0`, then deleted):

| chunk | `wi_blocks` | `wi_cost` | vs MAXOPBLOCKS = 10 |
|---|---|---|---|
| `off = 0`, `n1 = 1024` | 1 | **7** | fits |
| `off = 16*63`, `n1 = 16` (dirlink) | 1 | **7** | fits |
| `off = 1023`, `n1 = 2` | 2 | **13** | BUSTS |
| `off = 1023`, `n1 = 1024` | 2 | **13** | BUSTS |
| `off = 0`, `n1 = 3072` | 3 | **19** | BUSTS |
| `off = 1023`, `n1 = 3072` | 4 | **25** | BUSTS |

`wi_cost off n = 6 * wi_blocks off n + 1`, and only `wi_blocks = 1` fits.  So
the arm is provable ONLY for a chunk that stays inside one block — while the
code's chunk is `n1 = min(n - i, 3072)` (s7/s9 at +0x42..+0x4e).  **The very
first iteration of any write of more than one block busts it**, and a 2-byte
write straddling a block boundary busts it too.  This is why no earlier
caller hit it: dirlink's only write is 16 bytes at a 16-aligned offset
(`ProofDirlink.dl_wi_cost : wi_cost (16*k) 16 = 7`), and readi has no budget
at all.

**It is the recorded looseness, coming due.**  `SpecWritei.v`'s own header
says so: *"6 per block is bmap's worst case (two ballocs plus its own
log_write), not the amortised cost -- the indirect block is allocated at most
once in a file's life.  Tightening it needs an arm-aware bmap budget, not a
change here."*  filewrite is the first caller for which the amortisation
matters, and the gap between the model and the machine is 6/block vs. the
2/block + fixed overhead that xv6's own `max` formula is derived from:
`((MAXOPBLOCKS-1-1-2)/2)*BSIZE` reads "one slot for the inode, one for the
indirect, two spare, and the rest two-per-data-block".

**What a repair has to do (sized, not chosen — this is a coordinator ruling).**
Three things stack, and the first two are proof engineering while the third
may be a kernel finding:

1. **Hoist the indirect block out of the per-block charge.**  bmap's 5 is
   `2 ballocs x 2 + its own log_write`, but the INDIRECT balloc happens at
   most once per file, not once per block.  An arm-aware `SpecBmap` budget —
   the direct-hit arm at 0, the data-alloc arm at 2, the
   indirect-alloc-too arm at 5 — turns writei's per-block 6 into a per-block
   3 plus a per-CALL 3.  Touches `SpecBmap`, `ProofBmap`, `SpecWritei`'s
   `wi_cost`, `ProofWritei`'s five budget `lia`s, and re-derives
   `dl_wi_cost`.  Gets a 4-block chunk to `4*3 + 3 + 1 = 16`.  **Still > 10.**
2. **Model log_write's ABSORPTION.**  balloc's `bzero` log_writes the very
   block writei then log_writes again; xv6 charges that once.  `LogInv`
   already has the set-indexed `log_opS γ u Sb` (:278) — the vocabulary
   exists — but every fs.c spec above it is stated on the counted
   `log_op γ u` (:288).  Absorption takes the per-block 3 to 2, i.e.
   `2B + 3`.  For B = 3 that is 9; **for B = 4 it is 11, still > 10.**
3. **B = 4 IS REACHABLE, and that is the part to rule on before building
   anything.**  `f->off` need not be block-aligned (it advances by whatever
   the last short write returned), so a 3072-byte chunk can straddle four
   blocks, and xv6's own `max` formula budgets for three.  Either the honest
   bound is `2B+3 <= 11 > MAXOPBLOCKS` — a genuine `kernel-defects.md`
   candidate, the same shape as D1 — or there is an absorption argument that
   makes the fourth block free (the two extreme blocks are partial, so at
   most one of them can be a fresh allocation... which is FALSE for a write
   past the end of the file).  **Check this against the machine before
   choosing between (1)+(2) and a defect report.**

Nothing else about the arm is in doubt: the re-park now closes (Part 1's two
clauses are conjuncts 5 and 7, `wi_dinode` keeps `di_type` definitionally,
`ity_shot_agree` pins the type and `dir_ok_not_dir` finishes), the share
algebra is `fw_shr_gen_halve`/`fw_shr_regen`, and the whole tail is
`fw_tail`.  The budget is the ONE thing between S3g's blocks and a complete
`ProofFilewrite`.

**`ProofFilewrite.v` / `LinkFilewrite.v` remain unwritten; file.c stays 6/7,
and S4's three shells stay blocked.**

### Gate (Part 1)

Mirror `full.sh` `EXIT=0`, **1036 `.vo`** (unchanged — four files edited,
none added), zero `Error`.  `tools/lemma_diff.py --ref HEAD`: *"4 file(s)
checked -- CLEAN (nothing dropped, nothing admitted, no new assumption)"*.
`Print Assumptions` in a scratch file (deleted afterwards):
`Writei.wp_writei_sconf` and `Dirlink.wp_dirlink_sconf` = 5 platform axioms +
`functional_extensionality_dep`; `Fileread.wp_fileread_sconf` = the same plus
its known `Consoleread.wp_consoleread_sconf`; `Filestat.wp_filestat_sconf` =
5 + funext.  Every set UNCHANGED.  md5s verified equal on both sides after
every scp: `SpecWritei.v` `b20d163777ed09b8d112c8fad23b8b6b`,
`ProofWriteiParts.v` `0d1d1e21ad0b0b7bf1485f9e410f7c7c`,
`ProofWritei.v` `53d06fcccc3ddcbd856995012ee11d46`,
`ProofDirlink.v` `8c096c231fe20f4c38ba7150ca9ea990`.  `_CoqProject` NOT
touched (no new file).  Mirror `git status`: those four modified, nothing
else; no scratch left.

### Traps recorded

1. **A POSTCONDITION-ONLY STRENGTHENING IS ONLY FREE IF THE CALLEE'S OWN
   PREMISES ALREADY IMPLY IT — AND THE -1 ARM IS WHERE TO CHECK.**  Both of
   S3h's clauses look like they follow from the loop, and both fail on the
   early-return arm where the callee returns the caller's OWN record
   untouched.  A "the post gains a conjunct, no premise moves" ruling should
   be checked against every arm that returns its inputs verbatim before it is
   budgeted; the escape, when the caller has the fact anyway, is to state the
   PRESERVATION rather than the fact.
2. **A LOG-BUDGET PREMISE IS A NUMERIC OBLIGATION AND WANTS ARITHMETIC, NOT
   READING.**  writei's `wi_cost` and `MAXOPBLOCKS` are three lines apart in
   two files and both look fine; the mismatch is only visible once you
   evaluate `wi_cost` at the chunk the CODE passes.  Do that with a
   `vm_compute` probe at the top of a stage that threads a reservation
   through a loop, not after the ghost work is written.
3. **`grep "iApply (<block lemma>"` DOES NOT FIND EVERY CONSUMER OF A
   CONTINUATION.**  ProofWritei's `off > ip->size` arm inlines
   `iApply ("Hcont" $! …)` instead of going through `wi_ret`, so a sweep that
   widens the block lemmas' argument lists compiles for 20 minutes and then
   fails at an untouched site.  Grep the CONTINUATION's name (`Hcont`) as
   well as the lemmas'.
4. **`lemma_diff` stays CLEAN across a pure statement-strengthening**, which
   is correct and also means it is no evidence at all here — the gate that
   sees this change is `Print Assumptions` plus the full build.

## S3j — THE BUDGET RULING: **xv6 IS LOG-SOUND AT MAXOPBLOCKS = 10.**
## The absorption seam LANDED (`WriteiBudget.v`); the four-file retrofit is
## sized and NOT started

### The verdict (step 0) — NO KERNEL DEFECT

**S3i's item (3) — "either the honest bound is `2B+3 <= 11 > MAXOPBLOCKS`, a
genuine `kernel-defects.md` candidate" — is REFUTED.**  The honest bound is
`B + 3 <= 7`, and the fact that closes the gap was already a premise of
every fs.c contract in the tree:

> **`BitmapInv.bitmap_geom_ok` contains `0 < size <= BPB`, with
> `BPB = 8 * BSIZE = 8192`.  There is EXACTLY ONE BITMAP BLOCK.**

So `BitmapInv.BBLOCK` collapses to `bmapstart` for every allocatable block
(`WriteiBudget.one_bitmap_block`), and all FIVE ballocs of a four-block
chunk — the indirect one and the four data ones — log_write **the same
block**.  S3i's sizing charged one bitmap block *per data block*; that is
where the phantom 11 came from.  It is the same fact `LogInv`'s own header
already invokes for itrunc (*"every one of them a bit in THE SAME bitmap
block (FSSIZE = 2000 < BPB = 8192)"*) and that `SpecItrunc` is built on —
the vocabulary was in the tree, one level away, and the S3i sizing did the
arithmetic without it.

**The per-DISTINCT-block multiset for a B-block chunk**, machine-checked as
`WriteiBudget.wi_logset_size` / `wi_logset_fits`:

| group | count | why |
|---|---|---|
| the data blocks the range straddles | `B` | distinct by `blkmap_wf`'s injectivity |
| `bmapstart` | ≤ 1 | one bitmap block (above); every balloc absorbs after the first |
| the indirect block | ≤ 1 | at most one per file; bmap's own `log_write(bp)` absorbs against balloc's `bzero` of it |
| `IBLOCK inum inodestart` | 1 | the trailing `iupdate` — it runs on **every** returning path, `n = 0` included |
| | **`B + 3`** | |

with `B <= 4` (`wi_blocks_le4`) and **4 genuinely reached**
(`wi_blocks_four_reached`: `wi_blocks 1023 3072 = 4`, because `f->off` need
not be block-aligned).  Worst case **7 against MAXOPBLOCKS = 10, three
slots to spare.**  The bound needs no disjointness between the four groups
— coincidences only shrink the set.

So **the C code is right and the accounting was wrong**, exactly as it was
for itrunc.  Nothing was added to `kernel-defects.md`.

### All three absorptions are load-bearing — machine-checked

Both intermediate repairs S3i sized still bust, and the file records them
so neither is dropped as "probably enough":

| accounting | at `off=1023, n=3072` | vs 10 |
|---|---|---|
| `wi_cost` (today) = `6B+1` | **25** | busts |
| `wi_cost_armaware` = `4B+3` (S3i piece 1 alone) | **19** | busts |
| `wi_cost_noabs` = `2B+3` (pieces 1+2, no data-block absorption) | **11** | busts |
| `wi_cost_tight` = `B+3` | **7** | **fits** |

`wi_cost_noabs` fits at `B = 3` (`= 9`) and busts only at `B = 4`
(`wi_cost_noabs_three_fits` / `_busts`).  **The fourth block is the whole
problem**, and it is reachable only because `f->off` is unaligned — which
is also why xv6's own `max = ((MAXOPBLOCKS-1-1-2)/2)*BSIZE` reads as
budgeting for three data blocks plus "two spare": the two spare slots are
what the fourth straddled block eats.  So the data-block absorption
(balloc's `bzero` of a fresh block vs writei's own `log_write` of the same
block) cannot be left out.

### What LANDED: `WriteiBudget.v`, the absorption seam

One new file, **additive — no existing statement moved**, so the whole
retrofit's ripple is still ahead.  `_CoqProject` gains one line after
`SpecWritei.v`.

**The chosen seam is `LogInv.log_opS`, not a new absorption lemma on the
counted form.**  The task's two options were "move writei's loop onto
`log_opS`'s set-based accounting" or "add `log_op_absorb` to the counted
form"; the second is **impossible** and it is worth recording why:
`log_op γ u = ∃ Sb, log_opS γ u Sb` *forgets the set*, so the counted ghost
cannot express "this op has already logged this block" at all — there is
nothing for an absorb lemma to be stated about.  The set-based form needs
**zero new ghost state and zero new invariant work**: `log_opS`,
`log_spend_step`, `log_absorb_step`, `op_sum_absorb` and the credit's
soundness clause `e.2 ⊆ LB` in `log_res` all already exist and already
carry the "the set dies with the entry at end_op" argument.

`log_amort γ F u` — *"u units are genuinely free, and one unit is still
held back for each block of `F` this op has not yet logged"*:

```coq
Definition log_amort (γ : log_names) (F : gset Z) (u : nat) : iProp Σ :=
  (∃ (Sb : gset Z) (v : nat),
     ⌜(u + size (F ∖ Sb) <= v)%nat⌝ ∗ log_opS γ v Sb)%I.
```

It is `SpecItrunc.bm_paid` generalised from ONE amortised block to a SET,
which is what writei needs (the bitmap block **and** the indirect block).
The potential `u + size (F ∖ Sb)` is what makes it work; `v` and `Sb` are
both existential because no caller can know either, and the `<=` (rather
than `=`) is forced because `log_opS` is an exact ghost_map element and its
budget cannot be weakened without the ledger authority.

Nine lemmas, all proven:

- `log_amort_intro` / `log_amort_elim` — in at `u + size F` units, out at
  `≥ u`; `elim` produces the counted `log_op` that iupdate and end_op take.
- `log_amort_weaken` / `log_amort_shrink` — monotone in `u`, **anti**-monotone
  in `F` (reserving fewer blocks is the weaker claim: `F` is capacity held
  back, not a claim of ownership).
- **`log_amort_present`** — the workhorse, and **IDEMPOTENT**: `u` is
  identical going in and coming out, on both arms.  Paid (`b ∈ Sb`):
  log_write's credited arm absorbs and the unit returns. Unpaid: the unit is
  spent, `b` joins `Sb`, and the held-back term drops by *exactly* one
  (`subset_size` on `F ∖ (Sb ∪ {[b]}) ⊂ F ∖ Sb`). So writei's loop
  invariant mentions `log_amort γ F u` and **never case-splits on which
  iteration was the first to touch the bitmap** — the same property that
  makes itrunc's 269 frees provable.
- `log_amort_spend` — one genuine unit for a block outside `F` (the
  per-data-block charge), stated over an arbitrary *larger* result set so a
  callee that logged more than it was asked about still re-establishes it.
- **`log_amort_adopt`** — enlarging `F` by a block the op has ALREADY
  logged is free. This is what lets writei enter its loop at
  `F = {[bmapstart]}` and **adopt the indirect block whose identity it does
  not learn until balloc returns it**, out of balloc's own credited
  postcondition. Without it the loop invariant would have to name a block
  that does not exist yet.
- `log_amort_reframe`, and `wi_amort` / `wi_amort_intro` / `wi_amort_elim` —
  the two-block instance writei's loop actually carries, entering at
  `u + 2`.

Plus the arithmetic: `FW_MAX` (spelled from `MAXOPBLOCKS`/`BSIZE`, not as
3072), `wi_blocks_le4`, `wi_blocks_four_reached`, `wi_blocks_dirlink`,
`wi_cost_tight`, **`wi_cost_tight_fits`** (the theorem that unblocks
filewrite), `wi_cost_tight_worst = 7`, `wi_cost_tight_dirlink = 4`.

### FINDING: the reshaped premise is NOT a pointwise weakening

`wi_cost` and `wi_cost_tight` are **incomparable**
(`wi_cost_tight_incomparable`): at `wi_blocks = 0` the loose form charges
**1** (a zero-block call runs no iteration, so only iupdate) and the tight
form charges **3**, because the bitmap and indirect capacities are reserved
unconditionally — which is precisely what keeps the loop invariant free of a
"did we straddle any block at all" case split.  `wi_cost_tight_le_loose`
therefore needs `1 <= wi_blocks off n` as a hypothesis.

**So the `SpecWritei` statement change may NOT be waved through as "the
premise got cheaper".**  Every consumer must be re-checked on the empty-range
arm.  In practice nothing is hurt — dirlink sits at `wi_blocks = 1` (4 vs
7) and any begin_op caller holds 10 — but a reviewer who assumes
monotonicity will mis-size the ripple, which is exactly the mistake that
produced S3i's 11.

### NOT STARTED: the four-file retrofit, sized bottom-up

The dependency chain is forced **bottom-up**, and each link is a stage-sized
job on a proof file of 3000–4100 lines. This is why S3j stopped here rather
than starting a retrofit it could not finish and leave green:

1. **`SpecBalloc` credited form** — cheapest, and FIRST. balloc is ASSUMED
   (`Module Type` + one `LinkBalloc` `Axiom`), so this is a contract
   widening with **no proof**. It must hand back a credit for `bmapstart`
   *and* for the block it allocated (its `bzero` logged it) — the shape is
   `SpecBfree.wp_bfree_gen`'s `(cr, Sb)` pair, already in the tree, verbatim.
   ⚠ **Check first** whether a new `Parameter` in `Module Type BALLOC` puts a
   new entry in the downstream `Print Assumptions` cones; the standing gate
   is 5 platform axioms + funext for `Writei`/`Dirlink`, and balloc's Axiom
   is *not* in them today.
2. **`SpecBmap` credited form + `ProofBmap`** (3270 lines) — the piece with
   the real uncertainty. **The architecture is already right for it:**
   `ProofBmap.bm_kit` is the single point where `log_op (ba_log a) n` is
   threaded, and every interior lemma already quantifies over the `ak :
   option bm_alloc` record. Put the credit set in the kit as an
   **existential with a fixed lower bound** — `∃ Sb, ⌜ba_cred a ⊆ Sb⌝ ∗
   log_opS (ba_log a) n Sb`, with `ba_cred` a new record FIELD — and the
   index is invariant (credits only grow), so **no interior lemma gains a
   binder**. This is verbatim the trick the file's own header already
   documents for `ba_used`: *"indexing by the set on ENTRY and existentially
   quantifying the CURRENT one instead makes the index INVARIANT."* Derive
   the existing counted `BMAP` by forgetting, so `BMAP_NOALLOC` and readi
   do not move.
3. **`SpecWritei` tight premise + `ProofWritei`** (4103 lines) — the loop
   invariant becomes `wi_amort γ bmapstart ind u`, `wi_cost` becomes
   `wi_cost_tight` at the premise, and the five budget `lia`s
   (`ProofWritei` :1922, :2817, :3040, :3875, :3892, :4092) re-derive. Note
   S3i's trap 3: the `off > ip->size` arm inlines `iApply ("Hcont" $! …)` at
   :3342 and a `wi_ret` grep misses it.
4. **`ProofDirlink`** (3111 lines) — ONE consumer site
   (`grep -rl wp_writei_sconf` gives exactly this file); discharge with
   `wi_cost_tight_dirlink` (= 4).

Then `ProofFilewrite` + `LinkFilewrite` on S3g's seven blocks + `fw_tail`,
which S3h/S3i left otherwise ready.

### Gate

Mirror `full.sh` `EXIT=0`, **1037 `.vo`** (1036 + `WriteiBudget.v`), zero
`Error`. `tools/lemma_diff.py --ref HEAD`: no existing statement touched, no
`GONE`, no `ADMITTED`. `Print Assumptions` on the
`Writei`/`Dirlink`/`EndOp`/`BeginOp`/`LogWrite` cones UNCHANGED — trivially,
since the change is one new leaf file and no existing file was edited; the
new file's own lemmas are axiom-free. `_CoqProject` `sed`-ed in place on the
mirror, never scp'd. Step-0 probe deleted from the mirror.

### Traps recorded

1. **A BUDGET-SOUNDNESS ARGUMENT IS ONLY AS GOOD AS THE GEOMETRY PREMISES
   YOU REMEMBERED TO LOOK UP.** S3i's "possible kernel defect" was a
   one-premise miss: `bitmap_geom_ok`'s `size <= BPB` was already in
   writei's own premise list, and reading it turns 11 into 7. Before
   escalating a cost overrun to `kernel-defects.md`, enumerate the callee's
   geometry premises and ask of each whether it *collapses* the multiset —
   `BBLOCK`-style collapses are invisible in a per-call cost table.
2. **THE COUNTED LEDGER CANNOT EXPRESS ABSORPTION, SO "ADD AN ABSORB LEMMA
   TO THE COUNTED FORM" IS NOT A DESIGN OPTION.** `log_op` is
   `∃ Sb, log_opS _ _ Sb`; the set is *forgotten*, so there is no
   already-logged-this-op predicate to state a credit against. When a choice
   is offered between "move to the richer form" and "add a lemma to the poor
   one", check that the poor one can even *mention* the fact.
3. **AN AMORTISED BUDGET WANTS A POTENTIAL FUNCTION, NOT A DISJUNCTION, ONCE
   MORE THAN ONE BLOCK IS AMORTISED.** `bm_paid`'s explicit paid/unpaid
   disjunction works for one block; for two it would be four arms.
   `u + size (F ∖ Sb) <= v` is one clause, scales to any `F`, and gives
   idempotence from `subset_size` instead of from case analysis.
4. **A "TIGHTER" COST FUNCTION IS NOT AUTOMATICALLY POINTWISE SMALLER.**
   `wi_cost_tight` beats `wi_cost` by 18 at four blocks and LOSES to it by 2
   at zero, because hoisting a per-block charge into a per-call reservation
   moves cost onto the empty arm. `vm_compute` both at the degenerate input
   before sizing the consumer ripple.

## S3l — LINK 2 LANDED AND FULL-GATED: bmap is set-form, one credit,
## arm-wise exact.  Link 3's loop algebra is PROVEN; links 3+4 NOT STARTED

### What landed

**`SpecBmap.v` (+~230): the arm vocabulary and `wp_bmap_gen_body`.**  The
arm a caller can *read off the block map* is one boolean —

```coq
Definition bmap_ai  (bm bm' : blkmap)             : bool  (* indirect alloc'd *)
Definition bmap_ad  (bm bm' : blkmap) (fbn : nat) : bool  (* data alloc'd     *)
Definition bmap_alloced bm bm' fbn := (bmap_ai bm bm' || bmap_ad bm bm' fbn)%bool
Definition bmap_ind (fbn : nat) : bool := bool_decide (NDIRECT <= fbn)%nat

Definition bmap_cost (cr al ind : bool) : nat :=
  (if al then (if cr then 1 else 2) + (if ind then 1 else 0) else 0)%nat
Definition bmap_need (cr ind : bool) : nat :=
  (if ind then (if cr then 3 else 4) else 2)%nat
```

`bmap_cost <= 3`, `bmap_need <= 4` (both machine-checked).  The post is
five clauses: the spend `n <= n' + bmap_cost cr (bmap_alloced bm bm' fbn)
(bmap_ind fbn)`, `n' <= n`, `Sb ⊆ Sb'`, the ceiling `Sb' ⊆ Sb ∪
{[bmapstart]} ∪ {[ind']} ∪ {[dblk']}`, and the two memberships that ARE the
absorption: any allocation puts `bmapstart` in the set (so the next call
may present `cr := true`), and a freshly allocated data block is in the set
(so the caller's own `log_write` of it absorbs).

**Why ONE boolean and not a constant.**  Charging the maximum on the
direct-hit arm busts MAXOPBLOCKS for a four-block chunk — the arm that
allocates nothing must cost nothing.  Charging per *four-way disjunction*
(§18's option (B) read literally) is not needed either: the SET outcomes
collapse to four but the COST collapses to one function of `al` and `ind`,
because `ai -> ind` makes "a second unit was spent" equal `al && ind`.
That is the whole reason bmap's contract stayed one line of arithmetic.

**`ProofBmap.v` (+~350/-90): the set threaded through `bm_kit`.**  Four
interior lemmas (`bm_epilogue`, `bm_release`, `bm_indirect_tail`,
`wp_bmap_gen`), six ledger-discharge sites, three balloc calls, one
log_write call, and both seals.  `wp_bmap_sconf`'s STATEMENT IS UNCHANGED
and is now DERIVED from the core at `cr := false` — see the deviation
below for why not at `Sb := ∅`.  `BMAP_NOALLOC` and `ProofReadi` did not
move at all.

**`WriteiBudget.v` (+~150): link 3's loop algebra, proven.**  Section 10:
`bm_pot bms S := if decide (bms ∈ S) then 0 else 1`, the two invariant
clauses `wi_inv_bud` / `wi_inv_spent`, and the five lemmas that are the
whole `ProofWritei` retrofit — `wi_inv_enter`, `wi_bmap_need_ok`,
`wi_bmap_cost_le`, `wi_step_noalloc`, `wi_step_alloc`, `wi_inv_bud_pos`,
`wi_inv_exit`, and `wi_inv_enter_maxop` (entering at MAXOPBLOCKS covers
every chunk filewrite can ask for, four-block ones included).

### The deviations from the brief, and why

1. **`ba_cred` as a record field is UNIMPLEMENTABLE for this contract.**
   The brief's shape — `∃ Sb, ⌜ba_cred a ⊆ Sb⌝ ∗ log_opS …`, the `ba_used`
   invariant-index trick — carries only a LOWER bound on the current set.
   That is exactly right for `used` (a caller wants `used ⊆ used'` and
   nothing else) and exactly wrong here: writei's data-block absorption
   needs `dblk ∈ Sb'`, which the ENTRY index cannot mention, and §18
   clause 1 also demands an upper bound on `Sb' ∖ Sb`, which no
   lower-bounded existential can express.  `Sb` therefore rides as an
   EXPLICIT parameter of `bm_kit`, beside `n`, in the same in/out
   positions.  The feared binder cost did not materialise: only four
   interior lemmas mention the kit, and all four already carried `n`.
2. **`wp_bmap_sconf` is derived at the `log_op` WITNESS, not at `Sb := ∅`.**
   `log_op γ n` *is* `∃ Sb, log_opS γ n Sb`, so the counted seal destructs
   it and runs the core at whatever set the existential was hiding, with
   `cr := false`.  Deriving at `∅` would have required every counted caller
   to prove its set empty, which is false and unnecessary.  This is
   strictly stronger than the brief's `Sb := ∅` and costs nothing.
3. **bmap carries a SECOND, INTERNAL credit.**  `bm_indirect_tail` takes
   `cri` — "the indirect block is already in the op's set" — because on the
   arm where bmap allocates the indirect block itself, its own `log_write`
   at +0xb0 must absorb against balloc's bzero of that very block, or the
   arm costs 4 and `bmap_cost` is wrong.  `cri` is a `Local Lemma`
   parameter and never crosses the seal, so §18's "one credit at the seam"
   is intact.  The public contract has exactly one, the bitmap.

### FINDING: the set CEILING is decorative, and §18 should know it

§18 clause 1 requires an explicit bound on `Sb' ∖ Sb`, and link 2 supplies
one.  But **no proof obligation anywhere consumes it**, and none can: a
ceiling is a statement that a block is NOT in the set, and the only thing
callers ever do with the set is claim credits, which are MEMBERSHIPS.
Budget soundness is carried entirely by the counter — `log_spend_step`
already refuses to grow `Sb` without spending a unit — so the ceiling adds
no soundness.  It cost link 2 one extra hypothesis on `bm_indirect_tail`
(`bm_ledger_ok`'s own ceiling admits the ZERO entry the allocating arm is
standing on, so the tail needs a data-block-free ceiling of its own).
**Recommendation for link 3 and for create's S5 brief:** keep the ceiling
where it is free, but do NOT let it drive the shape of writei's loop
invariant — if it forces a block-set monotonicity lemma over the
loop-carried `blkmap`, drop it and state the memberships only.

### TRAP (new, and it cost this stage an hour): `set_solver` IS QUADRATIC
### IN THE PROOF CONTEXT, AND AN IRIS GOAL HAS A HUGE ONE

`set_solver` runs `set_unfold` over the WHOLE hypothesis context.  In
`ProofBmap`'s interior — several hundred hypotheses of proofmode state,
register-threading facts and mword equalities — a single call did not
terminate in fifteen minutes; the file compiles in 90 seconds without one.
Every set obligation in this retrofit is one of a dozen shapes
(`x ∈ A ∪ {[x]} ∪ C`, `A ⊆ A ∪ B ∪ C`, …), so they are proved ONCE as
named lemmas at the top of `ProofBmap` where the context is three
variables, and applied by name.  **Never write `set_solver` inside a
function-proof lemma in this tree.**  Corollary trap: the failure looks
exactly like a hang, and a `coqc` launched over `ssh` without `nohup` dies
with the connection, so the log stops mid-tactic and reads like a crash —
launch mirror builds detached.

### The remaining trap that bit: `uint` needs its mword ascription

`{[uint (bm_ind bmI)]}` does not typecheck — `bm_ind` returns `bv 32` and
`uint` wants `mword 32`.  The file's own older lines all write
`uint (bm_ind bmI : mword 32)`; new ones must too.

### Gate (link 2)

Mirror `full.sh` **`EXIT=0`, 1037 `.vo`, zero `Error`**, on top of
`8ceaf829`.  `WriteiBudget.v` green (`one.sh`).  `Print Assumptions` on
`Bmap.wp_bmap_sconf` / `Bmap.wp_bmap_gen` /
`BmapNoalloc.wp_bmap_noalloc_sconf` / `Balloc.*` / `Readi.wp_readi_sconf` /
`Writei.wp_writei_sconf` / `Dirlink.wp_dirlink_sconf`: unchanged.

### NOT STARTED: links 3 and 4

`SpecWritei` / `ProofWritei` / `ProofDirlink` are UNTOUCHED — the tree is
green with link 2 in it and links 3–4 out.  The shape is settled and the
arithmetic is machine-checked; what remains is mechanical:

1. `SpecWritei`: move `wi_cost_bmonly` up from `WriteiBudget` (which
   imports `SpecWritei`, so it cannot stay there), swap the sconf body's
   two `wi_cost` occurrences for it, and add `wp_writei_gen_body` taking
   `log_opS γ ncount Sb` and returning `log_opS γ n' Sb'` with `Sb ⊆ Sb'`.
   **writei needs NO credit parameter of its own** — `wi_inv_enter` holds
   at any entry set, because the potential is what absorbs the unknown.
2. `ProofWritei`: the loop's five numeric premises
   (`6*W+1 <= nI`, `ncount <= nI + 6*(B-W)`, …) become
   `wi_inv_bud` + `wi_inv_spent` + `nI <= ncount` + `Sb ⊆ SbI`; the bmap
   call becomes `BM.wp_bmap_gen` at `cr := bool_decide (ba_bms A ∈ SbI)`;
   the two `log_write`s become `LW.wp_log_write_gen` at
   `cr := bool_decide (uint blk ∈ Sb2)`; the five budget `lia`s become
   `wi_step_noalloc` / `wi_step_alloc` / `wi_inv_exit`.
3. `ProofDirlink`: one call site, `wi_blocks = 1`, so the premise is
   `wi_cost_bmonly = 4` against whatever it holds today.  **AUDIT ITS
   EMPTY-RANGE ARM** — `wi_cost_bmonly 0 0 = 2` against `wi_cost 0 0 = 1`,
   so the non-monotonicity trap is live here exactly as recorded above.

## S3m — LINKS 3+4 LANDED: writei's contract is `wi_cost_bmonly`, the whole
## budget retrofit is CLOSED.  `ProofFilewrite` NOT STARTED

### What landed

**`SpecWritei.v` (+~250): `wi_cost_bmonly` moved up, and the SET form.**
`wi_cost_bmonly off n = 2 * wi_blocks off n + 2` now lives beside `wi_cost`
(the loose 6-per-block bound it replaces), because `WriteiBudget` *requires*
`SpecWritei` and the public contract is stated on it.  The sconf body's two
`wi_cost` occurrences — the premise and the spend-at-most postcondition —
are swapped for it.  `wp_writei_gen_body` is the set form: `log_opS γ ncount
Sb` in, `log_opS γ n' Sb'` out, plus `Sb ⊆ Sb'`.  The numbers that matter:

```
wi_cost        1023 FW_MAX = 25   (busts MAXOPBLOCKS = 10)
wi_cost_bmonly 1023 FW_MAX = 10   (EXACTLY MAXOPBLOCKS, zero slack)
wi_cost_bmonly (16*k) 16    =  4   (dirlink's call site; was 7)
```

**`ProofWritei.v` (+~490/-100): the loop carries the ledger invariant.**
`wi_cont`, `wi_ret`, `wi_join`, `wi_size` and `wi_loop` all take the op's set
as a parameter; `wi_loop`'s loop-carried state gains `SI` beside `nI`.  The
five numeric premises became `wi_inv_bud` + `nI <= ncount` + `wi_inv_spent` +
`W <= B` + `Sb ⊆ SI`.  The bmap call is `BM.wp_bmap_gen` at
`cr := bool_decide (ba_bms A ∈ SI)`; both `log_write`s are
`LW.wp_log_write_gen` at `cr := bool_decide (uint (blkmap_get bm2 fbn) ∈ Sb2)`.
`wp_writei_gen` is the core and `wp_writei_sconf` is derived from it at the
`log_op` existential's own witness — **its STATEMENT IS UNCHANGED** apart from
the cost function, so no caller but dirlink moved.

**`ProofDirlink.v` (+~36): one call site, and the empty-range audit.**
`dl_wi_blocks k : wi_blocks (16*k) 16 = 1` is factored out of the old
`dl_wi_cost`, and `dl_wi_cost_bmonly k = 4` is read off it.  `dirlink_units`
**STAYS AT 7**: it is a constant that must dominate both writei's cost and
iput's 3, nothing forwards writei's cost through dirlink's contract, and
lowering it would ripple into every caller for no gain.  The spend
postcondition now holds *a fortiori* (4 <= 7).

**`WriteiBudget.v` (+~87): the two iteration bounds and the arm lemma.**
`wi_iter_alloc_bound` / `wi_iter_noalloc_bound` compose bmap's arm-wise cost
with log_write's absorption into exactly the hypotheses `wi_step_alloc` /
`wi_step_noalloc` want; `wi_ad_of_alloced` is the block-map fact that makes
the allocating arm affordable (see surprise 2).

### SURPRISE 1 (and the one real shape change): iupdate had to go SET FORM

`wp_writei_gen` promises `Sb ⊆ Sb'`, and **iupdate runs on every returning
path of writei, including the `n = 0` one.**  Against iupdate's counted
contract (`log_op γ (S u)` in, `log_op γ u` out) the set coming out is an
unrelated existential, so monotonicity past the flush is simply unprovable.
This is the one clause of §18's ruling that could not be met inside the four
files S3j sized.

The fix is small and strictly stronger than a bare existential: iupdate is
straight-line and logs exactly one block, so its set growth is
**DETERMINATE** —

```coq
log_opS γ (S u) Sb  -∗ … -∗  log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})
```

`SpecIupdate.v` gains `wp_iupdate_gen_body` + the `IUPDATE` parameter (+152,
pure insertion — the sconf body is untouched); `ProofIupdate.v` threads the
set through `iu_cont`/`iu_tail` and derives the counted seal (+95).  It
compiled clean first try, because `ProofIupdate` was *already* destructing
`log_op` to `log_opS` internally to reach `wp_log_write_au` — the retrofit
only stopped it from throwing the set away again.  **The three consumers
(Itrunc, Iput, Writei) take `IUPDATE` and did not move.**

### SURPRISE 2: the allocating arm needs a BLOCK-MAP fact, not arithmetic

`wi_step_alloc` allows `2 + bm_pot` for the whole iteration.  The arm
`al = true, ind = true` costs bmap 3 (bitmap 2 uncredited + one indirect
write), leaving **nothing** for writei's own `log_write` — so that arm only
closes if the log_write ABSORBS, i.e. if bmap allocated the DATA block too.
It always did, and the reason is `InodeInv.blkmap_wf_ind_nz` read backwards:
`bmap_ai` says the indirect BLOCK was 0 on the way in, and `blkmap_wf`'s "no
indirect block ⇒ no entries" conjunct then makes the indirect ENTRY 0 as
well, so on the success arm `bmap_ad` holds.  That is `wi_ad_of_alloced`.

The `ind = false` arm needs no absorption at all — bmap costs at most
`1 + bm_pot` there, leaving exactly one unit for the log_write.  Both facts
are packed into `wi_iter_alloc_bound`, whose one non-arithmetic hypothesis is
`al = true -> ind = true -> crlw = true`.

### SURPRISE 3: `destruct … eqn:` SUBSTITUTES, so the arm facts change shape

`destruct (bmap_alloced bmI bm2 fbn) eqn:Hal` rewrites the scrutinee to the
literal `true`/`false` **in every hypothesis**, so bmap's `Hbc5 : bmap_alloced
… = true -> bmapstart ∈ Sb'` becomes `true = true -> …` and must be applied to
`eq_refl`, NOT to `Hal` (whose statement keeps the original left-hand side).
Likewise `wi_bmap_cost_le` must be named at the literal `true`, and the
`rewrite Hal in Hbc1` that would have normalised the no-alloc arm is a no-op —
use `assert (bmap_cost cr false ind = 0) by reflexivity` instead.

### SURPRISE 4: `S W - 1` is NOT unified with `W`

The two step lemmas conclude at `W - 1`; applied at `S W` that is `S W - 1`,
which is *convertible* to `W` but which `refine`'s unifier does not reduce.
Every use needs `pose proof … as H; replace (S W - 1)%nat with W in H by lia`
rather than a direct `refine` against a goal stated at `W`.

### SURPRISE 5: `destruct (bool_decide _)` silently does not fire

`by (rewrite HnLdef; destruct (bool_decide _); lia)` fails with `lia`'s
"Cannot find witness", because the wildcard leaves the `Decision` instance
unresolved and nothing is destructed — `lia` then sees an opaque
`if b then S uX else uX`.  **Use stdpp's `case_bool_decide`.**  The failure
names `lia` and hides the real cause, which cost this stage a cycle.

### TRAP CHECK: the empty-range arm, audited

`wi_cost_bmonly 0 0 = 2` against `wi_cost 0 0 = 1`, so the new premise is
STRICTLY HARDER on an empty range and no consumer may be waved through.

- **writei's own `n = 0` path**: reached with the premise in hand; the arm
  needs only `ncount <> 0`, and `unfold wi_cost_bmonly in Hcost; lia` gives it.
- **dirlink**: has NO empty-range arm.  Its single writei call is at the
  literal `n = 16` — one directory entry — on both the middle-slot and the
  append arm, so `wi_blocks` is 1 and never 0.  The trap does not fire.

### The set CEILING is still decorative, and writei does not offer one

S3l's finding held: §18 clause 1's bound on `Sb' ∖ Sb` would have to name
every data block the loop touched — a set-valued function of the loop-carried
`blkmap`, exactly the shape S3l recommended against.  writei promises
`Sb ⊆ Sb'` and nothing more.  Budget soundness is carried by the counter
alone (`log_spend_step` already refuses to grow `Sb` without spending).
iupdate, by contrast, gives its growth EXACTLY, because it is one block.

### Gate (links 3+4)

Mirror `full.sh` **`EXIT=0`, 1037 `.vo`, zero `Error`**, on top of `ff3c9d9f`
(the same 1037 as link 2 — this stage adds no files).  `lemma_diff --ref HEAD`
reports exactly three things, all justified: the two new `Parameter`s
(`wp_writei_gen`, `wp_iupdate_gen`) are MODULE-TYPE OBLIGATIONS, supplied by
`ProofWritei.wp_writei_gen` / `ProofIupdate.wp_iupdate_gen` under the
`: WRITEI` / `: IUPDATE` ascriptions — not axioms; and the one `GONE`
(`WriteiBudget.wi_cost_bmonly`) is the MOVE up into `SpecWritei` that S3l
itself prescribed.  No `Admitted`, no new `Axiom`.

**`Print Assumptions` NOT CAPTURED — the one gate item this stage owes.**
The audit file (`Writei.wp_writei_sconf` / `wp_writei_gen`,
`Dirlink.wp_dirlink_sconf`, `Iupdate.wp_iupdate_sconf` / `wp_iupdate_gen`,
`Bmap.*`, `Balloc.wp_balloc_sconf`, `Readi.wp_readi_sconf`) was written and
launched twice and did not finish inside the stage's window — the cost is
loading the Link cone, not the printing.  It is a CONFIRMATORY check here
rather than a load-bearing one: `full.sh` is green at `EXIT=0` / 1037 `.vo`
/ zero `Error`, `lemma_diff` is clean, and the two new module parameters are
discharged by the `: WRITEI` / `: IUPDATE` ascriptions, which is exactly what
would make a new axiom impossible.  **Whoever picks up S3n should run it
first** — the expectation is UNCHANGED from S3l for every listed name, since
no proof in this stage introduces a hypothesis that is not discharged from an
existing lemma.

### NOT STARTED: `ProofFilewrite` + `LinkFilewrite`

Untouched.  Everything S3g–S3l staged for it is intact, and link 3 has now
removed the blocker: a four-block chunk costs `wi_cost_bmonly = 10 =
MAXOPBLOCKS`, which is exactly what `begin_op` hands each iteration, so
**every chunk filewrite can ask for is payable**.  Note for whoever picks it
up: filewrite does NOT need `wp_writei_gen` — each iteration is its own
begin_op/end_op, so the set resets per chunk and the COUNTED
`wp_writei_sconf` at `ncount := MAXOPBLOCKS` suffices, with the premise
discharged by `WriteiBudget.wi_cost_bmonly_fits`.  The gen form is for
create's S5 op-wide set (§18 clause 1), and it is now real rather than
aspirational.

## S3n — S3m's OWED AUDIT IS IN AND CLEAN; the five things that could have
## blocked filewrite are all REFUTED; `ProofFilewrite`'s preamble lands, the
## walk does NOT

### Step 0 — the `Print Assumptions` audit S3m owed: **NOTHING MOVED**

Run detached on the mirror (`nohup` — an ssh-tethered `coqc` dies with the
connection and reads like a crash), one scratch file over the eleven names,
`coqc` exit 0, scratch deleted.  **All eleven cones are exactly the five
`rv64d` platform axioms + `functional_extensionality_dep`**:
`Writei.wp_writei_sconf`, `Writei.wp_writei_gen`, `Iupdate.wp_iupdate_sconf`,
`Dirlink.wp_dirlink_sconf`, `Bmap.wp_bmap_sconf`, `Balloc.wp_balloc_sconf`,
`Readi.wp_readi_sconf`, `Ilock.wp_ilock_sconf`, `Iput.wp_iput_sconf`,
`Namex.wp_namex_sconf`; `Fileread.wp_fileread_sconf` is the same set plus its
known named `LinkConsoleread.Consoleread.wp_consoleread_sconf` and nothing
else.  S3m's expectation is confirmed: the set-form retrofit introduced no
assumption, exactly as the `: WRITEI` / `: IUPDATE` ascriptions predicted.

**Cost note for whoever runs it again:** ~1.3 min per name, ~15 min total,
and it is the CONE LOAD that costs, not the printing — S3m's two failures
were window-length, not a tooling problem.  `pgrep coqc` finds nothing while
it runs: the process is **`rocqworker`**, which is why S3m's progress checks
looked like crashes.

### The five pre-walk checks — the sixth blocker that ISN'T

Done BEFORE any of the walk, on S3i's trap-2 principle (a numeric obligation
wants arithmetic, not reading).  All five hold; each is now machine-checked
in `ProofFilewrite.v` rather than asserted:

1. **The stack constants close, and `filewrite_stack` is EXACTLY TIGHT on
   writei.**  `filewrite_stack = 12 + K_writei = 82`; every call is made
   inside the frame, so each callee needs `<= K - 12 = 70`: writei 70
   (EQUALITY, no slack), pipewrite 64, consolewrite 62, end_op 58, ilock 44,
   begin_op 26, iunlock 26.  `SpecFilewrite`'s header claim holds.
   (`fw_av_*`.)
2. **The budget premise is UNIFORM IN `off`.**  S3m's headline is
   `wi_cost_bmonly 1023 FW_MAX = 10`; what the loop needs is that bound at
   EVERY offset, since `f->off` is not block-aligned.
   `WriteiBudget.wi_cost_bmonly_fits` is already stated that way — its only
   hypothesis is `n <= FW_MAX`, `off` universally quantified, because
   `wi_blocks_le4` bounds `off mod BSIZE` rather than `off`.  Every chunk
   filewrite can ask for is payable.  (`fw_budget_ok`.)
3. **The share algebra composes.**  SpecIlock v5 consumes
   `inode_shr_gen k s dev inum g` and returns `ic_deposit cn k
   (DepShr s dev inum g)` + `ity_shot g (di_type dn)`; SpecIunlock takes the
   deposit and returns the arity-preserving `inode_shr k s dev inum`.
   Lending `s/2` leaves `inode_shr_gen k (s/2) .. g` in hand and gets
   `inode_shr k (s/2) ..` back — exactly `fw_shr_regen`'s two arguments —
   and `Qp.div_2` rejoins at `s`.  (`fw_qp_halves`.)
4. **writei's two unobvious resource premises are both available.**
   `p_pid pj` is NOT in `filewrite_fs_env` and need not be: filewrite writes
   from USER memory (`c.li s8,1` at +0x50), so it holds `proc_priv` and
   `ProcInv.proc_priv_pid` splits the quarter out, as SpecWritei's own
   comment at that premise says.  `dinode_at gi inum dn0` is not in the
   environment either — it arrives inside ilock's `ic_loaded` payload
   (fileread destructs it as `Hdnat`, ProofFileread.v:1741).
5. **end_op accepts a PARTIALLY SPENT reservation.**  `SpecEndOp` takes
   `log_op g u` for ANY `u` (:30, :142), so no iteration has to prove it
   spent its whole `begin_op` grant; writei promises spend-at-most and the
   remainder is carried straight into end_op.

### THE SURPRISE: there are TWO constants named `FW_MAX`, at two TYPES

`SpecFilewrite.FW_MAX : Z` (the chunk size as the `lui`/`addi` pairs at
+0x42..+0x4e materialise it) and `WriteiBudget.FW_MAX : nat` (the same 3072
as every budget lemma's hypothesis) are DIFFERENT CONSTANTS, and
`ProofFilewrite` must `Require Import` BOTH — so whichever comes second
shadows the other.  Every occurrence in `ProofFilewrite.v` is written
QUALIFIED, and `fw_max_bridge : Z.of_nat WriteiBudget.FW_MAX =
SpecFilewrite.FW_MAX` is the one place they meet.  An unqualified `FW_MAX`
in the walk typechecks in some goals and fails in others with a `nat`-vs-`Z`
mismatch that reads like a coercion problem.

### What landed: `ProofFilewrite.v`, THE ARITHMETIC PREAMBLE ONLY

~240 lines, compiles clean, `_CoqProject` row added (1038 `.vo`).  It carries
the WIP/resume header, the five findings above, and the pure `nat`/`Z`/`Qp`
obligations the walk consumes at its call sites — hoisted above the module
for the same reason `ProofFileread.v` hoists `fr_av_*`: a `lia` cannot run at
a call site, where the context holds a register file.  Contents: `fw_K12`,
`fw_av_writei/pipe/cons/ilock/iunlock/begin_op/end_op`, `fw_K_back`,
`fw_max_bridge`, `fw_budget_ok`, `fw_budget_ok_empty` (S3m's empty-range trap
check, re-audited at the call site: it fits with eight to spare),
`fw_chunk_rem`/`fw_chunk_cap`/`fw_chunk_lt31` (the two arms of the
`bge s7,a5` chunk test at +0xd2), `fw_i_advance` (the fuel step),
`fw_i_lt31`, `fw_off_lt31`, `fw_qp_halves`, `fw_ret_of_tail` (fw_tail's
disjunction into `filewrite_ret`), `fw_ret_of_dev`, `fw_zero_trip`.

**`wp_filewrite_sconf` and the `FilewriteProof` functor are NOT WRITTEN, so
`LinkFilewrite.v` does not exist and file.c STAYS 6/7.  S4 is NOT
unblocked.**  The walk is ~2500 lines of instruction-wise Iris —
`ProofFileread.v`'s single lemma is 2139 lines for FOUR arms and NO loop, and
filewrite adds a bottom-tested loop with a nine-component invariant — which
did not fit this stage's window alongside the audit.  The resume point is
spelled out in the file's header.

### Gate

Mirror `full.sh` **`EXIT=0`, 1038 `.vo`, zero `Error`** on top of `441c398e`.
`tools/lemma_diff.py --ref HEAD`: *"1 file(s) checked -- CLEAN (nothing
dropped, nothing admitted, no new assumption)"* — no new seal, since
`SpecFilewrite` already exists and the file adds only lemmas.  No `Admitted`,
no `Axiom`, no `cheat_`.  md5s equal on both sides: `ProofFilewrite.v`
`b38a6d7d0cc8eb28cb9a7ade8fc0bfd4`, `_CoqProject`
`f3e7affd32d753625e10b1ee1e219a8f` (patched IN PLACE on the mirror with
`sed`, never scp'd).  Audit scratch deleted; no scratch left on the mirror.

### Traps recorded

1. **`one.sh`'s trailing `EXIT=0` IS A FALSE GREEN.**  The script echoes it
   unconditionally after the loop; the real status is the
   `DONE <file> = <rc>` line.  A first attempt here printed
   `DONE ProofFilewrite.v = 1` and `EXIT=0` together, and a `grep EXIT`
   check would have landed a file that does not compile.
2. **`Require Import A` does NOT re-export A's own imports.**
   `ProofFilewrite` imports `SpecFilewrite`, which imports `InodeInv`, and
   `MAXFILE` was still *"not found in the current environment"* — the
   dependency is LOADED but not IN SCOPE.  Import the defining file
   (`InodeInv`, `FsCrash`) directly.
3. **The mirror's Rocq worker is `rocqworker`, not `coqc`.**  Every
   `pgrep -af coqc` progress check reports nothing while a compile is
   running, which reads as a dead job.

## S3o -- STOPPED AND REPORTED: the SIXTH blocker is real, and `SpecReadi.v`
## already named it.  `SpecWritei`'s USER ARM IS UNCALLABLE

**`ProofFilewrite.v`'s walk was not started.**  The stop is at ONE premise of
ONE call -- writei's, at `+0xa0` -- and it is not a discovery: it is the item
`claude-notes/design/file-table.md` files under **"OWED: `SpecWritei.v`
cannot be called on its user arm"**, whose last line reads *"`filewrite` is
the function that will hit this, and it should be done BEFORE that proof is
started rather than during it."*  S3o is that hit.

### What S3n's clearance (4) got wrong

S3n cleared the writei call by reading **SpecWritei's own comment at the
premise** -- *"On the user arm this is `proc_priv`'s own quarter
(`ProcInv.proc_priv_pid`)"* (SpecWritei.v:501).  That comment is the stale
one.  `SpecReadi.v`:255-263 is the correction, written when fileread became
readi's first caller, and it says so in terms:

> An earlier version of this contract asked for both at once, with a comment
> claiming `proc_priv_pid` supplied the quarter alongside the block.  It does
> not, and the user arm was uncallable; fileread, its first caller, is what
> found it.  **`SpecWritei.v` still has the same shape.**

**The rule this stage adds to the trap list: when a spec's premise is
justified by a COMMENT rather than by a lemma, the comment is evidence about
the author's belief, not about the resource algebra.  Clear it against the
accessor's STATEMENT.**  `ProcInv.proc_priv_pid` (:892) is
`proc_priv -* p_pid |->4{1/4} * (p_pid |->4{1/4} -* proc_priv)` -- a borrow,
in the type.  Two seconds of reading the signature refutes the comment; S3n
read the comment.

### The precise goal

filewrite's writei call passes `a1 = 1` (`c.li s8,1` at `+0x50`,
`c.mv a1,s8` at `+0x9a`), so writei's `eq_vec (m !!! Ra1) zero_reg = negb
user` forces **`user = true`**.  On that arm `wp_writei_sconf_body`
(SpecWritei.v:497-502) demands, as two separate premises of the same call,

```coq
  (if user then proc_priv gf pj pidv V else <the caller's byte buffer>) -*
  p_pid pj |->4{dq} pidv -*
```

and the walk holds exactly one of the two: `wp_filewrite_sconf_body` hands it
`proc_priv gf pj pidv V`, and `filewrite_fs_env` contains no `p_pid` cell at
any fraction.  The residual obligation is

```coq
  proc_priv gf (proc_addr j) pidv V
    |- proc_priv gf (proc_addr j) pidv V * exists dq, p_pid (proc_addr j) |->4{dq} pidv
```

which is **false, not merely unproven**.  The cell totals one:
`ProcInv.proc_priv_core` holds a half (:665) and `SchedCtx.proc_pub` the
other behind `p->lock`.  There is no third fragment, so a `proc_priv` holder
produces the fraction only by giving `proc_priv` up.  Widening
`SpecFilewrite` instead is not an escape -- sys_write is in the same position
one frame up, and `SpecFilewrite` is frozen.

### What is NOT blocked -- the rest of the walk was cleared BY HAND

S3o re-checked every other premise of every other call against what the walk
holds at that instruction.  **This is the only unsatisfiable one.**

- **The other four loop callees are clear, and clear for a REASON**:
  `SpecBeginOp`, `SpecIlock`, `SpecIunlock` and `SpecEndOp` each take the
  bare `p_pid pj |->4{dq} pidv` at a universally quantified `dq` and want no
  `proc_priv` at all, so the accessor serves them exactly as it serves
  fileread's ilock/iunlock (lend before the `jal`, close the wand the
  instant it returns -- ProofFileread.v:1685 / :1712).  **The defect is
  precisely "wants both at once", and writei is the only callee that does.**
- **writei's eighteen numeric/pure premises all close.**  (2) is
  `fw_budget_ok`; (13) is `SpecFilewrite.fw_chunk_joint`; (14) is
  `fw_size_lt31`; (8)(9)(10)(11)(12) are conjuncts 3, 4, 1, 6, 2 of the
  `InodeLock.inode_ok` ilock hands out inside `ic_loaded`; (3)-(7), (15),
  (16) are `filewrite_fs_env`'s own pure fields; the register premises are
  the decode.
- **Every writei RESOURCE except the pid pair is in hand**: `i_dev`/`i_inum`
  at 1/2 and `inode_meta`/`inode_map`/`inode_blocks`/`dinode_at` out of
  ilock's `ic_loaded` (at `dn0 := dn`), the three superblock cells +
  `bitmap_res` + `ireg_inv` + `bslots _ 3` out of the environment,
  `log_op g MAXOPBLOCKS` out of begin_op, `kalloc_env`/`proc_priv` out of the
  contract.
- **The re-park closes**, and its two assemblies are now machine-checked and
  landed: `fw_inode_ok_rebuild` builds `InodeLock.inode_ok` from writei's
  post verbatim (conjuncts 5 and 7 are S3i's two preservations, whose
  antecedents are the SAME conjuncts of the `inode_ok` that came in), and
  `fw_dir_ok_wi` makes `DirView.dir_ok` vacuous.
- **iunlock's `ity_shot g (di_type dn')` is ilock's own witness unchanged**,
  because `fw_wi_type` says writei never moves `di_type` (definitional in
  `wi_dinode`).
- **`bslots` composes**: the environment's three split for ilock's one by
  `fw_bslots3` and rejoin.
- S3n's five clearances (stack constants, budget-uniform-in-`off`, the `s/2`
  share algebra, `dinode_at` inside `ic_loaded`, end_op's partial spend) all
  stand; only the `p_pid` half of clearance 4 falls.

### The repair (S3p) -- sized, not done

`SpecReadi.v`:264-267 is the landed template: put the pid fraction in the
KERNEL arm only, precondition AND postcondition, in **both**
`wp_writei_sconf_body` and `wp_writei_gen_body`; then inside `ProofWritei.v`
carry `p_pid |->4{1/4} * (p_pid |->4{1/4} -* proc_priv ...)` in place of
`proc_priv * p_pid`, applying the wand before each `either_copyin` and
re-splitting after.  Blast radius, counted on the file:

| site | what moves |
|---|---|
| `SpecWritei.v` `wp_writei_sconf_body` / `wp_writei_gen_body` | the pair, pre and post -- 4 places |
| `ProofWritei.wi_cont` :339/:348, `wi_ret` :430/:439, `wi_join` :810/:820, `wi_size` :1129/:1139, `wi_loop` :1745/:1755 | 5 in-file premise pairs |
| `ProofWritei.wp_writei_gen` :3429, `wp_writei_sconf` :4390 | the two public lemmas |
| `ProofWritei` :2463, :2539, :3642 | the three `either_copyin` bundling sites -- where the wand-apply / re-split goes |
| `ProofWritei` -- 34 `Hppid` occurrences | threading |
| `ProofDirlink.v` :2042 | the ONE downstream consumer; `user = false`, so it only re-brackets its two arguments into the arm's pair |

Nothing above writei changes, because the new premise is strictly WEAKER.
`file-table.md`'s OWED note becomes DONE.  The reason it was deferred there --
*"`SpecWritei.v` and `ProofWritei.v` are mid-flight for the `balloc` contract
ripple"* -- **expired at S3m**, which landed that ripple.

### What LANDED (green, gated)

`iris/ProofFilewrite.v` only, still the preamble, now carrying:

- the S3o banner: the blocker, the precise goal, why it is false rather than
  open, the repair with its blast radius, and the resume point retargeted to
  **S3q**;
- **S3o's LEAF TABLE** -- the whole walk, instruction by instruction, with the
  `wp_*_s_sconf` leaf named for each of the ~60 instructions and **every
  branch displacement evaluated rather than copied** from S3g's graph.  Three
  are compressed-vs-full traps (`c.addw` at `+0xae` vs `addw` at `+0xc4`;
  `c.lui`/`lui`; the COMPRESSED `ADDIW` at `+0x82` -> `wp_caddiw_s_sconf`) and
  one, `+0xd8`, is a 21-bit field that is NEGATIVE (`2*2005 = 4010`, bit 11
  set -> `-86`) and reads as a forward jump if the sign extension is skipped;
- **the loop shape, settled**: `ProofWritei.wi_loop`'s -- a `Local Lemma` with
  a `wi_cont`-style packaged continuation and `revert CID0; induction W`, at
  fuel `n - i`.  NOT ireclaim's hart-closed wand: the back edge at `+0xc8`
  re-enters at `+0xcc` with a different `i`, so the invariant must be
  universally quantified over the loop-carried values, which is what the
  forall-fuel shape gives and a persistent-tail does not.  `fw_tail` IS that
  persistent tail and is already proved;
- seventeen new machine-checked lemmas the walk consumes: `fw_maxfile_bsize`,
  `fw_n_range`, `fw_size_lt31`, `fw_uint_moi`, `fw_major_range`,
  `fw_bltu9_false`, `fw_bltu9_true`, `fw_ret_pc_cons`, `fw_upd_upt_id`,
  `fw_ret_of_pipe`, `fw_zext8_zero`, `fw_wbool_of_fall`,
  `fw_inode_ok_rebuild`, `fw_wi_type`, `fw_dir_ok_wi`, `fw_dir_ok_same`,
  `fw_bslots3`.

`LinkFilewrite.v` is NOT written.  **file.c stays 6/7 and S4 stays blocked.**

### Gate

Mirror `one.sh ProofFilewrite.v`: **`DONE ProofFilewrite.v = 0`** (the
`DONE` line, not the trailing `EXIT=0` -- S3n's trap 1).  `full.sh` `EXIT=0`,
**1038 `.vo`** (no file added or removed).  `tools/lemma_diff.py --ref HEAD`:
*"1 file(s) checked -- CLEAN (nothing dropped, nothing admitted, no new
assumption)"*.  No `Admitted` / `Axiom` / `cheat_` / `admit` in the file.
`Print Assumptions` NOT run: `wp_filewrite_sconf` does not exist, and every
other cone is untouched (one leaf file changed, nothing depends on it).
md5 verified equal on both sides after every scp; `_CoqProject` NOT touched
(`ProofFilewrite.v`'s row landed at S3n).  Mirror `git status`: that one file
modified, nothing else; no scratch left.

### Traps recorded

1. **A PREMISE JUSTIFIED BY A COMMENT IS NOT CLEARED.**  S3n's pre-walk
   clearance read SpecWritei's prose and passed it; the accessor's TYPE
   refutes it in one line.  When a stage's job is "prove the blockers are
   gone", the evidence has to be a signature, a lemma or a `vm_compute` --
   never the callee author's sentence about what the caller can do.  The
   corollary S3o adds to file-table.md's own lesson (*"a spec's premise set
   is only validated by its first caller"*): **and a comment about the
   premise set is validated by nothing at all.**
2. **`uint` is not where three plausible imports put it.**  The Sail `uint`
   the `bltu` range facts are stated over lives in
   `SailStdpp.Operators_mwords`.  `Require Import SailStdpp.Values` does not
   reach it, `Require Import Riscv.riscv_extras` does not reach it, and
   `Import Defs` -- which `SpecFilewrite.v`:170 does -- does not reach it
   either; all three were tried, in that order, at one mirror round-trip
   each.  Copy `ProofFileread.v`'s whole four-line SailStdpp block.
3. **`wp_lh_s_sconf` is not in the `WpSconf*` four.**  It is in
   `WpSmodeHalf.v`, which `ProofFilewriteParts.v` does not import; the
   FD_DEVICE arm's `lh a5,36(a0)` at `+0x5c` needs the walk to require it
   directly, as `ProofFileread.v` does.
4. **`until grep -q "^EXIT=" /tmp/one.log` races the script's own `rm -f`.**
   Launching `one.sh` with `nohup ... &` and immediately polling reads the
   PREVIOUS run's log -- complete with its `EXIT=` -- and reports the previous
   run's result as this one's.  `rm -f /tmp/one.log` from the LAUNCHING shell
   before the `nohup`, not only inside the script.

## S3p — THE WRITEI PID REPAIR IS IN AND FULL-GATED.  The walk was NOT
## started, and nothing is owed in front of it

### What landed

The OWED item from `design/file-table.md`, applied exactly as
`SpecReadi.v`:244-267 does it.

**`iris/SpecWritei.v` — 4 places.** The pid fraction folds into the `if user`
bracket's KERNEL arm, in the precondition and the postcondition of BOTH
`wp_writei_sconf_body` and `wp_writei_gen_body`:

```coq
  (if user
   then proc_priv γf pj pidv V
   else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ src_bytes i) ∗
        p_pid pj ↦₄{dq} pidv) -∗
```

and the standalone `p_pid pj ↦₄{dq} pidv -∗` premise is gone from all four.
The stale comment that S3n read as authority is replaced by readi's, with the
history in it.

**`iris/ProofWritei.v`.** One new definition and one new lemma, in
`WriteiDefs` next to `wi_cont`:

```coq
  Definition wi_q (user : bool) (dq : dfrac) : dfrac :=
    if user then DfracOwn (1/4) else dq.

  Lemma wi_src_pid … : <the bracket> -∗
    p_pid (proc_addr j) ↦₄{wi_q user dq} pidv ∗
    (p_pid (proc_addr j) ↦₄{wi_q user dq} pidv -∗ <the bracket>).
```

Then: the 5 in-file premise pairs (`wi_cont`, `wi_ret`, `wi_join`, `wi_size`,
`wi_loop`) re-bracketed, the two public lemmas following `SpecWritei`
automatically, four borrow/close pairs (bmap and bread in `wi_loop`'s head,
the two brelses in its two arms, iupdate in `wi_join`) with `wi_q user dq`
passed as the callee's dfrac, the two `either_copyin` bundling `iAssert`s
grown, and the `Hppid` threads dropped everywhere else.

**`iris/ProofDirlink.v`:2042** — `user = false`, one `iCombine` before the
call and one `iDestruct` after.

**`iris/ProofFilewrite.v`** — the S3o banner rewritten to "repaired", plus
`fw_writei_src` — a `⊣⊢`, so one lemma is both what the walk must supply
at `+0xa0` and what it gets back at `+0xa4`.

### THE SIZING WAS RIGHT ABOUT THE SHAPE AND WRONG ABOUT THE COST — DOWNWARD

S3o sized this as "carry `p_pid ↦₄{1/4} ∗ (p_pid ↦₄{1/4} -∗ proc_priv …)` in
place of `proc_priv ∗ p_pid`, applying the wand before each `either_copyin`
and re-splitting after", i.e. a `user`-dependent carrier threaded through the
whole file.  **That is not what it takes.**  The observation that collapses it:

> **Every callee that wants the fraction quantifies its `dq`.**  bmap, bread,
> brelse and iupdate all take `p_pid pj ↦₄{dq} pidv` at an arbitrary dfrac,
> so ONE accessor at a `user`-indexed dfrac (`wi_q`) serves both arms and
> **no call site case-splits on `user` at all**.

So the borrow is not carried; it is opened immediately before each of the four
calls and closed the instant each returns, and in between the file carries the
bracket under its existing name.  `wi_ret` and `wi_size` — which only ever
threaded the fraction — lost a hypothesis and gained nothing.

`ProofWritei.v` compiled on the FIRST attempt after the edit, and so did
`ProofDirlink.v`.  There was no seventh blocker.

### The two `either_copyin` bundling sites, which are the only real work

`either_copyin` takes `proc_priv` and never the fraction, so the borrow must
be CLOSED across the copy — and the two `iAssert`s that split the source
around it are stated per-arm, so both had to grow the fraction into their
kernel arm rather than case-split on it:

* the pre-split (`Hsrcw` / `Hsrcrest`) parks `p_pid … ↦₄{dq}` in `Hsrcrest`'s
  `else` branch, alongside the head and tail of the buffer that
  `ProofWriteiParts.wi_split3` peels off;
* the post-normalisation (`Hnorm`) puts it back, with one `iSplitR "Hppid"`
  in front of the existing `wi_join3`.

On the user arm both are `True` / the whole block, untouched.

### The dirlink consumer: `iCombine`, not an `iAssert`

`ProofDirlink` builds readi's kernel-arm bracket by hand at :2659 with an
explicit `iAssert` naming the bigop.  For writei the cheaper form works and
is shape-independent:

```coq
        iCombine "Hsrc Hppid" as "Hsrc".      (* before the call *)
        …
        iDestruct "Hsrc" as "[Hsrc Hppid]".   (* after it *)
```

`iCombine` produces the plain `∗` (no `CombineSepAs` instance fires between a
bigop and a `p_pid` pointsto), and `IntoSep` sees through `if false then _
else (_ ∗ _)` by iota, so neither direction needs the bigop written out.
**Worth copying**: it means a kernel-arm consumer of one of these brackets
does not have to know the buffer's exact printed form.

### Gate

* `ProofWriteiParts.v`, `WriteiBudget.v`, `ProofWritei.v`, `ProofDirlink.v`,
  `ProofFilewrite.v`: each `DONE … = 0` (the `DONE` line, not the trailing
  `EXIT=0` — S3n's trap 1).
* `full.sh` `EXIT=0`, **1038 `.vo`** (no file added or removed).
* `Print Assumptions` via the mirror's `audit.sh`:
  `Writei.wp_writei_sconf`, `Writei.wp_writei_gen` and
  `Dirlink.wp_dirlink_sconf` are each **exactly the six names S3n recorded**
  — `rv64d.valid_reservation`, `rv64d.plat_term_write`,
  `rv64d.match_reservation`, `rv64d.load_reservation`,
  `rv64d.cancel_reservation`, `FunctionalExtensionality.functional_
  extensionality_dep`.  Nothing added, nothing dropped: the new premise is
  strictly weaker, so nothing above writei moved.
* `tools/lemma_diff.py --ref HEAD`: CLEAN.  No `Admitted` / `Axiom` /
  `cheat_` / `admit`.
* md5 verified equal on both sides after every scp; `_CoqProject` NOT touched.

### OWED, and deliberately not done here: ONE stale sentence in `SpecReadi.v`

`iris/SpecReadi.v`:260-263 still reads

> *"[SpecWritei.v] still has the same shape -- see
> claude-notes/design/file-table.md."*

which **is now false**, and this stage's own trap 1 (S3o's) says a stale
comment is exactly how the next reader gets misled.  It is not fixed here for
one reason: `SpecReadi.v` is at the bottom of the readi cone, so a
comment-only edit re-digests `SpecReadi.vo` and forces a rebuild of
`ProofReadi`, `ProofFileread`, `ProofDirlookup`, `ProofDirlink`, `ProofNamei`
and everything above them — a whole-tree round trip for a sentence, with the
risk of parking RED if it does not finish.  Park-green wins.

**The replacement text, so it costs the next stage nothing** (any stage that
rebuilds that cone for its own reasons should just apply it):

```
     (An earlier version of this contract asked for both at once, with a
     comment claiming [proc_priv_pid] supplied the quarter alongside the
     block.  It does not, and the user arm was uncallable; fileread, its
     first caller, is what found it.  [SpecWritei.v] HAD THE SAME DEFECT and
     was repaired the same way at fs-sysfile S3p, when filewrite -- its own
     first user-arm caller -- hit it; both are now this shape.  See
     claude-notes/design/file-table.md.) *)
```

### WHAT WAS NOT DONE: the walk

`wp_filewrite_sconf`, `FilewriteProof` and `LinkFilewrite.v` are **not
written**.  file.c stays 6/7 and S4 stays blocked.  This stage spent its
budget on Part 1 and on the mirror round-trips it needed; the walk is
~2500 lines of instruction-wise Iris over a 118-instruction function with a
bottom-tested loop, and starting it without finishing it would have parked
red.  Everything S3o staged for it is intact and now unobstructed.

### Traps recorded

1. **A `.vo` REBUILT BY `one.sh` IS NOT A REBUILT CONE, and the failure reads
   like a proof error.**  Changing `SpecWritei.v` staled
   `ProofWriteiParts.vo`, `WriteiBudget.vo` and `SpecFilewrite.vo`; `one.sh`
   compiles the named files in the named order and nothing else, so the first
   three attempts died on *"Compiled library X makes inconsistent assumptions
   over library SpecWritei"* — once per stale prerequisite, one mirror
   round-trip each.  Use `make -f CoqMakefile <target>.vo -j24` for anything
   downstream of a changed Spec; `one.sh` is only safe for a leaf.  (A
   `mk.sh` doing exactly that now sits next to `one.sh` on the mirror.)
2. **`one.sh`'s trailing `EXIT=0` is FALSE GREEN — confirmed again, three
   times in this stage.**  It is the script's own exit, not `coqc`'s.  Read
   the `DONE <file> = N` line.  (S3n's trap 1, and it will keep biting
   because the false line is the LAST one in the log.)
3. **A `Definition` next to the premise it abbreviates is not always the
   right move.**  `ProofReadi` names its bracket `rd_dst`; writei's is left
   INLINE, matching `SpecWritei`'s statement literally, and only the borrow
   is named.  The proofmode cost is the same (the bracket is two conjuncts,
   not a continuation), and keeping the public lemmas' statements
   syntactically identical to the spec body's is worth more than the
   abbreviation.
4. **durable-notes' "a class that is not IMPORTED becomes a fresh VARIABLE,
   silently" — HIT AGAIN, and the documented tell is exact.**
   `ProofFilewrite.v` does not `Require Import WpLock`, so
   ``Context `{!riscvGS Σ, !lockG Σ, …}`` did not fail: it *invented* a
   section variable `lockG`, and `proc_priv`'s real `WpLock.lockG` instance
   then had nothing to resolve against.  That left the statement's `Σ`
   unresolved and with it EVERY other instance in the lemma — eleven
   `UNDEFINED EVARS` over `riscvGS`, `fileG`, `fdslotG`, `mem_pointsto` and
   `big_opL`'s `Monoid`, not one of which names the real problem.  The tell
   the durable note gives is the one that identifies it: **the printed local
   context contains BOTH `lockG` and `lockG0`**, and the evar goal is
   spelled QUALIFIED (`WpLock.lockG ?Σ`) where the binder is not.
   *What this stage adds:* the note offers `Require Import`/`Require Export`
   as the fix; **qualifying the binder in place (``!WpLock.lockG Σ``) is
   better when the file is not yours to re-import**, because a new import
   also silently re-resolves every other unqualified name in the file — and
   this file's header already warns that an unqualified `FW_MAX` typechecks
   in some goals and fails in others.
5. **`ProcInv` does not `Export` `ProcGeom`, and `ProcPtOwn` does not
   `Export` `UserPtTree`.**  So a file that has `proc_priv` in scope from
   `Require Import ProcInv` still has neither `proc_addr` nor `p_pid`, and
   one with `upd_upt` still has no `uptd`.  Three separate round-trips in
   this stage, one per name.  Same family as S3o's trap 2 (`uint` lives in
   `SailStdpp.Operators_mwords`): **in this tree, having the operation does
   not mean having its argument type.**

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
- **S3d** (agent) **— PARTIAL**: §17' piece (A) — the restated ledger and
  the arm-resident ½, plus `ic_dep`'s generation field, `ic_payload`'s
  generation parameter and SpecIlock/SpecIunlock v4 — LANDED and
  full-gated (1032 `.vo`, eight cones unchanged).  Piece (B), the
  one-shot's parking, STOPPED-AND-REPORTED: §16.4's claim box makes
  ilock's fill complete on the MARKER branch, so the pending cannot live
  on the allocated disjunct alone, and iput's in-generation re-park
  forbids it on the marker disjunct — design/fs-icache.md §17.5 has the
  counterexample, the dead escapes and three candidate repairs.
  filewrite is still blocked and still unspecified.
- **S3f** (agent) **— PARTIAL**: §17.6 BUILT WHOLE and full-gated (the
  icache half + `inode_pay`); `SpecFilewrite.v` FROZEN and compiling;
  `ProofFilewrite` / `LinkFilewrite` / `SpecConsolewrite` /
  `LinkConsolewrite` parked green for S3g.  file.c stays 6/7.
- **S3g** (agent) **— PARTIAL**: `SpecConsolewrite` + `LinkConsolewrite`
  (the assumed device contract, one named Axiom) and
  `ProofFilewriteParts.v` (the 96-byte frame, the arithmetic, SEVEN block
  lemmas incl. the WHOLE panic arm, and the share-generation algebra)
  LANDED and full-gated (1036 `.vo`).  The complete decode graph, the
  frame map, a FIFTH decode correction (the hoisted `n <= 0` test at
  +0x32) and the `SpecIunlock`-loses-the-generation finding with its
  in-Parts repair are recorded in the S3g section.
  `ProofFilewrite` / `LinkFilewrite` parked green.  file.c stays 6/7.
- **S3h** (agent) **— STOPPED AND REPORTED**: the FD_INODE arm cannot
  rebuild `IcacheEscrow.ic_loaded`, because `InodeLock.inode_ok` has seven
  conjuncts and `SpecWritei`'s postcondition re-establishes five — the size
  cap (`di_size dn' <= MAXFILE*BSIZE`, weakened to `< 2^31`) and
  `inode_sized data'` are both missing, and neither is recoverable at the
  call site.  filewrite is the first re-parker of a CHANGED payload; the
  S3h section has the table, the two impossibility arguments and the
  two-clause repair to `SpecWritei` (ripple: ProofWritei's `wi_loop` plus
  three ProofDirlink sites; premise counts unchanged).  `SpecFilewrite`
  stays FROZEN and correct.  `ProofFilewriteParts.fw_tail` (the whole
  +0xf4-to-epilogue join, all three arriving paths) LANDED and full-gated.
  `ProofFilewrite` / `LinkFilewrite` still unwritten; file.c stays 6/7.
- **S3i** (agent) **— PARTIAL**: the `SpecWritei` repair LANDED and
  full-gated, but as PRESERVATIONS (`di_size dn <= cap -> di_size dn' <= cap`
  and `inode_sized data -> inode_sized data'`) — S3h's unconditional form is
  UNPROVABLE on the -1 arm and on the writing arm alike, and the implication
  is what keeps the ruling's zero premise ripple.  `ProofFilewrite` STOPPED
  AND REPORTED on a SECOND blocker, the LOG BUDGET: `begin_op` pays
  MAXOPBLOCKS = 10 and writei's `wi_cost` for the code's chunk is 13..25, so
  the FD_INODE loop cannot discharge writei's budget premise for any chunk
  that spans more than one block.  The S3i section has the machine-checked
  table, why dirlink and readi never saw it, and the three-part sizing of a
  repair (arm-aware bmap budget; log_write absorption via `LogInv.log_opS`;
  and a kernel question — a four-block chunk may exceed MAXOPBLOCKS
  outright).  file.c stays 6/7.
- **S3j** (agent) **— PARTIAL**: **the budget ruling is IN, and it is
  "xv6 is sound".**  S3i's possible-kernel-defect arm is REFUTED: every
  fs.c contract already carries `bitmap_geom_ok`'s `0 < size <= BPB`, so
  there is exactly ONE bitmap block and the honest per-distinct-block cost
  of a B-block chunk is `B + 3 <= 7`, not `2B + 3 = 11`, against
  MAXOPBLOCKS = 10.  Nothing was added to `kernel-defects.md`.  The
  ABSORPTION SEAM landed as `WriteiBudget.v` (additive, zero ripple,
  1037 `.vo`): the tight cost `wi_cost_tight = wi_blocks + 3` with
  `wi_cost_tight_fits`, the machine-checked multiset bound, machine-checked
  refutations of both weaker accountings S3i sized (19 and 11, both bust),
  and `log_amort` — `SpecItrunc.bm_paid` generalised from one amortised
  block to a SET, with the idempotent `log_amort_present` and the
  `log_amort_adopt` that lets writei's loop reserve an indirect block whose
  identity balloc has not yet returned.  Chosen on `LogInv.log_opS`; the
  counted-form alternative is IMPOSSIBLE (`log_op` forgets the set, so
  there is nothing for an absorb lemma to be about).  The four-file
  retrofit (`SpecBalloc` → `SpecBmap`/`ProofBmap` → `SpecWritei`/
  `ProofWritei` → `ProofDirlink`) is sized bottom-up in the S3j section and
  NOT STARTED — each link is a stage-sized job on a 3000–4100-line proof.
  `ProofFilewrite` / `LinkFilewrite` still unwritten; file.c stays 6/7.
- **S3k** (agent): the retrofit, bottom-up per the S3j sizing, then
  `ProofFilewrite` + `LinkFilewrite` on S3g's seven blocks + `fw_tail`.
  Then file.c is 7/7 and S4's three shells unblock.
- **S3l** (agent) **— PARTIAL**: **link 2 LANDED and full-gated** — `SpecBmap`
  grows `wp_bmap_gen_body` (set-form, ONE credit, arm-wise exact cost as a
  function of one observable boolean) and `ProofBmap` threads `Sb` explicitly
  through `bm_kit`; `wp_bmap_sconf`'s statement is unchanged and DERIVED, and
  `BMAP_NOALLOC`/`ProofReadi` did not move.  Link 3's loop algebra
  (`bm_pot`, `wi_inv_bud`/`wi_inv_spent` and the five step lemmas) landed
  PROVEN in `WriteiBudget` section 10.  **Links 3 and 4 NOT STARTED** —
  `SpecWritei`/`ProofWritei`/`ProofDirlink` untouched, tree green with link 2
  in it.  Two shape deviations from the §18 brief (the `ba_cred` record field
  cannot express the growth writei needs; the set CEILING is decorative and
  should not drive link 3's invariant) and a new cross-cutting trap
  (`set_solver` does not terminate inside this tree's function proofs) are in
  the S3l section.  file.c stays 6/7.
- **S3b** (agent) **— PARTIAL**: filestat PROVEN AND LINKED (file.c 6/7);
  §17's fd-type witness STOPPED-AND-REPORTED as unimplementable in the ruled
  shape — design/fs-icache.md §17.1 has the finding and the repair (§17′) to
  rule on. filewrite is still blocked and still unspecified.
- **S3n** (agent) **— PARTIAL**: S3m's owed `Print Assumptions` audit is IN
  and **CLEAN — all eleven cones unmoved** (five platform axioms + funext;
  Fileread + its known named `Consoleread` Axiom).  The five things that
  could have made filewrite a SIXTH blocker are all refuted and now
  machine-checked (stack constants close with writei EXACTLY tight; the
  budget premise is uniform in `off`; the s/2 share algebra composes;
  writei's `p_pid`/`dinode_at` both reachable; end_op takes a partly spent
  reservation).  `ProofFilewrite.v` lands as the ARITHMETIC PREAMBLE ONLY
  (1038 `.vo`, lemma_diff clean) with a WIP/resume header; the ~2500-line
  walk and `LinkFilewrite` are NOT written, so **file.c stays 6/7 and S4
  stays blocked**.  New surprise: two constants named `FW_MAX` at two types
  (`SpecFilewrite`'s `Z`, `WriteiBudget`'s `nat`) which this file must import
  together — qualify every occurrence.
- **S3o** (agent) **— STOPPED AND REPORTED**: the SIXTH blocker is real and
  was already on file.  **`SpecWritei`'s user arm is uncallable** — it wants
  `proc_priv` AND a `p_pid` fraction on the same call, `ProcInv.proc_priv_pid`
  is a borrow, and the cell has no third fragment; filewrite's writei call is
  `user = true` (`c.li s8,1` at `+0x50`).  `SpecReadi.v`:255-263 and
  design/file-table.md's "OWED" section had both named it and named filewrite
  as the function that would hit it.  S3n's clearance (4) was read off
  SpecWritei's stale COMMENT rather than off the accessor's type.  Everything
  else in the walk was cleared by hand and is clear.  `ProofFilewrite.v` lands
  green with the S3o banner, the instruction-by-instruction LEAF TABLE (every
  displacement re-evaluated; four decode traps), the settled forall-fuel loop
  shape, and seventeen new lemmas including the re-park's two assemblies
  (`fw_inode_ok_rebuild`, `fw_dir_ok_wi`).  1038 `.vo`, lemma_diff clean.
  **file.c stays 6/7 and S4 stays blocked.**
- **S3p** (agent) **— PARTIAL**: **THE REPAIR IS IN, AND BLOCKER SIX IS
  GONE.**  `SpecWritei` now carries `SpecReadi`'s shape verbatim (the pid
  fraction inside the `if user` bracket's KERNEL arm, pre and post, both
  bodies); `ProofWritei` borrows it back with ONE lemma, `wi_src_pid`, over a
  `wi_q user dq` dfrac — no call site case-splits on `user`, because every
  fraction-taking callee already quantified its `dq`.  `ProofDirlink`
  (`user = false`) `iCombine`s its two arguments across the call.  Full-gated,
  1038 `.vo`, `Print Assumptions` on Writei and Dirlink byte-identical,
  lemma_diff clean.  `ProofFilewrite.v`'s banner is rewritten to "repaired",
  and `fw_writei_src` is the discharge of the stopping premise — a `⊣⊢`,
  machine-checked at the `user = true` the decode forces and stated with the
  `if` UNREDUCED so the bracket cannot drift again unnoticed.
  **THE WALK ITSELF WAS NOT STARTED** — see S3q.  file.c stays 6/7.
- **S3q** (agent) **— PARTIAL, PARKED GREEN AT THE LOOP TEST**: the walk is
  written.  `iris/ProofFilewrite.v` now carries `FilewriteProof
  (Pipewrite)(Ilock)(Writei)(Iunlock)(BeginOp)(EndOp)(Consolewrite) :
  FILEWRITE` and `wp_filewrite_sconf` is proved instruction by instruction
  for **every path except the FD_INODE loop BODY**, under exactly ONE
  banered `Axiom cheat_` whose single `exact (cheat_ _)` sits at **+0xcc,
  the bottom loop test**.  Proved outright: the pre-prologue `f->writable`
  test and its frame-free -1 return at +0x122; `fw_pro`; the three-way type
  dispatch; **FD_PIPE in full**; **FD_DEVICE in full, all four paths**
  (out-of-range major, null slot, the `c.jalr` into consolewrite, the join);
  the ELSE arm (`fw_panic`); and FD_INODE's entry — the s4 spill at +0x30,
  the hoisted `n<=0` test, the **whole zero-trip path** through `fw_tail`
  and `fw_epi`, plus the five late spills, both `lui`/`addi` 3072 pairs,
  `i:=0`, `user:=1` and the `c.j` to the test.  `lemma_diff --ref HEAD`
  reports exactly `NEWAXIOM Axiom cheat_` and nothing else.
  **`LinkFilewrite.v` is DELIBERATELY ABSENT** (park-green protocol: no
  parked walk may be consumed outside its own file), so **file.c stays 6/7
  and S4 stays blocked.**  `_CoqProject` untouched — it already carried
  `ProofFilewrite.v`.
  FIVE MECHANICAL TRAPS, all recorded for the resumer:
  1. **Four typeclasses are not where the preamble puts them.**  The
     functor's `Context` needs `diskGhostG` / `uartGhostG` / `fsLogG` /
     `iregG`, which live in `DiskPtsto` / `WpUart` / `FsBlocks` /
     `InodeRegion` and are re-exported by NONE of `ProofFilewrite.v`'s
     original imports.  Without them Rocq invents four fresh section
     variables and the body fails with *"Could not find an instance for
     ?diskGhostG0"* and three more — an error that names no file.  Same
     shape as the `lockG`/`lockG0` tell, one tier up.
  2. `dev_major` / `NDEV_max` are **`SpecFileread`'s**; `SpecFilewrite`
     states `filewrite_dev_env`'s guard with them but does not re-export
     them, so the device arm's four `Local Lemma`s cannot even be typed
     without `Require Import SpecFileread`.
  3. **`neq_vec`'s arguments are the two mwords, not an `eq_vec`.**  A BNE
     leaf's premise is `neq_vec _ _ = _`, and `rewrite Hcmp` with an
     `eq_vec` equation has nothing to match: it fails *"does not match any
     subterm"*.  `unfold neq_vec` first works for the rewrite but then the
     follow-up `rewrite Hp` fails.  The fix is fileread's, and the reason
     `ProofFilereadParts.fr_ty_neqz` exists: carry BOTH an `eq_vec` and a
     `neq_vec` comparison hypothesis, and use `rewrite Hncmp; unfold
     neq_vec; first [rewrite Hp | idtac]; reflexivity`.
  4. `destruct (Z.geb 0 n) eqn:Hz0` **rewrites the already-asserted
     `zopz0zKzJ_s`-vs-`Z.geb` bridge hypothesis too**, so that hypothesis
     IS the branch leaf's premise; a `rewrite Hbge0; exact Hz0` leaves
     `true = true` and fails on the type.  `exact Hbge0`.
  5. `Z.geb_gt` does not exist.
  The walk's own imports are placed **after** the seventeen preamble lemmas
  on purpose (a `Require Import` re-resolves every unqualified name below
  it — the file's own `FW_MAX` warning generalised), which is why
  `fw_writei_src`'s context says `WpLock.lockG` and the functor's says
  `lockG`.
- **S3r** (agent): close the frontier — the `∀`-fuel loop lemma at `n - i`
  (`ProofWritei.wi_loop`'s shape one level up) whose body is
  begin_op → ilock at `s/2` → the re-park → writei → the `f->off` update →
  iunlock → end_op → break/continue, joining through `fw_rest5` into
  `fw_tail`; then delete `cheat_` and write `LinkFilewrite.v`.  The state
  the loop is handed is spelled out in the FRONTIER banner in
  `ProofFilewrite.v`.  Then file.c is 7/7 and S4's three shells unblock.
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
