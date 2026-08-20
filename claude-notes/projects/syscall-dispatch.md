# syscall-dispatch — folding the 22 table entries into syscall()

Opened 2026-08-20, the day `completed/fs-sysfile.md` closed at file.c 7/7 and
sysfile.c 16/16. That campaign proved the ENTRIES; this one proves the
DISPATCHER, and its acceptance criterion is one line: `LinkSyscall.v`'s
`Axiom wp_syscall_sconf` is replaced by an instantiation of
`ProofSyscall.SyscallProof`, and `sysc_arm_placeholder` — the tree's only
`Admitted` — is gone.

`ProofSyscall.v`'s own header is the authoritative status (which entries are
wired, what blocks each of the rest); re-read it against the `decide`
branches in `sysc_arm_dispatch` rather than trusting any prose. This file is
the ledger of what each increment cost and the standing account of the
debts, so a later lane can pick one up without re-deriving why it is a debt.

## INCREMENT 1 (2026-08-20): syscall()'s environment becomes `fs_ready`

The sixteen sys_* functions were all proven and linked before this
increment; what was missing was the DISPATCHER, and what was missing from
the dispatcher was a statable environment. `ProofSyscall.v`'s own header is
now the record of where each entry stands — read that first. This section
is the campaign's ledger and the three debts, so a later lane can pick one
up without re-deriving why it is a debt.

### What landed

1. **`FsCfg.fscfg` grew three fields** (`fsc_bmapstart`, `fsc_size`,
   `fsc_ninodes`) and one more (`fsc_kpages`, the free-list count/seal
   PAIR). The last one matters for a reason worth remembering:
   `KvmSpec.kalloc_env` hides the pair behind an existential, and
   `SpecFileclose.fileclose_pipe_env` NAMES it (pipeclose gives a page
   back, so it must speak about the count). A caller that names the pair
   can never tie its own name to a hidden one — the unreachable-witness
   shape again, one level down. So `fs_ready` carries the "kmem" lock and
   the sealed count SPELLED OUT and recovers `kalloc_env` as a projection.

2. **`FsReady.fs_ready` grew the two halves it was missing** — §0
   `fs_geom_ok` (eleven fields: the nineteen pure premises every fs syscall
   used to state, minus the four that were ties to `icfg` and are now
   `reflexivity`, minus the four that are `bitmap_geom_ok`'s own conjuncts
   and are reached through it) and §0b `fs_sb_cells` (the four superblock
   words at `DfracDiscarded`). The cells are the interesting half: every fs
   contract in the tree takes them at a threaded fraction and every one of
   them only READS — `readsb` fills `sb` once inside fsinit and nothing
   writes it again — so the fraction was an accounting cost with no
   corresponding permission, forced through every contract, bundle and
   continuation on the way. `word4_pointsto_persist` at the end of fsinit
   retires it, and `DfracDiscarded` instantiates every existing contract's
   `dq` unchanged.

3. **`fscfg` became a `fileG` field**, beside `icfg`. The alternative was
   adding `{FSC : fscfg}` to sixteen files' worth of `Module Type`
   parameters and `Definition` signatures — the interface sweep
   `completed/explicit-cpuid.md` is about, whose failure mode is a contract
   that compiles while meaning something else. Neither record is capacity
   (they are per-boot VALUES, no camera), so a double path can only
   disagree about a value, and resolution picks one instance per use site.
   `FsReady.v`, `FsSyscalls.v` and `FirstTok.v` dropped their explicit
   `FSC` binders in exchange.

4. **`ProofSyscall.syscall_env` is `fs_ready` plus twenty-eight equations.**
   `sysc_ties` is the equation record; `sysc_fs_env_all` applies it once and
   hands back the OLD twenty-five-conjunct shape, which is what kept the
   arms that predate the change from moving (one token per destruct site).
   Two latent defects died with the old shape: `kalloc_env γa None` at a
   fresh existential BESIDE `sysc_fs_env`'s `is_lock (fcn_kmem fn) ...` was
   claiming two lock handles at two unrelated gnames for the ONE lock at
   `KernelSyms.kmem`, and the same for `printk_env`.

5. **Six new arms**: fstat (8), chdir (9), unlink (18), link (19), close
   (21), sync (22). Sixteen of 22 entries are wired.

6. **`SpecSysClose.v`'s pid fraction was a real defect, and it is fixed.**
   See the durable note; the fix is `fileclose_fs_env_nopid` plus
   `ProcInv.proc_priv_pid_ofile` / `SpecFileclose.fileclose_loop_open`, and
   it cost ~15 lines in a 936-line proof because the lending pair already
   existed for kexit's descriptor loop.

### The three debts, and what each is worth

**(A) The reference ledger does not close — blocks open (15), mkdir (20),
mknod (17).** `wp_syscall_sconf_body` must give `iref_slots IREFSPARE` back
because `UsertrapRes.ut_own` carries it at the literal `IREFSPARE` and
`SpecUserretClosed`'s trap loop gets its residue back UNCHANGED. So no
weakening of the syscall contract helps — a one-unit leak per `open` breaks
the Löb invariant, full stop.
* mkdir/mknod: the fact is TRUE and only the statement is weak
  (`SpecCreate.v`:101 — "the `iunlockput` returns the second, so
  `ns' = ns`"), but only on create's SUCCESS arm; the failure arm is where
  create's post gives the bare interval. Tightening is create's job.
  ESTIMATE: contained to `SpecCreate.v` + `ProofCreate.v`'s fail tail.
* open: the unit is genuinely spent for good — the success arm PARKS the
  reference in `f->ip`. `IREFSLOTS` already provisions NFILE units for
  exactly this; what is missing is a HOLDER those units can sit in that
  `sys_open` can reach. `FileInv.fslot`'s `None` (free-slot) arm is the
  natural one — `filealloc` hands the unit out with the fresh `file_ref`,
  `fileclose`'s last close puts one back — but `fslot`'s `Some (q,n)` arm
  cannot see the file's TYPE, and only an inode-typed file has spent its
  unit. That is the "wants per-`ofile` ghost state" item in
  `projects/fs-icache.md`, "Deferred / owed", and it is what has to land
  first. Do NOT try to fund it from `ofile_slot` instead: units-per-
  descriptor and units-per-file disagree the moment `filedup` runs.

**(B) A contract whose pid fraction exceeds what exists — blocks pipe (4).**
Same defect `sys_close` had (durable note below). `SpecSysPipe.v` takes
`proc_priv` AND `fileclose_fs_env`, i.e. three quarters of `p->pid`. The
edit is the same one; it is bigger only because four of
`ProofSysPipe.v`'s own block lemmas thread the bundle in their STATEMENTS
(`:624`, `:639`, `:1126`, `:2264`), and the quarter has to be in hand at
each of the three fileclose call sites. `Hpriv` is live at all of them.

**(C) Premises about unchecked user input — blocks read (5), write (16).**
`sys_read` takes `0 <= sys_rw_count v2` and
`MAXFILE*BSIZE + sys_rw_count v2 < 2^31`; `sys_write` the first. No
dispatcher can supply either — `argint` reads a trapframe word and the C
checks nothing.
* The MAXFILE half is a weakening `SpecFileread.v`'s own header says can be
  relaxed to `n < 2^31` ("mechanical: three uses in ProofFileread.v"), and
  `sys_rw_count_lt` gives `< 2^31` unconditionally. Cheap.
* `0 <= n` is readi's overflow arm. xv6's `off + n < off` test at
  readi+0x026 is DEAD BY PREMISE today (`SpecReadi.v`'s COVERAGE NOTE); a
  negative count arrives as a huge `uint` and fires it. The shape of the
  fix, worked out but not landed: give `rd_clamp` a first case
  (`0` when `2^32 <= off + n`, which is EXACTLY when the C's test fires, so
  the postcondition keeps its two arms and gains no third), drop the joint
  premise, prove the taken branch at +0x026, and give every readi caller a
  "the sum does not wrap" side condition dischargeable from its own bound.
  piperead and consoleread are already total in a non-positive count (their
  loops do not run); filewrite's chunking answers -1.
