(* ProofSyscall.v -- the real proof of syscall(), replacing LinkSyscall.v's
   whole-function axiom.

   STATUS (read this before extending, and re-verify against the actual
   `Admitted`/`Qed` sites rather than trusting this note): the whole
   dispatch is `Qed`-sealed -- prologue, `myproc()`, the `p->trapframe->a7`
   read, the fused range check, the 22-entry jump-table read, the `c.jalr`,
   the shared return tail (`sysc_ret_tail`), the epilogue
   (`sysc_epilogue_tail`) AND the whole unknown-syscall printk fallback
   (`sysc_fallback`, +0x40..+0x56).

   TWENTY of the 22 table entries are WIRED to real, `Qed`'d arms calling
   their own whole-function contracts: 1 fork, 2 exit, 3 wait, 4 pipe,
   6 kill, 7 exec, 8 fstat, 9 chdir, 10 dup, 11 getpid, 12 sbrk, 13 pause,
   14 uptime, 15 open, 17 mknod, 18 unlink, 19 link, 20 mkdir, 21 close,
   22 sync.
   Count the `decide` branches in `sysc_arm_dispatch`, not this list.

   ALL 22 ENTRIES ARE WIRED, and `sysc_arm_placeholder` is GONE with them:
   `sysc_arm_dispatch`'s fall-through is now `exfalso; lia` against its own
   `1 <= k <= 22`, which is why the 22 `decide` branches each name their
   disequality instead of dropping it with `_`.  That retired the tree's
   only `Admitted`.

   Read (5) and write (16) were last, and what unblocked them was not the
   dispatch: it was `31f115a` making `0 <= n` a fact of the code (so neither
   contract asks its caller for anything about the count) and
   `ConsoleInv.console_inv` giving the devsw column an owner.

   15 open came in once its iref ledger became an EQUALITY.  Its contract
   used to promise only `ns - sys_open_slots <= ns' <= ns`, and this
   dispatch lends [IREFSPARE] and must get [IREFSPARE] back, so no
   instantiation could close -- the arm was unwireable for arithmetic, not
   for want of a resource.  The interval was an artefact of dropping the
   untyped table entry's own unit when the slot was opened; publishing a
   file releases it in exchange for the inode reference it parks, so
   sys_open spends nothing.  See [SpecSysOpen]'s post.

   ==== THE ENVIRONMENT IS [FsReady.fs_ready] NOW, AND THAT CLOSED THE
        WHOLE "GENUINELY MISSING RESOURCES" CATEGORY ====================

   `syscall_env` used to be `sysc_proc_env` plus twenty-five conjuncts of
   file-system fabric spelled at `fn`'s own field names, PLUS a
   `kalloc_env`/`printk_env` pair at fresh existentials.  It is now

       syscall_env γf pj bn fn  =  sysc_proc_env γf ∗ sysc_fs_env pj bn fn
       sysc_fs_env pj bn fn     =  ⌜sysc_ties pj bn fn⌝ ∗ procs_inv (fcn_procs fn)
                                   ∗ disk_geom (fcn_disk fn) (fcn_pd fn) …
                                   ∗ is_lock (fcn_dlock fn) … (disk_res …)
                                   ∗ FsReady.fs_ready

   -- twenty-three EQUATIONS saying the caller's threaded `bn`/`fn` name the
   ambient file system, the disk fabric at `fn`'s three virtio ring pages,
   and the one predicate that says the file system is ready to operate.
   (The three ring pages were equations too, until `fs-cfg-boot.md` R1 took
   `fsc_desc`/`fsc_avail`/`fsc_used` out of `FsCfg.fscfg`: `virtio_disk_init`
   `kalloc`s them at WP time, so the boot-era fupd that builds the record
   cannot know them.  `fs_ready` quantifies them and the pair of resources
   above is what an equation against a field used to buy -- see
   `sysc_ties`' note.  Interderivable, so nothing below moved.  Two more
   equations left later, for a different reason: `sct_dqb`/`sct_dqs` named
   `fclose_names` fields that the bitmap-invariant sweep deleted, the
   superblock cells now being DISCARDED for good and every contract that
   reads one taking it at a generic `dq` this dispatch fills in with
   `DfracDiscarded`.)  Three consequences, and they are the reason six
   entries could be wired in one increment:

   (1) THE UNREACHABLE-WITNESS PROBLEM IS GONE BY CONSTRUCTION.  There is
       exactly one file system per boot ([FsCfg.fscfg]), so a bundle at the
       ambient names and one at `fn`'s are the same bundle modulo the ties;
       nothing has to be existentially guessed.  `sysc_fs_env_all` applies
       the ties once, for the whole bundle, and hands the old
       twenty-four-conjunct shape back -- which is why the arms that predate
       this change did not move.  The ONE row it does not hand back is the
       icache's: `SpecFileclose` retired `fileclose_ic_env` (fileclose takes
       `⌜fclose_ties fn⌝` and `fs_ready` instead), and rather than keep a
       copy of a deleted definition, the fifteen conjuncts are DERIVED from
       the bundle's own `fs_ready` by `sysc_ic_env_of_ready` -- one lemma
       application per arm, in the old body's order, so the arms' inner
       destruct patterns are still verbatim.
   (2) FOUR ROWS THAT COULD NOT BE STATED AT ALL BEFORE now come for free:
       `sb_ninodes` and `sb_size` (there is no `fclose_names` field for the
       inode count, so the old closer bundle never carried them),
       `bitmap_geom_ok`,
       the `16*nib <= 2^16` mkfs tie, and the printk credential PAIR.  They
       are the create-family entries' own premises, and they come off
       [FsReady.fs_geom_ok] / [FsReady.fs_sb_cells].
   (3) IT HAS A PRODUCER.  `syscall_env` was, in its own words, a Definition
       nobody constructs; `fs_ready` has [FsReady.fs_ready_establish].  The
       boot wiring still owes the call, but the obligation is now a named
       lemma rather than an open question.

   ==== WHAT BLOCKS THE REMAINING TWO, measured against their own
        `SpecSysXxx.v` -- ONE debt, and it is not an environment problem ==

   (Debts (A) and (B) below are both RETIRED.  They are kept for their
   shapes: (B) is the one that stops a proof dead without any build
   noticing, and (A) is the one where the FUNCTION was already right and
   only its CONTRACT was weak -- three times over, for three entries.)

   (A) RETIRED -- THE REFERENCE LEDGER DID NOT CLOSE, for mkdir, mknod and
       then open.
       An entry returning `iref_slots ns'` at less than `IREFSPARE` cannot
       be wired: `wp_syscall_sconf_body` hands out `iref_slots IREFSPARE`
       and must get `IREFSPARE` back, because [UsertrapRes.ut_own] carries
       the allowance at that literal and [SpecUserretClosed]'s trap loop
       gets its residue back UNCHANGED on the next trap.  A leak of one unit
       per `open` breaks the Löb invariant, so no honest weakening helps:
       the ledger has to close.
       - `sys_mkdir` (20) and `sys_mknod` (17) ARE WIRED.  This entry used
         to say the fact was TRUE for them and only the statement weak --
         create returned the INTERVAL `ns - create_slots <= ns' <= ns` --
         and that tightening it was create's job rather than the syscall's.
         That is what was done: all nine of create's continuation sites
         already computed the exact figure and then weakened into the
         interval, so [SpecCreate]'s post states it outright now
         (`if ok then S ns' = ns else ns' = ns`), mkdir's and mknod's own
         posts say `ns' = ns`, and the arms pass the whole allowance in and
         take the whole allowance out.  It also made both wrappers in
         [FsSyscalls.v] composable, which its note (S3) had ruled out.
       - `sys_open` (15) IS WIRED, and it was the same story a third time.
         This entry used to say the unit was genuinely spent for good --
         the success arm PARKS the reference in `f->ip`
         ([FileInvDefs.inode_pay]), where it lives as long as the
         descriptor does -- and that what was missing was a HOLDER for the
         NFILE units [IREFSLOTS] provisions for ftable entries.  The
         diagnosis was right and the holder is exactly where it guessed:
         [FileInvDefs.file_core] parks `iref_frac q` on the untyped and
         pipe arms, so a free entry's payload IS one unit.  It needed no
         per-`ofile` ghost state in the end, because nothing has to ask
         what type the file is: a whole reference CARRIES the payload, so
         [ProofSysOpenParts.so_open_slot] -- which was dropping it --
         simply hands it back, and the entry holds one unit's worth either
         way, as `iref_frac` when free and as the inode reference once the
         file is published.  [SpecSysOpen]'s post says `ns' = ns`.
   (B) RETIRED -- A CONTRACT WHOSE PID FRACTION EXCEEDED WHAT EXISTS.
       `sys_pipe` (4) used to take `proc_priv` AND
       `SpecFileclose.fileclose_fs_env`, and the latter carried a QUARTER of
       `p->pid`; [ProcInv.proc_priv] owns one half and [SchedCtx]'s state
       resource the other, so three quarters was more than any thread can
       hold outside the proc lock.  Nothing in the build saw it (the premise
       set is satisfiable in isolation -- durable-notes.md's "satisfiable in
       isolation, refutable at the call site"), and the only caller was an
       `Axiom`.  `sys_close` (21) had the same defect.

       BOTH ARE FIXED, and the fix went further than either contract: NO
       file-system contract asks for a fraction of `p->pid` any more.  The
       block ([ProcDefs.proc_priv_bare]) is what travels, from `bread` and
       `bmap` up through `namex` and `fileclose`, and only `acquiresleep`
       and `holdingsleep` -- the two functions that actually load the field
       -- ever see it, borrowing it for that one instruction.  `sys_pipe` is
       WIRED as `sysc_arm_pipe`; its two surviving tie premises (`fcn_pid`,
       `fcn_dq`) are discharged there the way sys_close's are.
   (C) A PREMISE ABOUT UNCHECKED USER INPUT, which no dispatcher can ever
       supply.  `sys_read` (5) takes `0 <= sys_rw_count v2` and
       `MAXFILE*BSIZE + sys_rw_count v2 < 2^31`, and `sys_write` (16) the
       first of the two, about the count word the USER wrote.  Retiring
       them is not spec plumbing:
       - the MAXFILE half is a WEAKENING [SpecFileread.v]'s own header says
         can be relaxed to `n < 2^31` ("mechanical: three uses in ProofFileread.v"), and `sys_rw_count_lt` gives `< 2^31` free -- so
         this half costs one afternoon in fileread;
       - `0 <= n` is readi's overflow arm.  xv6's `off + n < off` test at
         readi+0x026 is DEAD BY PREMISE today ([SpecReadi.v]'s COVERAGE
         NOTE); a negative count arrives as a huge `uint` and fires it.
         What that needs is the wrapping reading of the `c.addw` at +0x022,
         one extra case in `rd_clamp` (0 when `2^32 <= off + n`, which is
         exactly when the test fires) and the arm behind it -- after which
         every readi caller owes a "the sum does not wrap" side condition,
         dischargeable from its own bound.  piperead and consoleread are
         total in a non-positive count already (their loops simply do not
         run), and filewrite's chunking answers -1.

   THE RANK PREMISE IS NOT AN OBSTACLE, AND NO CONTRACT NEEDS TO CHANGE FOR
   IT.  dup/fork/kill/pause/uptime/sync each demand
   `locks_below lks "<rank>"` while `wp_syscall_sconf_body` says nothing
   about `lks` -- but it does not have to.  `syscall()` runs at push_off
   level 0, so `sysc_arm_pre` carries `cpu_own 0 ...`, and
   `CpuOwn.cpu_own_zero_empty` DERIVES `lks = ∅` from it; then
   `LockRank.locks_below_empty` discharges the premise at ANY rank.  Two
   lines per arm (see the comment above `sysc_noff0`), zero ripple into
   usertrap's cone.  SpecSysLink.v's header documents the same derivation
   at its own altitude.

   `sys_exit` (k = 2) IS WIRED (`sysc_arm_exec`'s neighbour
   `sysc_arm_exit`), and every obstacle this header used to attribute to it
   turned out to be a misreading.  Kept because each one is a shape another
   GAP entry may present:

     - THE DIVERGENCE WAS FREE.  Its contract ends in a bare `WP Loop` with
       no continuation, which reads like it cannot fit `sysc_arm_goal` -- but
       `iProp` is AFFINE, so the arm simply DROPS the continuation it is
       handed.  No bespoke branch, no shape change.
     - THE SIX `fn` TIES DISSOLVED TO ONE, because `pj` is an index of
       `syscall_env` too.  An arm may instantiate its callee's proc-array
       parameters AT `fn`'s fields rather than at the dispatch's, so
       `procs_inv (fcn_procs fn)`, the lookup and `pj = proc_addr (fcn_j fn)`
       all moved inside `sysc_fs_env`, where they mention only `fn` and `pj`.
       `fcn_bio fn = bn` and `fcn_dq fn = DfracOwn (1/4)` went the same way.
       Only `fcn_pid fn = pid` was left, and it is a pure premise of
       `wp_syscall_sconf_body` that usertrap discharges by `reflexivity`
       (`UsertrapRes.un_fn` is DEFINED out of the fields it names).  The
       record premise itself is then just record eta: `sysc_fn_eta`.
     - THE NINE MISSING RESOURCE FAMILIES were a NAMING problem, the same one
       `sysc_fs_env` was built for.  It now carries the allocator at `fn`'s
       own `fcn_kmem`/`fcn_kalloc` and the icache bundle whole.
     - `kstack_closer` WAS THE ONE REAL OBSTACLE, and the additive exit slot
       is what removed it -- see `sysc_exit_ty` here and the note at the slot
       in SpecSyscall.v.  This arm is its only consumer: it takes the right
       conjunct and walks the anchor down syscall's own four frame cells
       (which is what `sysc_arm_goal`'s four `word_pointsto`s ARE, once
       `StackOwn.stack_own_4_intro` folds them), landing exactly on the
       anchor and depth `SpecSysExit` names.  Those cells are spent, and
       rightly: nothing pops this frame.

   THE LESSON: this catalogue was wrong about sys_exit on three counts out
   of four, and it was wrong in the SAFE direction each time -- it
   over-counted the obstacles.  Re-measure an entry against its own
   `SpecSysXxx.v` before believing what is written here.

   THE ACTUAL SHAPE OF THE REMAINING WORK, worked out by reading the
   precedents below (do this before touching the proof, it will save many
   remote-build round trips):

   - `syscall()`'s own machine code (KernelSyms.syscall, 100 bytes / 33
     instructions, decoded in CodeSyscall.v) is: a 32-byte frame (ra/s0/s1/
     s2), a direct call to `myproc()` (mirrors ProofSysGetpid.v's own
     myproc-call handling almost verbatim), a load of `p->trapframe->a7`
     (offset 168 off `p->trapframe`, itself loaded at offset 88 off `p`)
     into a5, the ALREADY-PROVED fused range check, `slli`+`auipc`+`addi`+
     `add` computing `&syscalls[num]`, a `c.ld` of the table entry into a5,
     a redundant `beqz a5,fallback` (dead when `1<=num<=22`, refuted by
     `sysc_target_nz`), then `c.jalr a5` -- THE INDIRECT CALL.  On return:
     `sd a0,112(s2)` (store the result to `p->trapframe->a0`), `c.j` over
     the fallback block, then a shared epilogue (reload ra/s0/s1/s2, pop the
     frame, `c.ret`).  The fallback block (unknown syscall number) calls
     `printk("%d %s: unknown sys call %d\n", p->pid, p->name, num)` then
     stores `-1` to `p->trapframe->a0`, falling through to the same shared
     epilogue.
   - `c.jalr a5` IS PRECEDENTED: `WpSconfCtl.wp_cjalr_s_sconf` (its own
     header names this exact use: "fileread's FD_DEVICE arm calls
     devsw[major].read") is the general "indirect call through a register"
     leaf, target `ret_pc (rget m rs1)`.  `ProofFileread.v`'s `devsw[major]
     .read` dispatch (~line 1150-1400) is the closest worked example of
     resolving a table-loaded register to a KNOWN symbol and then applying
     that symbol's whole-function `Module Type` contract exactly like any
     other WP leaf -- no extra combinator beyond the usual `wp_next`/
     `cpu_own_transport`/`wp_next_chain` glue.
   - `ProofArgraw.v` (argraw() itself IS a computed-index jump table, its
     own header says "the first proof in the tree over a computed indirect
     jump") is the load-bearing STRUCTURAL template for the whole dispatch:
     a symbolic-index prologue reaching a table-word fact (`ar_table_word`,
     mirrored here by the already-Qed'd `sysc_table_word`), ONE per-index
     "arm" lemma per case (`ar_arm0`..`ar_arm5`), a tiny combinator
     (`ar_arm`, a bare `destruct k as [|[|...]]; [apply ar_arm0|...]`) and
     the capstone (`wp_argraw_sconf`) assembling prologue + `ar_arm` +
     epilogue.  THIS FILE SHOULD FOLLOW THAT SHAPE AT 22 ARMS INSTEAD OF 6:
     one top-level lemma per `sysc_target` case (heterogeneous types, since
     each `SysXxx` module wants a different resource subset -- unlike
     argraw's six arms, which all shared one trapframe-argument shape), a
     shared prologue lemma reaching the `c.jalr` with `a5` known per-case,
     and a shared epilogue lemma (the `sd a0,112(s2)` / `c.j` / reload /
     pop / `ret` tail) that every RETURNING arm hands its result to.
     `sys_exit`'s own `SYSEXIT.wp_sys_exit_sconf` DIVERGES (bare `WP Loop`,
     no continuation -- see `SpecSysExit.v`), so its arm does not reach the
     shared epilogue at all; see `ProofSysExit.v`'s own call into
     `Kexit.wp_kexit_sconf` for the shape of applying a diverging callee.
   - `syscall_env` is FULLY PERSISTENT (every conjunct is), so it needs no
     open/reassemble dance across a call the way `UsertrapRes.ut_own`'s
     mutable pieces do (`ut_own_rebuild` is the pattern for THOSE, not
     for this) -- derive a `#`-copy once and every arm (and the printk
     fallback) can peel out whichever pieces it needs while the original
     hypothesis stays available, unchanged, to hand back verbatim as `R γf
     pj bn fn` in the continuation.
   - THE OLD RESOURCE-ONLY "EASY (14) / GAP (8)" CATALOGUE IS DELETED, and
     it was wrong in both directions: it counted only what `syscall_env`
     had to SUPPLY, so it called `read`/`write` easy (they carry
     unpayable PURE premises) and `chdir`/`link`/`unlink`/`close`/`sync`
     hard (their resources are all in `fs_ready`).  The debts in the
     STATUS block above are the measured replacement.
   - Syscall ARGUMENTS never cross this file's own concern: every `sys_xxx`
     is niladic in C and reads its own arguments out of `proc_priv`'s
     trapframe page via its own internal `argint`/`argraw`/... calls
     (`ProcGeom.tf_arg_idx`), so `syscall()`'s dispatch does no argument
     marshaling at the `c.jalr` site -- the live register file handed to
     the callee is unconstrained on entry, exactly as `wp_cjalr_s_sconf`'s
     own statement allows.
   - Budget (`av`): `K_syscall = 4 + K_sys_exec` is syscall's OWN 4-slot
     frame plus the deepest callee's own bound, and sys_exec (244) really
     is the deepest -- the runners-up are link 154, open 148, mknod and
     unlink 144, mkdir 142, chdir 136.  myproc()'s call (BEFORE the
     dispatch) needs `(av-4) >= 10` (mirrors ProofSysGetpid.v /
     ProofArgraw.v verbatim), which 244 trivially covers.  After myproc
     returns, `av` is back at the caller's own remaining `(av-4)` for the
     rest of the function, including the dispatch call, so every arm's own
     `K_sys_xxx <= av - 4` premise falls out of `K_syscall <= av` by `lia`.

   ALL 22 sys_* FUNCTIONS ARE PROVEN AND LINKED (sysfile.c is 16/16 and
   file.c 7/7), sys_unlink included -- LinkSysUnlink.v retired the last
   stub axiom.  So nothing below this file is missing: both remaining
   unwired entries are blocked on debt (C) in the STATUS block, and on
   nothing else. *)

From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import VcGen.
Require Import KernelText KernelDataInv RiscvModelBytes.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import WpLock LockRank.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import KptTree TrampPt.
Require Import KallocInv KvmSpec.
Require Import DiskPtsto DiskInv.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
(* [sb_bmapstart]/[bitmap_inv]/[BPB].  The bitmap is a persistent INVARIANT
   now, not a threaded resource: [sysc_bm_cells] reads it (and the two
   superblock cells, at [□]) straight off [FsReady.fs_ready], and no contract
   in the cone names a used-set.  Everything else the fs fabric names is
   qualified at its home
   ([SpecKexec], [SpecPanic], [BioInv], [SpecDirlink], [InodeInv]) rather than
   imported, so nothing this file already says changes meaning. *)
Require Import BitmapInv.
Require Import ConsoleInv.
Require Import CstringInv.
Require Import IcacheRef.
Require Import IrefSlots FdSlots.
Require Import FileInvDefs FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import BioDefs.
Require Import SpecFileclose.
Require Import SpecAllocpid.
Require Import WaitInv.
Require Import TicksInv.
Require Import SpecProcinit.
Require Import PrintkArgs SpecPrintk.
Require Import CodeSyscall.
Require Import SpecSysFork SpecSysExit SpecSysWait SpecSysPipe SpecSysRead SpecSysKill
               SpecSysExec SpecSysFstat SpecSysChdir SpecSysDup SpecSysGetpid SpecSysSbrk
               SpecSysPause SpecSysUptime SpecSysWrite SpecSysMknod SpecSysLink SpecSysMkdir
               SpecSysClose SpecSysSync.
Require Import SpecSysOpen SpecSysUnlink.
Require Import SpecMyproc.
(* the content-independent bundles the non-closer fs entries state their
   environments over -- [filestat_fs_env]/[fread_names] and friends. *)
Require Import UartTxInv.
Require Import SpecFileread SpecFilewrite.
Require Import SpecFilestat.
Require Import BioInv.
Require Import FsReady FsCfg.
Require Import FirstTok.  (* [first_done] -- syscall_env's last conjunct *)
Require Import SyscParkEnv.  (* [sysc_park_extra] -- what the producer below takes *)
Require Import ParkCap.      (* [park_token] -- the park, handed down through [syscall_env] *)
Require Import SpecSyscall.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ======================================================================= *)
(* p->name IS A C STRING, AND THAT IS NOW PROVED.  [ProcDefs.pname_cells]
   carries [ProcGeom.pname_wf] -- "there is a NUL in the sixteen bytes" --
   established at every write site (safestrcpy NUL-terminates, freeproc
   stores a zero, the array boots zero), and [CstringInv.bytes_string_split]
   turns that into the [cstring_bytes nm ++ pad] shape [printk("%s", ...)]
   wants.  There used to be a [PROCNAME_OK] module type here, discharged as
   an axiom in LinkSyscall.v; the fact was never missing from the tree, only
   from the invariant, so nothing had to be assumed. *)

Module SyscallProof
    (SysFork : SYSFORK) (SysExit : SYSEXIT) (SysWait : SYSWAIT)
    (SysPipe : SYSPIPE) (SysRead : SYSREAD) (SysKill : SYSKILL)
    (SysExec : SYSEXEC) (SysFstat : SYSFSTAT) (SysChdir : SYSCHDIR)
    (SysDup : SYSDUP) (SysGetpid : SYSGETPID) (SysSbrk : SYSSBRK)
    (SysPause : SYSPAUSE) (SysUptime : SYSUPTIME) (SysWrite : SYSWRITE)
    (SysMknod : SYSMKNOD) (SysLink : SYSLINK) (SysMkdir : SYSMKDIR)
    (SysClose : SYSCLOSE) (SysSync : SYS_SYNC)
    (SysOpen : SYSOPEN) (SysUnlink : SYSUNLINK)
    (Myproc : MYPROC) (Printk : PRINTK_GEN) : SYSCALL.

(* ONE SECTION PER HART EPOCH.  Every piece below concludes in [WP Loop],
   which names [cpu_id], so a lemma is RIGID at the hart of the section that
   proves it and can never be applied to a goal a [wp_next] crossing has
   carried elsewhere (claude-notes/durable-notes.md, "CpuId IS A CLASS, SO A
   CROSSING NEEDS A NEW SECTION").  Closing a section is what turns the hart
   into an ordinary implicit argument, so the file is stratified by WHO
   APPLIES WHOM ACROSS A CROSSING:

     S1 [SyscallVocab]  the resource bundle, the pure/bitvector lemmas, the
                        dispatch-arm vocabulary, and [sysc_epilogue_tail]
                        (+0x58 .. +0x62);
     S2 [SyscallRet]    [sysc_ret_tail] -- +0x3a (the store of the syscall's
                        result to [p->trapframe->a0]) and +0x3e (the jump into
                        the epilogue).  It applies S1's epilogue AFTER its own
                        two crossings, so it cannot live in S1;
     S3 [SyscallArms]   one lemma per wired table entry, the placeholder
                        stand-in, the [sysc_arm_dispatch] combinator and the
                        printk fallback [sysc_fallback].  An arm applies S2's
                        tail after the CALLEE's crossing (the fallback
                        applies S1's epilogue after printk's);
     S4 [SyscallMain]   the capstone, which applies S3's dispatch at the hart
                        the [c.jalr] lands on.

   The notations and tactics are hoisted out of the sections so all four
   share them. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

(* ===================================================================== *)
(* THE FALLBACK'S FORMAT STRING, and the pure obligations printk's general
   contract states about it.  Mirrors ProcdumpAux.v's [pd_fmt] family
   exactly (same three lemmas, same [kernel_data_string] bridge); the
   address is what [auipc a0,5] at +0x46 followed by [addi a0,a0,2766]
   (a NEGATIVE 12-bit immediate, -1330) computes. *)
Definition sysc_fmt : string :=
  ("%d %s: unknown sys call %d" ++ String (ascii_of_nat 10) EmptyString)%string.
Definition sysc_fmt_a : Z := 0x80007390.

Lemma sysc_fmt_nonul : PrintkFmt.nonul sysc_fmt = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sysc_fmt_kinds : pk_kinds sysc_fmt = [PkNum; PkStr; PkNum].
Proof. vm_compute; reflexivity. Qed.

Lemma sysc_fmt_len : (Z.of_nat (String.length sysc_fmt) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.

Lemma sysc_fmt_bytes :
  forall j b, cstring_bytes sysc_fmt !! j = Some b ->
    KernelData.kernel_data !! (sysc_fmt_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 28 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Ltac pcw := apply bv_eq; vm_compute; reflexivity.
(* the recurring "raw sp-relative address = pa_stk sp k" bridge *)
Ltac stkeq := unfold pa_stk, add_vec_int; f_equal; apply bv_eq; vm_compute; reflexivity.

(* ===================================================================== *)
(* THE TIES: [bn] AND [fn] *ARE* THE AMBIENT FILE SYSTEM.

   [SpecSyscall.v]'s header calls the problem these solve the
   UNREACHABLE-WITNESS problem: a bundle that held the fs fabric at FRESH
   EXISTENTIALS could never be shown to describe the same file system as
   the block/inode resources a closer's contract states at [fn]'s own
   fields.  The first answer was to spell the whole fabric at [fn]'s fields
   -- twenty-five conjuncts of it, restated inside [sysc_fs_env].

   THE SECOND ANSWER, WHICH IS THIS ONE, IS THAT THERE IS ONLY ONE FILE
   SYSTEM.  [FsReady.fs_ready] is that fact as a predicate: every fs
   invariant, lock handle, certificate, superblock cell and geometry
   premise, at the AMBIENT [FsCfg.fscfg]/[IcacheRef.icfg] names, with a
   PRODUCER ([FsReady.fs_ready_establish]) -- which no version of
   [syscall_env] ever had.  So the environment is [fs_ready] plus the
   equations saying the caller's threaded [bn]/[fn] name that same file
   system, and every conjunct the old bundle restated is now a projection
   away.

   Written as a RECORD rather than a conjunction chain because it is
   twenty-eight equations and an arm wants three of them by name.  Compare
   [FsSyscalls.fs_geom], which is the same device for the pure geometry one
   layer out.

   THE THREE THAT ARE NOT EQUATIONS ([sct_pj], [sct_j], [sct_plock]) are
   PROCESS facts about the process [fn] is about, and they are here for the
   same reason they were in the old bundle: an arm may instantiate its
   callee's proc-array parameters at [fn]'s fields rather than at the
   dispatch's, and then it needs them.  [fs_ready] carries no process
   content at all (FsCfg.v's header), which is why they live here and not
   there. *)
Record sysc_ties `{ICFG : icfg} `{FSC : fscfg}
    (pj : mword 64) (bn : bio_names) (fn : fclose_names) : Prop := MkSyscTies {
  (* ---- the block layer and the disk fabric ---- *)
  sct_bn         : bn = fsc_bio;
  sct_bio        : fcn_bio fn = bn;
  sct_bmapstart  : fcn_bmapstart fn = fsc_bmapstart;
  sct_size       : fcn_size fn = fsc_size;
  sct_uart       : fcn_uart fn = fsc_uart;
  sct_disk       : fcn_disk fn = fsc_disk;
  sct_dlock      : fcn_dlock fn = fsc_dlock;
  (* [sct_pd]/[sct_pav]/[sct_pu] ARE GONE, and they are the only three
     equations this record has ever lost.  [fsc_desc]/[fsc_avail]/[fsc_used]
     left [FsCfg.fscfg] (ruling R1: [virtio_disk_init] [kalloc]s the three
     ring pages at WP time, so no boot-era [fupd] can give the record a
     value for them), so there is no field left for an equation to name.
     [fclose_names] KEEPS [fcn_pd]/[fcn_pav]/[fcn_pu] -- every callee still
     threads them -- and what pins them is now a RESOURCE rather than an
     equation: [sysc_fs_env] carries [disk_geom (fcn_disk fn) (fcn_pd fn)
     ...] and the virtio lock at [fn]'s own three, which is what the three
     equations were there to buy.  [sysc_fs_env_all]'s statement, and hence
     every arm below, is unchanged. *)
  (* ---- the inode cache, the region and the log ---- *)
  (* ---- the allocator: the "kmem" lock and its free-list count pair ---- *)
  sct_kmem       : fcn_kmem fn = fsc_kalloc;
  sct_kalloc     : fcn_kalloc fn = fsc_kpages;
  (* ---- the one fraction left.  [fcn_dqb]/[fcn_dqs] are GONE from
         [fclose_names] (the superblock cells are DISCARDED for good --
         FsReady.v §0b -- and every contract that reads one takes it at a
         generic [dq] which the dispatch instantiates at [DfracDiscarded]),
         so the two equations that used to say so have nothing left to name.
         The pid quarter is what iput's contract is lent at. ---- *)
  sct_dq         : fcn_dq fn = DfracOwn (1/4);
  (* ---- the process [fn] is about IS the one the dispatch is running ---- *)
  sct_pj         : pj = proc_addr (fcn_j fn);
  sct_j          : (fcn_j fn < NPROC)%nat;
  sct_plock      : fcn_procs fn !! fcn_j fn = Some (fcn_plock fn);
}.

Section SyscallVocab.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ===================================================================== *)
  (* syscall_env -- the union of everything the wired entries need
     that is NOT one of the four explicit families (bslots/initproc/
     fd_slots/iref_slots).  Every conjunct is Persistent (is_lock,
     kalloc_env at [None], procs_avail at [None], printk_env), so the whole
     bundle is held with [#] and never needs reassembly across a call --
     no wired entry writes anything inside it.  THERE IS NO MUTABLE FIFTH
     FAMILY any more: the block bitmap used to ride outside as
     [fileclose_bm fn us], re-indexed on the way out, and it is now the
     persistent [BitmapInv.bitmap_inv] inside [FsReady.fs_ready] -- which is
     why [sysc_arm_pre] and [sysc_hcont_ty] lost a row and a binder each. *)
  (* explicit (redundant-with-Section) binder list, for two reasons.  It
     pins the full fifteen classes so Section discharge cannot narrow the
     inferred signature below what the [SYSCALL] Module Type's
     [syscall_env] Parameter fixes (the body used to need fewer -- with
     [sysc_fs_env] in it, it now genuinely uses [bioG]/[logG]/[fsCrashG]
     too).  And it is what lets the body MENTION [sysc_fs_env] at all: a
     Section-variable [Σ] would not be this definition's own. *)
  (* ===================================================================== *)
  (* THE FILE-SYSTEM FABRIC, AT [fn]'s OWN NAMES -- what closing a GAP entry
     costs, and it is a NAMING change, not a type change.

     The nine wired entries all take their icache/fs ghost names as
     free-standing parameters, so a fresh existential inside this bundle was
     exactly as good as one tied to the ambient [fn].  The GAP entries are
     precisely the ones where that stops being true: [sys_exec] consumes
     [SpecKexec.fs_fabric] AND the two superblock cells AND
     [BitmapInv.bitmap_inv], all in the same breath and all at
     [fn]'s own [fcn_fs]/[fcn_bmapstart]/[fcn_cov]/[fcn_logstart]/[fcn_size],
     so a fabric over fresh existentials could never be shown to describe the
     same file system -- SpecSyscall.v's header calls that the
     UNREACHABLE-WITNESS problem, and it is why the two extra indices [bn]/
     [fn] exist.  So everything the fabric needs that [sysc_bm_cells] also
     pins is spelled at [fn]'s fields, and the rest is spelled at the AMBIENT
     [icfg] class ("there is one inode cache"), which is what lets
     [dev]/[nib]/[g] be discharged by [eq_refl] instead of by a tie.

     EVERYTHING IS AT [fn]'s OWN FIELD NAMES, and the ties to the ambient
     [icfg] class ride as pure conjuncts rather than being baked in.  That
     is what lets one bundle serve two very differently-shaped callees:
     [sys_exec] takes [dev]/[nib]/[g] as parameters and asks for them to
     equal [icfg_dev]/[icfg_nib]/[icfg_log], while [sys_exit] asks for
     [⌜fclose_ties fn⌝], which is at [fn]'s fields throughout.  Spelling the
     bundle at [fn] and carrying the ties makes both a rewrite away;
     spelling it at [icfg] would have made the second unreachable.

     THE ICACHE IS NOT A ROW OF THIS BUNDLE, nor of [sysc_fs_env_all].
     [is_itable2]/[itable_inv]/[ic_escrows]/[ic_sleeplocks] used to be
     conjuncts of [syscall_env] in their own right, at fresh existentials;
     they are conjuncts of [FsReady.fs_ready] now, so an arm that wants them
     derives them with [sysc_ic_env_of_ready] (below) out of the very
     [fs_ready] this bundle already carries.

     [procs_inv (fcn_procs fn)] IS here, unlike in the first version of this
     bundle.  [sysc_arm_pre] already carries [procs_inv γs] at the DISPATCH's
     own [γs] and the two cannot be tied -- but they do not have to be: an
     arm is free to instantiate its callee's proc-array parameters at [fn]'s
     fields instead of at the dispatch's, and then it wants [fn]'s own
     [procs_inv].  Both are persistent, so carrying the two costs nothing.
     That is what dissolves four of the six ties SpecSyscall.v's header
     attributed to [sys_exit]; only [fcn_pid fn = pid] escapes, and it is a
     pure premise of [wp_syscall_sconf_body] (usertrap discharges it by
     [reflexivity] -- [UsertrapRes.un_fn] is built from the very fields the
     tie names). *)
  (* the SAME explicit (redundant-with-Section) binder list [syscall_env]
     carries, and for a sharper reason than its own: a definition that took
     the Section's variables would be fixed at the Section's [Σ], and
     [syscall_env] -- which binds its own -- could not then mention it. *)
  Definition sysc_fs_env
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (pj : mword 64) (bn : bio_names) (fn : fclose_names) : iProp Σ :=
    (⌜sysc_ties pj bn fn⌝ ∗
     (* the proc array, at [fn]'s own names.  Not a conjunct of [fs_ready]:
        it is a PROCESS resource and the file system has no process content
        (FsCfg.v's header).  [sysc_arm_pre] carries the DISPATCH's own
        [procs_inv γs] beside this one; both are persistent, so carrying two
        costs nothing and it is what lets an arm instantiate a callee at
        either spelling. *)
     procs_inv (fcn_procs fn) ∗
     (* THE DISK FABRIC AT [fn]'s OWN THREE PAGES (R1).  This replaces
        [sysc_ties]' [sct_pd]/[sct_pav]/[sct_pu]: the pages are no longer
        [fscfg] fields, so [fs_ready] quantifies them
        ([FsReady.fs_ready]'s disk conjunct) and there is nothing for an
        equation to point at.  Both rows are Persistent, so the bundle is
        still held with [#] and still needs no reassembly.

        A PRODUCER PAYS NOTHING NEW.  It holds [fs_ready], unpacks the
        existential, and builds [fn] with [fcn_pd] at the witness -- [fn] is
        the producer's own record ([UsertrapRes.un_fn]).  Going the other
        way, [FsReady.disk_geom_agree] identifies any two.  So the
        precondition is the SAME precondition, spelled where the pages
        actually live. *)
     disk_geom (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) ∗
     is_lock (fcn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn)) ∗
     FsReady.fs_ready)%I.

  (* no explicit binder list here -- unlike the Definition above, an
     [Instance] takes its binders as a CONTEXT, so re-binding the Section's
     [GEN] is rejected ("GEN is already used").  The Section's variables are
     the right ones anyway: the instance is only ever looked up after [End]
     discharges them. *)
  Global Instance sysc_fs_env_persistent pj bn fn : Persistent (sysc_fs_env pj bn fn).
  Proof. rewrite /sysc_fs_env. apply _. Qed.

  (* THE CLOSER'S OWN TIE RECORD, out of the dispatch's.  [fclose_ties] is
     [SpecFileclose]'s twelve-equation statement of "this [fclose_names]
     names the ambient file system"; [sysc_ties] says the same and more (the
     three process facts, the [bn] equation, the pid fraction), so this is a
     projection with one composition in it -- [fcn_bio] goes through [bn]. *)
  Lemma sysc_fclose_ties (pj : mword 64) (bn : bio_names) (fn : fclose_names) :
    sysc_ties pj bn fn -> fclose_ties fn.
  Proof.
    intro T. constructor.
    - exact (sct_uart _ _ _ T).
    - exact (sct_disk _ _ _ T).
    - exact (sct_dlock _ _ _ T).
    - exact (sct_kmem _ _ _ T).
    - exact (sct_kalloc _ _ _ T).
    - rewrite (sct_bio _ _ _ T). exact (sct_bn _ _ _ T).
    - exact (sct_bmapstart _ _ _ T).
    - exact (sct_size _ _ _ T).
  Qed.

  (* THE INODE CACHE, AS THE ARMS READ IT OFF THE BUNDLE.  It USED TO be a
     [Definition] here -- a verbatim copy of the body the DELETED
     [SpecFileclose.fileclose_ic_env] had -- carried as one row of
     [sysc_fs_env_all] so that the eleven arms' positional destructs would
     not have to move.  A copy of a deleted definition is still a copy: every
     one of these fifteen conjuncts is a PROJECTION of the
     [FsReady.fs_ready] the bundle already carries, re-spelled at [fn]'s own
     fields by [sysc_ties].  So it is a LEMMA now, the row is gone from
     [sysc_fs_env_all], and an arm that wants the cache asks for it ONCE --
     one lemma application per arm, so the derivation is shared rather than
     unfolded into each proof term.  The CONJUNCT ORDER is the old body's,
     which is what keeps the arms' inner destruct patterns verbatim. *)
  Lemma sysc_ic_env_of_ready (pj : mword 64) (bn : bio_names)
      (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗
    (⌜0 < fcn_size fn <= BPB⌝ ∗
     ⌜0 <= fcn_bmapstart fn⌝ ∗
     ⌜fcn_bmapstart fn ∈ fsc_cov⌝ ∗
     ⌜~ (fcn_bmapstart fn ∈ log_region_set fsc_logst)⌝ ∗
     ⌜0 <= icfg_ist⌝ ∗
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        DinodeEnc.IBLOCK inum icfg_ist ∈ fsc_cov /\
        ~ (DinodeEnc.IBLOCK inum icfg_ist
             ∈ log_region_set fsc_logst)⌝ ∗
     ⌜IcacheInv.cov_below fsc_cov (fcn_size fn)⌝ ∗
     IcacheEscrow.is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg
                fsc_cov fsc_logst icfg_nib icfg_dev ∗
     IcacheInv.itable_inv ∗
     IcacheEscrow.ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov
                fsc_logst ∗
     InodeRegion.ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     ireg_open ∗
     IcacheEscrow.ic_sleeplocks fsc_ic)%I.
  Proof.
    (* the three rows between the ties and [fs_ready] -- [procs_inv] and the
       two disk rows -- are nothing this bundle is about. *)
    iIntros "(%T & _ & _ & _ & #Hrdy)".
    iDestruct (FsReady.fs_ready_geom with "Hrdy") as "%G".
    iDestruct (FsReady.fs_ready_icache with "Hrdy")
      as "(#Hit & #Hitinv & #Hesc & #Hsl)".
    iDestruct (FsReady.fs_ready_region with "Hrdy") as "[#Hireg #Hropen]".
    (* THE TIES, APPLIED TO THE WHOLE GOAL AT ONCE -- [sysc_fs_env_all]'s
       idiom, and for its reason: the proofmode goal IS [envs_entails Δ _],
       so an UNSCOPED rewrite re-spells the four hypotheses above at [fn]'s
       fields and turns the two [icfg] rows of the conclusion into
       [reflexivity] in the same step.  Only the nine ties whose ambient side
       actually OCCURS are in the chain: [fsc_bmapstart]/[fsc_size] reach
       this goal through no hypothesis (the pure rows below carry them out of
       [G] instead), and a rewrite with no subterm to hit is an error. *)
    iSplit.
    { iPureIntro. rewrite (sct_size _ _ _ T). exact (FsReady.fgo_size G). }
    iSplit.
    { iPureIntro. rewrite (sct_bmapstart _ _ _ T). exact (FsReady.fgo_bm_nn G). }
    iSplit.
    { iPureIntro. rewrite (sct_bmapstart _ _ _ T).
      exact (FsReady.fgo_bm_cov G). }
    iSplit.
    { iPureIntro. rewrite (sct_bmapstart _ _ _ T).
      exact (FsReady.fgo_bm_out G). }
    iSplit.
    { iPureIntro. exact (FsReady.fgo_ist_nn G). }
    iSplit.
    { iPureIntro. exact (FsReady.fgo_iblocks G). }
    iSplit.
    { iPureIntro. rewrite (sct_size _ _ _ T).
      exact (FsReady.fgo_covbelow G). }
    iSplit; [ iExact "Hit"     |].
    iSplit; [ iExact "Hitinv"  |].
    iSplit; [ iExact "Hesc"    |].
    iSplit; [ iExact "Hireg"   |].
    iSplit; [ iExact "Hropen"  |].
    iExact "Hsl".
  Qed.

  (* THE UNPACK, AND WHY IT IS SHAPED LIKE THE OLD BUNDLE.

     Every conjunct below used to be a conjunct of [sysc_fs_env] in its own
     right, spelled at [fn]'s fields.  Keeping the ORDER means the arms'
     existing [iDestruct] patterns read the same, and the diff of this
     increment is one token per arm rather than a rewritten arm -- which
     matters, because a mis-shifted pattern in one of eleven arms is a
     silent change of which resource an arm thinks it holds.

     The last four rows are NEW, and they are what the twelve unwired
     entries were waiting on: [sb_ninodes] / [sb_size] (create's own reads,
     which the old closer bundle never carried ([fclose_names] has no field
     for the inode count), the printk contract ialloc's out-of-inodes arm
     needs, and printk's own credential.  All four come out of [fs_ready]
     free; none of them could have been stated at [fn]'s fields at all. *)
  Lemma sysc_fs_env_ties (pj : mword 64) (bn : bio_names) (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗ ⌜sysc_ties pj bn fn⌝.
  Proof. rewrite /sysc_fs_env. by iIntros "($ & _)". Qed.

  Lemma sysc_fs_env_all
      (pj : mword 64) (bn : bio_names) (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗
    ⌜icfg_dev = InodeInv.ROOTDEV⌝ ∗
    ⌜(0 < icfg_nib)%nat⌝ ∗
    ⌜fcn_dq fn = DfracOwn (1/4)⌝ ∗
    ⌜fcn_bio fn = bn⌝ ∗
    ⌜pj = proc_addr (fcn_j fn)⌝ ∗
    ⌜(fcn_j fn < NPROC)%nat⌝ ∗
    ⌜fcn_procs fn !! fcn_j fn = Some (fcn_plock fn)⌝ ∗
    ⌜log_geom_ok fsc_cov fsc_logst⌝ ∗
    procs_inv (fcn_procs fn) ∗
    SpecPanic.panic_env ∗
    BioInv.bio_ctx bn (fs_view fsc_fs (fcn_disk fn) icfg_dev fsc_cov) ∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst icfg_dev ∗
    fs_crash_seam fsc_cov fsc_logst ∗
    gen_cert ∗
    dev_inv (fcn_uart fn) (fcn_disk fn) ∗
    disk_geom (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) ∗
    is_lock (fcn_dlock fn) d_lock "virtio_disk"%string
      (disk_res (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn)) ∗
    is_lock (fcn_kmem fn) (mword_of_int KernelSyms.kmem) "kmem"%string
      (kmem_res (fcn_kalloc fn) (mword_of_int (KernelSyms.kmem + 24))) ∗
    kalloc_avail (fcn_kalloc fn) None ∗
    (* [sysc_ic_env fn] USED TO BE HERE, between the allocator and
       [ireg_open].  It is [sysc_ic_env_of_ready] now: the icache rows are a
       projection of this bundle's own [fs_ready], so an arm derives them
       instead of unpacking a row that had to be rebuilt here first. *)
    ireg_open ∗
    (* ---- the four rows the old bundle could not state ---- *)
    ⌜bitmap_geom_ok fsc_cov fsc_logst (fcn_bmapstart fn) (fcn_size fn)⌝ ∗
    ⌜1 < fsc_ninodes /\ fsc_ninodes <= 16 * Z.of_nat icfg_nib
      /\ fsc_ninodes < 2 ^ 31 /\ 16 * Z.of_nat icfg_nib <= 2 ^ 16⌝ ∗
    InodeInv.sb_ninodes ↦₄□ (mword_of_int fsc_ninodes : mword 32) ∗
    BitmapInv.sb_size ↦₄□ (mword_of_int (fcn_size fn) : mword 32) ∗
    (* ...AT [fn]'s UART/disk names, like every other fabric row above --
       the printk GNAME has no [fclose_names] field, so it stays ambient.
       Spelling the pair at [fn]'s is what lets one arm hand [dev_inv] and
       [printk_env] to a callee that takes ONE uart parameter for both
       (every create-family entry does). *)
    ⌜printk_gen_contract (kt := KT1) fsc_printk (fcn_uart fn) (fcn_disk fn)⌝ ∗
    printk_env fsc_printk (fcn_uart fn) (fcn_disk fn).
  Proof.
    (* [Hgeom]/[Hdlock] come out of the BUNDLE now, at [fn]'s own three ring
       pages, and [fs_ready]'s own disk conjunct -- which quantifies them
       (R1) -- is dropped ([_] at slot 10 below). *)
    iIntros "(%T & #Hprocs & #Hgeom & #Hdlock & #Hrdy)".
    iDestruct (FsReady.fs_ready_geom with "Hrdy") as "%G".
    iDestruct (FsReady.fs_ready_all with "Hrdy") as
      "(_ & _ & #Hpr & %Hprg & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi &
        _ & #Hit & #Hitinv & #Hesc & #Hsl & #Hireg & #Hropen &
        #Hka & _ & _)".
    iDestruct (FsReady.fs_ready_kmem with "Hrdy") as "[#Hkm #Hav]".
    iDestruct (FsReady.fs_ready_sb with "Hrdy") as "(#Hsbn & #Hsbi & #Hsbs & #Hsbb)".
    iDestruct (FsReady.fs_ready_panic with "Hrdy") as "#Hpanic".
    (* THE TIES, APPLIED TO THE WHOLE GOAL AT ONCE.  The proofmode goal IS
       [envs_entails Δ _] and [Δ] carries every hypothesis, so an UNSCOPED
       [rewrite] re-spells the hypotheses and the conclusion together --
       which is exactly what is wanted here: [fs_ready] hands everything
       over at the ambient names and this bundle promises it at [fn]'s.  The
       PURE facts ([G], [Hprg]) are Coq hypotheses rather than [Δ] entries,
       so they are NOT re-spelled and each pure row below rewrites its own
       way (durable-notes.md's note on the un-scoped rewrite, at
       [sysc_arm_exit]). *)
    rewrite -(sct_bn _ _ _ T) -(sct_bmapstart _ _ _ T) -(sct_size _ _ _ T)
            -(sct_uart _ _ _ T) -(sct_disk _ _ _ T)
            (* [sct_dlock] IS NOT IN THIS CHAIN, and that is R1's doing:
               [fsc_dlock] used to reach the goal only through [fs_ready]'s
               [is_lock fsc_dlock … (disk_res fsc_disk fsc_desc …)] row, and
               that row is now the BUNDLE's own [is_lock (fcn_dlock fn) …].
               So there is no [fsc_dlock] left anywhere in [Δ] or the
               conclusion, and the rewrite would fail with "does not match
               any subterm".  The tie itself stays on the record -- a
               consumer still reads [fcn_dlock fn = fsc_dlock]. *)
            -(sct_kmem _ _ _ T) -(sct_kalloc _ _ _ T).
    (* assembled conjunct by conjunct rather than with a named [iFrame]: the
       thirty-one rows are in this bundle's own order and every one of them
       is persistent, so a mismatch names the row that moved instead of
       leaving an unsolved goal (the idiom [sysc_fs_fabric] already uses). *)
    (* THE FOUR ties to the [icfg] class ARE GONE (rank 1c): the device,
       the inode count, the log's names and the region's first block are
       read off the class, so there is no threaded copy to tie. *)
    iSplit.
    { iPureIntro. exact (FsReady.fgo_rootdev G). }
    iSplit.
    { iPureIntro. exact (FsReady.fgo_nib_pos G). }
    iSplit; [ iPureIntro; exact (sct_dq _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_bio _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_pj _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_j _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_plock _ _ _ T) |].
    iSplit.
    { iPureIntro. 
      exact (FsReady.fgo_loggeom G). }
    iSplit; [ iExact "Hprocs" |].
    iSplit; [ iExact "Hpanic" |].
    iSplit; [ iExact "Hbio"   |].
    iSplit; [ iExact "Hlog"   |].
    iSplit; [ iExact "Hseam"  |].
    iSplit; [ iExact "Hgen"   |].
    iSplit; [ iExact "Hdevi"  |].
    iSplit; [ iExact "Hgeom"  |].
    iSplit; [ iExact "Hdlock" |].
    iSplit; [ iExact "Hkm"    |].
    iSplit; [ iExact "Hav"    |].
    (* the icache row is GONE from here -- [sysc_ic_env_of_ready] derives it
       from [fs_ready] directly.  [Hit]/[Hitinv]/[Hesc]/[Hsl] stay
       DESTRUCTED above rather than dropped: the blanket rewrite needs
       [fsc_ic]/[fsc_itlock] to occur somewhere in [Δ], and those four rows
       are the only place they do. *)
    iSplit; [ iExact "Hropen" |].
    iSplit.
    { iPureIntro. rewrite
                          (sct_bmapstart _ _ _ T) (sct_size _ _ _ T).
      exact (FsReady.fgo_bmgeom G). }
    iSplit.
    { iPureIntro.
      split; [ exact (FsReady.fgo_nin_lo G) |].
      split; [ exact (FsReady.fgo_nin_hi G) |].
      split; [ exact (FsReady.fgo_nin_31 G) | exact (FsReady.fgo_ushort G) ]. }
    iSplit; [ iExact "Hsbn" |].
    iSplit; [ iExact "Hsbs" |].
    iSplit.
    { iPureIntro. rewrite (sct_uart _ _ _ T) (sct_disk _ _ _ T). exact Hprg. }
    iExact "Hpr".
  Qed.

  (* THE PROCESS-SIDE AMBIENT, which is all that is left beside [fs_ready]:
     four spinlock handles and the availability cell.  Not one of them is
     file-system state, which is exactly why they are here and not in
     [FsCfg.fscfg] (that class has no process content at all).

     [kalloc_env] AND [printk_env] USED TO BE CONJUNCTS OF THIS BUNDLE, AT
     FRESH EXISTENTIALS, AND THAT WAS A LATENT SATISFIABILITY BUG.  There is
     one "kmem" spinlock at [KernelSyms.kmem] and one UART; a bundle
     asserting [kalloc_env γa None] at an existential [γa] BESIDE
     [sysc_fs_env]'s [is_lock (fcn_kmem fn) ...] was claiming two lock
     handles for one address at two unrelated gnames, and nothing in the
     build could see it because nobody constructs the bundle yet.  Both now
     come out of [fs_ready], where there is exactly one of each, and
     [syscall_env_all] hands them to the arms in the old shape. *)
  Definition sysc_proc_env
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (γf : gname) : iProp Σ :=
    (∃ (γp γw γft γtk : gname),
       is_lock γp alp_pid_lock "nextpid"%string nextpid_res ∗
       procs_avail None ∗
       is_lock γw wait_lock_addr "wait_lock"%string wait_res ∗
       is_ftable γft γf ∗
       is_tickslock γtk)%I.

  Definition syscall_env
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (γf : gname) (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      : iProp Σ :=
    (sysc_proc_env γf ∗ ConsoleInv.console_ready ∗ sysc_fs_env pj bn fn ∗
     (* THE STEADY ARM OF proc.c's [static int first]
        ([FirstTok.first_done]).  It is here, and LAST, for two reasons.
        HERE: fork is the one syscall that BUILDS a second process block,
        and a block carries [FirstTok.first_tok] -- which the parent cannot
        share, its boot arm being exclusive.  The persistent steady arm is
        what a running process can hand to every child forever, and
        [FirstTok.first_tok_of_done] mints the child's from it.
        LAST: every arm's [iDestruct] pattern is positional, so a conjunct
        added anywhere else silently re-binds someone's hypothesis; the
        patterns that end in [& _] absorb this one for free.
        NOBODY CONSTRUCTS THIS BUNDLE YET (it arrives abstractly as
        usertrap's [Rsys]), which is deliberate: the obligation lands
        exactly where forkret will discharge it -- its boot arm persists the
        store and seals the file system, its steady arm already holds
        both halves. *)
     FirstTok.first_done ∗
     (* ...AND THE WORLD A CHILD'S PARK NEEDS ([SyscParkEnv.park_world]),
        appended LAST for the same positional reason: fork hands it down
        to kfork, which builds the child's trap-loop environment from it.
        The parker of THIS process supplied it ([UsertrapRes.ut_park_caps])
        and [syscall_env_park] copies it in. *)
     park_world (fcn_procs fn) ∗
     park_token (fcn_procs fn))%I.

  (* ===================================================================== *)
  (* ...AND ITS PRODUCER.  [SpecSyscall.SYSCALL]'s [syscall_env_park].       *)
  (* ===================================================================== *)
  (* The paragraph above says nobody constructs this bundle yet.  THIS IS
     THE CONSTRUCTOR, and the reason it can exist is the reason the comment
     said the obligation would land at forkret: [FirstTok.first_done] is
     [first_addr |->4[] 0] beside [FsReady.fs_ready], forkret holds it on
     BOTH arms of its [if (first)], and it carries three of this bundle's
     four conjuncts outright.

     WHAT IS ACTUALLY OWED, then, is only what [fs_ready] does not carry:
     [SyscParkEnv.sysc_park_extra]'s four (the nextpid lock, the slot
     ledger, the ticks lock, the console) plus four the caller is holding
     anyway for [UsertrapRes.ut_caps] (the [wait_lock], [is_ftable],
     [procs_inv], [disk_geom]).  All eight are persistent and all eight
     exist before either parker runs.

     THE DISK LOCK IS THE ONE ROW THAT IS NOT A COPY, for the reason
     [sysc_fs_env]'s own header gives: [fs_ready] QUANTIFIES the three ring
     pages (R1) while this bundle names them at [fn]'s fields, so the
     witness is opened here and [FsReady.disk_geom_agree] identifies it with
     the caller's [disk_geom].  That is exactly what that lemma exists for.

     [sysc_ties] IS DERIVED, NOT TAKEN.  Fourteen of its equations are
     [fclose_ties]' verbatim, [sct_bn]/[sct_bio] are that record's [fcn_bio]
     row read twice, and the remaining four are the pure premises above --
     so a caller that already owes [fclose_ties fn] for [ut_caps] owes
     nothing new here. *)
  Lemma sysc_ties_of_fclose (fn : fclose_names) :
    fclose_ties fn ->
    (fcn_j fn < NPROC)%nat ->
    fcn_procs fn !! fcn_j fn = Some (fcn_plock fn) ->
    fcn_dq fn = DfracOwn (1/4) ->
    sysc_ties (proc_addr (fcn_j fn)) (fcn_bio fn) fn.
  Proof.
    intros [Huart Hdisk Hdlock Hkmem Hkalloc Hbio Hbms Hsize] Hj Hplock Hdq.
    (* [sct_bio] and [sct_pj] are [reflexivity] because the indices were
       READ OFF [fn]; everything else is one of the twenty-two hypotheses. *)
    constructor; try assumption; try reflexivity.
  Qed.

  Lemma syscall_env_park (γf γw γft γtk : gname) (fn : fclose_names) :
    fclose_ties fn ->
    (fcn_j fn < NPROC)%nat ->
    fcn_procs fn !! fcn_j fn = Some (fcn_plock fn) ->
    fcn_dq fn = DfracOwn (1/4) ->
    sysc_park_extra γtk -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    is_ftable γft γf -∗
    procs_inv (fcn_procs fn) -∗
    disk_geom (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) -∗
    first_done -∗
    park_world (fcn_procs fn) -∗
    park_token (fcn_procs fn) -∗
    syscall_env γf (proc_addr (fcn_j fn)) (fcn_bio fn) fn.
  Proof.
    iIntros (Hties Hj Hplock Hdq) "#Hextra #Hwl #Hft #Hprocs #Hdg #Hdone #Hworld #Htok".
    iDestruct "Hextra" as "(#Hnextpid & #Hpav & #Htick & #Hcons)".
    iDestruct "Hdone" as "[#Hcell #Hrdy]".
    pose proof Hties as Ht.
    destruct Ht as [Huart Hdisk Hdlock _ _ _ _ _ _ _ _ _].
    (* the disk fabric, at [fn]'s pages rather than at [fs_ready]'s witness *)
    iDestruct (FsReady.fs_ready_disk with "Hrdy") as "[_ Hdex]".
    iDestruct "Hdex" as (pd pav pu) "[#Hdg2 #Hdlk]".
    iDestruct (FsReady.disk_geom_agree fsc_disk (fcn_pd fn) (fcn_pav fn)
                 (fcn_pu fn) pd pav pu with "[] []") as %(Hpd & Hpav & Hpu);
      [ rewrite -Hdisk; iExact "Hdg" | iExact "Hdg2" |].
    rewrite /syscall_env.
    iSplitR.
    { rewrite /sysc_proc_env.
      iDestruct "Hnextpid" as (γp) "#Hnp".
      iExists γp, γw, γft, γtk. iFrame "Hnp Hpav Hwl Hft Htick". }
    iSplitR; [iExact "Hcons"|].
    iSplitR.
    { rewrite /sysc_fs_env.
      iSplitR;
        [iPureIntro; exact (sysc_ties_of_fclose fn Hties Hj Hplock Hdq)|].
      iFrame "Hprocs Hdg".
      iSplitR; [rewrite Hdlock Hdisk Hpd Hpav Hpu; iExact "Hdlk"|].
      iExact "Hrdy". }
    iSplitR; [rewrite /first_done; iFrame "Hcell Hrdy"|].
    iSplitR; [iExact "Hworld"|].
    iExact "Htok".
  Qed.

  (* THE CONSOLE, reached on its own rather than through [syscall_env_all].
     Adding it to that projection's output would move eleven arms'
     [iDestruct] patterns, and a mis-shifted pattern in one of eleven is a
     silent change of which resource an arm thinks it holds
     (completed/explicit-cpuid.md's failure mode).  The two arms that want
     the console take it here instead.

     It is NOT in [FsReady.fs_ready]: the console is not the file system, and
     [fs_ready]'s establishment is already the boot chain's largest owed
     row.  It is a SIBLING conjunct, so the only thing that grows is whatever
     finally establishes [syscall_env].  Nobody does yet: [LinkSyscall.v]
     LINKS the dispatch (all twenty-two arms, no axiom), but establishing
     the environment is the trap loop's entry problem, owed by whoever pays
     [SpecForkretParkPaid.forkret_park_pkg]'s residue closer.  Cheaply, as
     that file notes: [syscall_env] is entirely persistent, so a second
     process's copy costs nothing. *)
  Lemma syscall_env_console (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    syscall_env γf pj bn fn -∗ ConsoleInv.console_ready.
  Proof. by iIntros "(_ & $ & _)". Qed.

  (* ...and the fork row, on its own for the same reason the console is:
     ONE arm wants it, and adding it to [syscall_env_all]'s output would
     move eleven [iDestruct] patterns. *)
  Lemma syscall_env_first (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    syscall_env γf pj bn fn -∗ FirstTok.first_done.
  Proof. by iIntros "(_ & _ & _ & $ & _)". Qed.

  Lemma syscall_env_world (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    syscall_env γf pj bn fn -∗ park_world (fcn_procs fn).
  Proof. by iIntros "(_ & _ & _ & _ & $ & _)". Qed.

  Lemma syscall_env_token (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    syscall_env γf pj bn fn -∗ park_token (fcn_procs fn).
  Proof. by iIntros "(_ & _ & _ & _ & _ & $)". Qed.

  (* ...and the OLD shape, as a projection.  Same reason [sysc_fs_env_all]
     keeps its order: an arm's [iDestruct] pattern is an interface, and
     re-shuffling eleven of them by hand is the kind of edit that compiles
     while meaning something else. *)
  Lemma syscall_env_all (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    syscall_env γf pj bn fn -∗
    ∃ (γa γp γw γft γtk γpr : gname)
      (γud : uart_names) (γvd : disk_names),
      kalloc_env γa None ∗
      is_lock γp alp_pid_lock "nextpid"%string nextpid_res ∗
      procs_avail None ∗
      is_lock γw wait_lock_addr "wait_lock"%string wait_res ∗
      is_ftable γft γf ∗
      is_tickslock γtk ∗
      printk_env γpr γud γvd ∗
      sysc_fs_env pj bn fn.
  Proof.
    iIntros "(#Hproc & _ & #Hfs & _)".
    iDestruct "Hproc" as (γp γw γft γtk)
      "(#Hnextpid & #Hpav & #Hwaitlk & #Hftable & #Htick)".
    iPoseProof "Hfs" as "#Hfsc".
    (* five rows now: the ties, [procs_inv], the two disk rows R1 moved in,
       and [fs_ready] *)
    iDestruct "Hfsc" as "(_ & _ & _ & _ & #Hrdy)".
    iDestruct (FsReady.fs_ready_kalloc with "Hrdy") as "#Hkalloc".
    iDestruct (FsReady.fs_ready_printk with "Hrdy") as "[#Hpr _]".
    iExists fsc_kalloc, γp, γw, γft, γtk, fsc_printk, fsc_uart, fsc_disk.
    iFrame "Hkalloc Hnextpid Hpav Hwaitlk Hftable Htick Hpr Hfs".
  Qed.

  (* [SpecKexec.fs_fabric], re-assembled: the thirteen persistent resources
     kexec's cone (and therefore sys_exec's) states as one bundle.  Two of
     them come from OUTSIDE [syscall_env] -- [kernel_data], which every arm
     already holds, and [procs_inv γs] at the dispatch's own [γs] -- see
     [sysc_fs_env]'s note on why they cannot live in the bundle. *)
  Lemma sysc_fs_fabric (γf : gname) (pj : mword 64) (γs : list gname)
      (bn : bio_names) (fn : fclose_names) :
    kernel_data -∗ procs_inv γs -∗ syscall_env γf pj bn fn -∗
    SpecKexec.fs_fabric γs (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
      (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

.
  Proof.
    iIntros "#Hdata #Hprocs #Henv".
    iDestruct (syscall_env_all with "Henv") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & _ & _ & _ & #Hfs)".
    iDestruct (sysc_fs_env_all with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & _ &
        _ & #Hpanic & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ )".
    iDestruct (sysc_ic_env_of_ready with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & #Hit & #Hitinv & #Hesc & #Hireg &
        #Hropen & #Hsl )".
    (* assembled conjunct by conjunct rather than with [iFrame "#"]: the
       fifteen are in the fabric's own order, and a mismatch then names the
       one that moved instead of leaving an unsolved goal. *)
    rewrite /SpecKexec.fs_fabric.
    iSplitR; [iExact "Hdata"   |].
    iSplitR; [iExact "Hpanic"  |].
    iSplitR; [iExact "Hbio"    |].
    iSplitR; [iExact "Hlog"    |].
    iSplitR; [iExact "Hseam"   |].
    iSplitR; [iExact "Hgen"    |].
    iSplitR; [iExact "Hit"     |].
    iSplitR; [iExact "Hitinv"  |].
    iSplitR; [iExact "Hesc"    |].
    iSplitR; [iExact "Hsl"     |].
    iSplitR; [iExact "Hireg"   |].
    iSplitR; [iExact "Hropen"  |].
    iSplitR; [iExact "Hprocs"  |].
    iSplitR; [iExact "Hdevi"   |].
    iSplitR; [iExact "Hgeom"   |].
    iExact "Hdlock".
  Qed.

  (* THE THREE RESOURCES [SpecFileclose.fileclose_bm] USED TO CARRY, and all
     three are PERSISTENT now, so there is no [sysc_bm_join] to write: the
     two superblock cells are DISCARDED for good (FsReady.v §0b) and the
     block bitmap lives in the invariant [BitmapInv.bitmap_inv], which no
     contract indexes by a used-set any more.  What used to be an exclusive
     resource threaded in and re-indexed out is now one [iDestruct] off the
     bundle, and an arm keeps its copy across the call it makes.

     Stated as a lemma only so no arm has to spell [fn]'s six field
     accessors, exactly as the old split did. *)
  Lemma sysc_bm_cells (pj : mword 64) (bn : bio_names) (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗
    sb_bmapstart ↦₄□ (mword_of_int (fcn_bmapstart fn) : mword 32) ∗
    InodeInv.sb_inodestart ↦₄□ (mword_of_int icfg_ist : mword 32) ∗
    bitmap_inv fsc_fs (fcn_bmapstart fn) fsc_cov fsc_logst
               (fcn_size fn).
  Proof.
    iIntros "#Hfs".
    iDestruct (sysc_fs_env_ties with "Hfs") as "%T".
    iDestruct "Hfs" as "(_ & _ & _ & _ & #Hrdy)".
    iDestruct (FsReady.fs_ready_sb_four with "Hrdy") as "(_ & #Hisp & _ & #Hbmp)".
    iDestruct (FsReady.fs_ready_bitmap with "Hrdy") as "#Hbmi".
    rewrite (sct_bmapstart _ _ _ T) (sct_size _ _ _ T).
    iSplitR; [ iExact "Hbmp" |].
    iSplitR; [ iExact "Hisp" |].
    iExact "Hbmi".
  Qed.

  (* [fn] REBUILT FROM ITS OWN ACCESSORS, which is what [sys_exit]'s
     [fn = MkFCloseNames ...] premise reduces to once every parameter it
     quantifies is instantiated at [fn]'s matching field.  Only three of the
     twenty-six are not already [fn]'s own: [bn] and [pid] are the ambient
     dispatch's, and the [1/4] is a literal -- so the premise IS record eta,
     modulo those three ties. *)
  Lemma sysc_fn_eta (fn : fclose_names) (bn : bio_names) (pid : mword 32) :
    fcn_bio fn = bn -> fcn_pid fn = pid -> fcn_dq fn = DfracOwn (1/4) ->
    fn = MkFCloseNames (fcn_procs fn) (fcn_j fn) (fcn_plock fn) (fcn_kmem fn)
           (fcn_kalloc fn) (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
           (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn
           pid (DfracOwn (1/4))
           (fcn_bmapstart fn) (fcn_size fn).
  Proof. intros <- <- <-. destruct fn; reflexivity. Qed.

  (* the dispatch carries [IREFSPARE] = 4 units of the inode-reference
     allowance; kexec's walk wants 2 and gives them back. *)
  Lemma sysc_iref_split : iref_slots IREFSPARE -∗ iref_slots 2 ∗ iref_slots 2.
  Proof. rewrite /IREFSPARE. iIntros "H". iApply (iref_slots_split 2 2 with "H"). Qed.

  (* ...and the 3/1 split sys_link's walk wants (it holds [ip] and [dp] at
     once, plus one in flight). *)
  Lemma sysc_iref_split3 : iref_slots IREFSPARE -∗ iref_slots 3 ∗ iref_slots 1.
  Proof. rewrite /IREFSPARE. iIntros "H". iApply (iref_slots_split 3 1 with "H"). Qed.

  Lemma sysc_iref_join3 : iref_slots 3 -∗ iref_slots 1 -∗ iref_slots IREFSPARE.
  Proof.
    rewrite /IREFSPARE. iIntros "H1 H2".
    iApply (iref_slots_combine 3 1 with "H1 H2").
  Qed.

  Lemma sysc_iref_join : iref_slots 2 -∗ iref_slots 2 -∗ iref_slots IREFSPARE.
  Proof.
    rewrite /IREFSPARE. iIntros "H1 H2".
    iApply (iref_slots_combine 2 2 with "H1 H2").
  Qed.

  (* the trap-CSR complement, at the index [syscall()] runs at: both halves
     are [emp] at [eb = true], so an arm mints them rather than threading
     them (IntrDefs.v's own [trap_csrs_ext]/[cpu_claim_ext]). *)
  Lemma sysc_trap_ext_true : ⊢ trap_csrs_ext KT1 true.
  Proof. rewrite /trap_csrs_ext. done. Qed.

  Lemma sysc_claim_ext_true (p : mword 64) : ⊢ cpu_claim_ext true p.
  Proof. rewrite /cpu_claim_ext. done. Qed.

  (* ===================================================================== *)
  (* THE DISPATCH TABLE.  syscalls[k], k = 1..22, straight out of KernelSyms
     (verified against kernel-rocq/KernelSyms.v). *)
  Definition sysc_target (k : nat) : Z :=
    match k with
    | 1%nat  => KernelSyms.sys_fork
    | 2%nat  => KernelSyms.sys_exit
    | 3%nat  => KernelSyms.sys_wait
    | 4%nat  => KernelSyms.sys_pipe
    | 5%nat  => KernelSyms.sys_read
    | 6%nat  => KernelSyms.sys_kill
    | 7%nat  => KernelSyms.sys_exec
    | 8%nat  => KernelSyms.sys_fstat
    | 9%nat  => KernelSyms.sys_chdir
    | 10%nat => KernelSyms.sys_dup
    | 11%nat => KernelSyms.sys_getpid
    | 12%nat => KernelSyms.sys_sbrk
    | 13%nat => KernelSyms.sys_pause
    | 14%nat => KernelSyms.sys_uptime
    | 15%nat => KernelSyms.sys_open
    | 16%nat => KernelSyms.sys_write
    | 17%nat => KernelSyms.sys_mknod
    | 18%nat => KernelSyms.sys_unlink
    | 19%nat => KernelSyms.sys_link
    | 20%nat => KernelSyms.sys_mkdir
    | 21%nat => KernelSyms.sys_close
    | 22%nat => KernelSyms.sys_sync
    | _  => 0
    end.

  (* the table's .rodata bytes, at a SYMBOLIC index -- proved once, applied
     22 times (mirrors [ProofArgraw.ar_table_word]/[ProcdumpAux.pd_states_word]:
     the lookup is a MATCH over 22 named literals rather than a uniform
     stride, but the [kernel_data_window] bridge is identical). *)
  Lemma sysc_tbl_bytes (k : nat) : (1 <= k <= 22)%nat ->
    forall j, (j < 8)%nat ->
      KernelData.kernel_data !! (KernelSyms.syscalls + 8 * Z.of_nat k + Z.of_nat j)%Z
        = Some (nth_byte (mword_of_int (sysc_target k) : mword 64) j).
  Proof.
    intros Hk j Hj.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]]; try lia;
      (destruct j as [|[|[|[|[|[|[|[|j']]]]]]]]; try lia;
       vm_compute; f_equal; apply bv_eq; reflexivity).
  Qed.

  Lemma sysc_table_word (k : nat) : (1 <= k <= 22)%nat ->
    kernel_data -∗
    (mword_of_int (KernelSyms.syscalls + 8 * Z.of_nat k) : mword 64)
      ↦₈□ (mword_of_int (sysc_target k) : mword 64).
  Proof.
    intro Hk.
    assert (Hle : text_end <= KernelSyms.syscalls + 8 * Z.of_nat k)
      by (unfold text_end, KernelSyms.syscalls; lia).
    assert (Hhi : KernelSyms.syscalls + 8 * Z.of_nat k + Z.of_nat 8%nat
                  <= rodata_end)
      by (unfold rodata_end, KernelSyms.syscalls; lia).
    pose proof (sysc_tbl_bytes k Hk) as Hb.
    iIntros "#Hd". rewrite /word_pointsto. iSplit.
    { iPureIntro. destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]];
        try lia; vm_compute; reflexivity. }
    iApply (kernel_data_window (KernelSyms.syscalls + 8 * Z.of_nat k)
              (mword_of_int (sysc_target k) : mword 64) 8%nat _ eq_refl
              Hle Hhi Hb with "Hd").
  Qed.

  (* every table entry is nonzero *)
  Lemma sysc_target_nz (k : nat) : (1 <= k <= 22)%nat ->
    (mword_of_int (sysc_target k) : mword 64) <> zero_reg.
  Proof.
    intro Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]]; try lia;
      (intro Hc; apply (f_equal (@bv_unsigned _)) in Hc; vm_compute in Hc; discriminate).
  Qed.

  (* ===================================================================== *)
  (* THE FUSED RANGE CHECK.  [c.addiw a5,a5,-1] then [bltu a4,a5] with
     a4 = 21: fall-through (real dispatch) iff [unsigned(num-1) <= 21], i.e.
     [1 <= num <= 22].  [num] is the sign-extended 32-bit trapframe word.

     [subrange_vec_dec]'s UNSIGNED characterization mirrors
     [KptPt.subrange64_unsigned_11_0] (width 32 instead of 12); the SIGNED
     one is then free from [bv_signed]'s own definition
     ([bv_signed w := bv_swrap n (bv_unsigned w)]) plus [bv_swrap_wrap]. *)
  Local Lemma sysc_subrange31_0_unsigned (Y : mword 64) :
    bv_unsigned (subrange_vec_dec Y 31 0 : mword 32) = bv_wrap 32 (bv_unsigned Y).
  Proof.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    rewrite Z.shiftr_0_r.
    change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
    reflexivity.
  Qed.

  Local Lemma sysc_subrange31_0_signed (Y : mword 64) :
    bv_signed (subrange_vec_dec Y 31 0 : mword 32) = bv_swrap 32 (bv_unsigned Y).
  Proof.
    unfold bv_signed. rewrite sysc_subrange31_0_unsigned. apply bv_swrap_wrap.
  Qed.

  (* the low 32 bits of [add_vec num C], as an UNSIGNED quantity, via
     [bv_add_unsigned] -- then re-expressed SIGNED via [bv_swrap]'s
     definition and [sysc_subrange31_0_signed]. *)
  Local Lemma sysc_addiw_signed (num : mword 64) :
    bv_signed (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
                 (mword_of_int 63 : mword 6)))) 31 0 : mword 32)
    = bv_swrap 32 (bv_wrap 64 (bv_unsigned num + 18446744073709551615)).
  Proof.
    rewrite sysc_subrange31_0_signed bv_add_unsigned.
    assert (HC : bv_unsigned (sign_extend' 64 (sign_extend' 12
                   (mword_of_int 63 : mword 6)) : mword 64) = 18446744073709551615)
      by (vm_compute; reflexivity).
    rewrite HC. reflexivity.
  Qed.

  (* [bv_unsigned num] re-expressed as [bv_wrap 64 (bv_signed num)]:
     [bv_signed] is [bv_swrap] of the unsigned value, [bv_wrap_swrap]
     (RiscvExtras.v) undoes the swrap, and [bv_wrap] of an ALREADY-in-range
     value is the identity. *)
  Local Lemma sysc_unsigned_of_signed (num : mword 64) :
    bv_unsigned num = bv_wrap 64 (bv_signed num).
  Proof.
    unfold bv_signed. rewrite bv_wrap_swrap.
    symmetry. apply bv_wrap_bv_unsigned.
  Qed.

  (* the cross-width collapse, generalized with an extra additive constant:
     wrapping at 64 before adding [C] and swrapping at 32 is the same as
     adding [C] to the un-wrapped value and swrapping at 32 directly --
     32 divides 64, so the outer 32-wrap only ever sees the value mod 2^32,
     which the inner 64-wrap does not disturb ([bv_wrap_bv_wrap]). *)
  Local Lemma sysc_mod32_wrap64_add (W Ceff : Z) :
    (bv_wrap 64 W + Ceff) mod (bv_modulus 32) = (W + Ceff) mod (bv_modulus 32).
  Proof.
    rewrite (Zplus_mod (bv_wrap 64 W) Ceff) (Zplus_mod W Ceff).
    change (bv_wrap 64 W mod bv_modulus 32) with (bv_wrap 32 (bv_wrap 64 W)).
    change (W mod bv_modulus 32) with (bv_wrap 32 W).
    rewrite (bv_wrap_bv_wrap 32%N 64%N W ltac:(lia)).
    reflexivity.
  Qed.

  (* the plain (no extra additive constant) form: [sysc_addiw_signed]'s own
     RHS shape, [bv_swrap 32 (bv_wrap 64 (...))], needs this first before
     [sysc_swrap32_wrap64_add] can peel the INNER wrap. *)
  Local Lemma sysc_swrap32_wrap64 (W : Z) :
    bv_swrap 32 (bv_wrap 64 W) = bv_swrap 32 W.
  Proof.
    unfold bv_swrap. f_equal.
    exact (sysc_mod32_wrap64_add W (bv_half_modulus 32)).
  Qed.

  Local Lemma sysc_swrap32_wrap64_add (W C : Z) :
    bv_swrap 32 (bv_wrap 64 W + C) = bv_swrap 32 (W + C).
  Proof.
    unfold bv_swrap.
    replace (bv_wrap 64 W + C + bv_half_modulus 32)%Z
      with (bv_wrap 64 W + (C + bv_half_modulus 32))%Z by ring.
    replace (W + C + bv_half_modulus 32)%Z
      with (W + (C + bv_half_modulus 32))%Z by ring.
    unfold bv_wrap at 1 3.
    rewrite (sysc_mod32_wrap64_add W (C + bv_half_modulus 32)).
    reflexivity.
  Qed.

  (* periodicity: adding a multiple of the 32-bit modulus never changes
     [bv_swrap 32 _] -- the [bv_swrap] analogue of [bv_wrap_add_modulus]. *)
  Local Lemma sysc_swrap32_add_modulus (c z : Z) :
    bv_swrap 32 (z + c * bv_modulus 32) = bv_swrap 32 z.
  Proof.
    unfold bv_swrap.
    replace (z + c * bv_modulus 32 + bv_half_modulus 32)%Z
      with (z + bv_half_modulus 32 + c * bv_modulus 32)%Z by ring.
    rewrite bv_wrap_add_modulus. reflexivity.
  Qed.

  (* THE CLEAN FORM: the c.addiw result's SIGNED value is exactly
     [bv_swrap 32 (bv_signed num - 1)] -- the 32-bit int-decrement C
     semantics, chained through every bridge above. *)
  Local Lemma sysc_addiw_signed_clean (num : mword 64) :
    bv_signed (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
                 (mword_of_int 63 : mword 6)))) 31 0 : mword 32)
    = bv_swrap 32 (bv_signed num - 1).
  Proof.
    rewrite sysc_addiw_signed (sysc_unsigned_of_signed num) sysc_swrap32_wrap64
            sysc_swrap32_wrap64_add.
    replace (bv_signed num + 18446744073709551615)%Z
      with (bv_signed num - 1 + 4294967296 * bv_modulus 32)%Z
      by (unfold bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z; ring).
    apply sysc_swrap32_add_modulus.
  Qed.

  (* mirrors [ProofArgfd.af_sext_uint] exactly, at this file's own bound
     variable name. *)
  Local Lemma sysc_sext_uint (w : mword 32) :
    uint (sign_extend' 64 w : mword 64) = bv_wrap 64 (bv_signed w).
  Proof. rewrite uint_unsigned sext32_64_moi. apply moi64_unsigned. Qed.

  Lemma sysc_bltu_fall (num : mword 64) :
    (1 <= bv_signed num <= 22)%Z ->
    zopz0zI_u (mword_of_int 21 : mword 64)
      (sign_extend' 64 (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
         (mword_of_int 63 : mword 6)))) 31 0)) = false.
  Proof.
    intro Hr. unfold zopz0zI_u. apply Z.ltb_ge.
    rewrite (sysc_sext_uint (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
      (mword_of_int 63 : mword 6)))) 31 0)).
    assert (H21 : uint (mword_of_int 21 : mword 64) = 21) by (vm_compute; reflexivity).
    rewrite H21 sysc_addiw_signed_clean.
    rewrite (bv_swrap_small 32 (bv_signed num - 1) ltac:(unfold bv_half_modulus, bv_modulus;
      change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z; lia)).
    rewrite (bv_wrap_small 64 (bv_signed num - 1) ltac:(unfold bv_modulus;
      change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; lia)).
    lia.
  Qed.

  Lemma sysc_bltu_taken (num : mword 64) :
    ~ (1 <= bv_signed num <= 22)%Z ->
    (-2147483648 <= bv_signed num < 2147483648)%Z ->
    zopz0zI_u (mword_of_int 21 : mword 64)
      (sign_extend' 64 (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
         (mword_of_int 63 : mword 6)))) 31 0)) = true.
  Proof.
    intros Hr Hrange. unfold zopz0zI_u. apply Z.ltb_lt.
    rewrite (sysc_sext_uint (subrange_vec_dec (add_vec num (sign_extend' 64 (sign_extend' 12
      (mword_of_int 63 : mword 6)))) 31 0)).
    assert (H21 : uint (mword_of_int 21 : mword 64) = 21) by (vm_compute; reflexivity).
    rewrite H21 sysc_addiw_signed_clean.
    destruct (Z_le_gt_dec (-2147483648) (bv_signed num - 1)) as [Hlo | Hlo].
    - (* no wraparound in the 32-bit decrement: swrap is the identity *)
      rewrite (bv_swrap_small 32 (bv_signed num - 1) ltac:(unfold bv_half_modulus, bv_modulus;
        change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z; lia)).
      destruct (Z_lt_le_dec (bv_signed num - 1) 0) as [Hneg | Hpos].
      + (* negative: the 64-bit wrap adds the full 2^64 back, far above 21 *)
        rewrite <- (bv_wrap_add_modulus 1 64 (bv_signed num - 1)).
        rewrite (bv_wrap_small 64 (bv_signed num - 1 + 1 * bv_modulus 64)
                   ltac:(unfold bv_modulus;
                     change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; lia)).
        unfold bv_modulus in *; change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *.
        lia.
      + (* nonnegative and not in [1,22]: strictly above 22 *)
        rewrite (bv_wrap_small 64 (bv_signed num - 1) ltac:(unfold bv_modulus;
          change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; lia)).
        lia.
    - (* the one wraparound point: [bv_signed num = -2^31], so the C
         decrement overflows to [2^31 - 1] -- still, trivially, far above
         21. *)
      assert (Hnum : bv_signed num = -2147483648) by lia.
      rewrite Hnum.
      replace (-2147483648 - 1)%Z with (2147483647 + (-1) * bv_modulus 32)%Z
        by (unfold bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z; ring).
      rewrite sysc_swrap32_add_modulus.
      rewrite (bv_swrap_small 32 2147483647 ltac:(unfold bv_half_modulus, bv_modulus;
        change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z; lia)).
      rewrite (bv_wrap_small 64 2147483647 ltac:(unfold bv_modulus;
        change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; lia)).
      lia.
  Qed.

  (* =================================================================== *)
  (* THE BRIDGE FROM THE RAW a7 LOAD TO THE C `int num` TRUNCATION.
     [sysc_bltu_fall]/[sysc_bltu_taken] above are stated at a "num" that
     must ALREADY be a sign-extended 32-bit quantity (their own doc
     comment: "[num] is the sign-extended 32-bit trapframe word") --
     [sysc_bltu_taken]'s extra [-2^31 <= bv_signed num < 2^31] hypothesis
     is otherwise unmeetable for an arbitrary (user-controlled) 64-bit a7
     load.  The REAL [c.addiw a5,a5,-1] at +0x1e reads the RAW a5 (the
     unmodified a7 load, call it [RAWNUM]) -- so applying those two lemmas
     needs this bridge: the low 32 bits of [RAWNUM + C] depend only on the
     low 32 bits of [RAWNUM], hence agree with those of
     [sext32(RAWNUM) + C], for ANY additive constant [C]. *)
  Local Lemma sysc_wrap32_add_indep (x y C : Z) :
    bv_wrap 32 x = bv_wrap 32 y ->
    bv_wrap 32 (x + C) = bv_wrap 32 (y + C).
  Proof. intro Heq. unfold bv_wrap in *. rewrite (Zplus_mod x C) (Zplus_mod y C) Heq. reflexivity. Qed.

  Lemma sysc_a3_bltu_bridge (RAWNUM C : mword 64) :
    subrange_vec_dec (add_vec (sign_extend' 64 (subrange_vec_dec RAWNUM 31 0 : mword 32)) C) 31 0
    = subrange_vec_dec (add_vec RAWNUM C) 31 0.
  Proof.
    apply bv_eq.
    rewrite (sysc_subrange31_0_unsigned (add_vec (sign_extend' 64 (subrange_vec_dec RAWNUM 31 0 : mword 32)) C))
            (sysc_subrange31_0_unsigned (add_vec RAWNUM C))
            !bv_add_unsigned
            (bv_wrap_bv_wrap 32%N 64%N _ ltac:(lia)) (bv_wrap_bv_wrap 32%N 64%N _ ltac:(lia)).
    apply sysc_wrap32_add_indep.
    rewrite <- uint_unsigned, (sysc_sext_uint (subrange_vec_dec RAWNUM 31 0)),
            (sysc_subrange31_0_signed RAWNUM), (bv_wrap_bv_wrap 32%N 64%N _ ltac:(lia)).
    unfold bv_signed. rewrite bv_wrap_swrap. reflexivity.
  Qed.

  (* the a3 VALUE ITSELF, as a clean [mword_of_int (bv_signed a3num)] --
     used to identify a3's register content with the nat index [k] every
     later address computation and the table lemmas key off of. *)
  Lemma sysc_a3_val (a3num : mword 64) :
    (1 <= bv_signed a3num <= 22)%Z ->
    a3num = mword_of_int (bv_signed a3num).
  Proof. intro Hr. apply bv_eq. rewrite moi64_unsigned. apply sysc_unsigned_of_signed. Qed.

  (* NOTE: a helper bounding a3's signed value into 32-bit range (needed
     to apply [sysc_bltu_taken] on the out-of-range dispatch path) was
     attempted here and pulled back out -- see STATUS at the top of this
     file.  Left for a future session: [sysc_bltu_taken]'s own
     [-2^31 <= bv_signed num < 2^31] premise is satisfiable at
     [num := sign_extend' 64 (subrange_vec_dec RAWNUM 31 0)] for the SAME
     reason [sysc_a3_val] holds (sign-extension of a 32-bit value), via
     [stdpp.bitvector.bv_signed_in_range] plus [bv_swrap_wrap] --
     the derivation is straightforward on paper but needs one more
     round-trip to pin the exact rewrite that isn't firing here.

     the table-address computation ([slli a4,a3,3]/[auipc a5,5]/
     [addi a5,a5,3818]/[add a5,a5,a4]), symbolic in the nat index [k] --
     mirrors [sysc_tbl_bytes]/[sysc_target_nz]'s own 22-way destruct, kept
     as ONE small lemma rather than re-derived per arm. *)
  Lemma sysc_addr_word (k : nat) : (1 <= k <= 22)%nat ->
    add_vec (mword_of_int KernelSyms.syscalls : mword 64)
      (shift_bits_left (mword_of_int (Z.of_nat k) : mword 64)
         (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
    = mword_of_int (KernelSyms.syscalls + 8 * Z.of_nat k).
  Proof.
    intro Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]]; try lia;
      apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* trapframe page validity, read off [proc_priv] without consuming it --
     mirrors [ProofUsertrapSys.ut_tfp_valid] (a [Local] lemma there, so
     re-derived here rather than imported). *)
  Lemma sysc_tfp_valid (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜page_valid (page_base (ud_tfp (pv_upt V)))⌝.
  Proof.
    iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
    iDestruct (proc_pt_wf_get with "Hptt") as "%Hwf".
    iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  (* =================================================================== *)
  (* THE SHARED DISPATCH-ARM VOCABULARY.  Every RETURNING table entry,
     once its own [SysXxx.wp_sys_xxx_sconf] resolves, hands back exactly
     what [wp_syscall_sconf_body]'s own continuation wants -- mirrors
     [UsertrapRes.ut_own]'s five shared families plus [proc_priv]/[R] (see
     the file header). *)

  (* the state a RETURNING arm needs before it can start: [pc_is] at the
     table entry's own known address, plus every resource
     [wp_syscall_sconf_body] threads opaquely through the dispatch. *)
  Definition sysc_arm_pre `{CIDh : CpuId} (γf : gname) (pj : mword 64) (γs : list gname)
      (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (M : regfile)
      (tgt : mword 64) :=
    (pc_is tgt ∗
     sie_cap_gpr KT1 M av true pj ∗
     cpu_own 0%nat true pj true lks ∗
     kernel_text ∗
     (* the proc array and the panic arms every [acquire]/[release] in the
        cone reaches -- both persistent, both already held by the capstone,
        and between them what most table entries need beyond [proc_priv] *)
     procs_inv γs ∗
     syscall_env γf pj bn fn ∗
     bslots 3 ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv γf pj pid V ∗
     (* the descriptor-state fragments, on the same in-and-out channel as
        the three allowances: four entries retype a descriptor and spend
        them (open, close, pipe, dup); the rest hand them straight back. *)
     fd_frags_any (pv_fdg V))%I.

  (* Build the arm bundle structurally, while its proof context contains only
     the twelve resources being assembled.  In the capstone below, even a
     named [iFrame] searches the goal's conjuncts; its final [proc_priv]
     contains the 4096-word trapframe page, making that search seconds long. *)
  Lemma sysc_arm_pre_intro `{CIDh : CpuId}
      (γf : gname) (pj : mword 64) (γs : list gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (M : regfile)
      (tgt : mword 64) :
    pc_is tgt -∗
    sie_cap_gpr KT1 M av true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    procs_inv γs -∗
    syscall_env γf pj bn fn -∗
    bslots 3 -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗
    iref_slots IREFSPARE -∗
    proc_priv γf pj pid V -∗
    fd_frags_any (pv_fdg V) -∗
    sysc_arm_pre γf pj γs bn fn dqi ip pid V lks av M tgt.
  Proof.
    iIntros "Hpc Hcg Hcpu Htext Hprocs HR Hbs Hip Hfd Hir Hpriv Hufrag".
    rewrite /sysc_arm_pre.
    iSplitL "Hpc"; [iExact "Hpc" |].
    iSplitL "Hcg"; [iExact "Hcg" |].
    iSplitL "Hcpu"; [iExact "Hcpu" |].
    iSplitL "Htext"; [iExact "Htext" |].
    iSplitL "Hprocs"; [iExact "Hprocs" |].
    iSplitL "HR"; [iExact "HR" |].
    iSplitL "Hbs"; [iExact "Hbs" |].
    iSplitL "Hip"; [iExact "Hip" |].
    iSplitL "Hfd"; [iExact "Hfd" |].
    iSplitL "Hir"; [iExact "Hir" |].
    iSplitL "Hpriv"; [iExact "Hpriv" |].
    iExact "Hufrag".
  Qed.

  (* the OUTER [wp_syscall_sconf_body]'s own continuation, named so every
     arm/the epilogue can take it as an explicit parameter rather than
     restate it -- [V]/[m] here are the WHOLE FUNCTION's entry values,
     fixed for the whole proof; only [mf]/[V'] vary per return. *)
  Definition sysc_hcont_ty `{CIDh : CpuId} (γf : gname) (pj : mword 64) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (m : regfile)
      (ret_tgt : mword 64) : iProp Σ :=
    wp_next true pj (fun (CID : CpuId) =>
      (∀ (mf : regfile) (V' : pprivate),
        ⌜ callee_saved m mf ⌝ -∗
        ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
        (* ...and the fd-state ghost name -- see SpecSyscall.v's note: no
           syscall reassigns a live process's [pv_fdg], so the bundle is
           stated at the ENTRY record and this equation re-keys it. *)
        ⌜ pv_fdg V' = pv_fdg V ⌝ -∗
        sie_cap_gpr KT1 mf av true pj -∗
        cpu_own 0%nat true pj true lks -∗
        bslots 3 -∗
        (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
        fd_slots FDSPARE -∗
        iref_slots IREFSPARE -∗
        syscall_env γf pj bn fn -∗
        proc_priv γf pj pid V' -∗
        fd_frags_any (pv_fdg V) -∗
        pc_is ret_tgt -∗
        WP (Loop : expr riscv_lang))%I).

  (* THE EXIT SLOT, as the dispatch sees it: the caller's return
     continuation AND, additively, a closer for the kernel stack.  See
     SpecSyscall.v's own note for why [∧] and not [∗] or [∨] -- in one line,
     the caller funds both branches out of the same frame cells and the
     CALLEE picks, because the pick is the syscall number.

     A RETURNING ARM'S FIRST MOVE IS [iDestruct "Hcont" as "[Hcont _]"],
     after which it is written exactly as it was before this slot existed --
     [sysc_ret_tail], [sysc_epilogue_tail] and [sysc_fallback] still take the
     bare [wp_next] and never learn that the conjunction happened. *)
  Definition sysc_exit_ty `{CIDh : CpuId} (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m : regfile) (ret_tgt : mword 64) : iProp Σ :=
    (sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m ret_tgt
     ∧ kstack_closer pj (m !!! Regidx csp_rs1) (trap_res true + av))%I.

  (* the crossing, for the whole slot.  Only the LEFT conjunct is
     hart-indexed: [ProcDefs] names no [CpuId] at all (nor does [StackOwn]),
     so [kstack_closer] crosses a migration untouched and the right branch is
     a bare re-assertion. *)
  Lemma sysc_exit_retarget (CID0 CID1 : CpuId) (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m : regfile) (ret_tgt : mword 64) :
    (true = false \/ pj = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
    sysc_exit_ty (CIDh := CID0) γf pj bn fn dqi ip pid V lks av m ret_tgt -∗
    sysc_exit_ty (CIDh := CID1) γf pj bn fn dqi ip pid V lks av m ret_tgt.
  Proof.
    intro Hcr. iIntros "H". rewrite /sysc_exit_ty. iSplit.
    - iDestruct "H" as "[H _]".
      iApply (wp_next_retarget CID0 CID1 true pj _ Hcr with "H").
    - iDestruct "H" as "[_ $]".
  Qed.

  (* the stack-slot arithmetic ([pa_stk sp0 j] as an offset from the
     PUSHED sp [pa_stk sp0 4]) -- mirrors [ProofArgraw.ar_stk] exactly
     (that one is local to ProofArgraw.v's own section, hence re-derived
     here rather than imported). *)
  Lemma sysc_stk (sp0 : mword 64) (j u : nat) :
    (j + u = 4)%nat -> (u < 4)%nat ->
    pa_stk sp0 j = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000"))).
  Proof.
    intros Hju Hu.
    destruct u as [|[|[|[|]]]]; try lia; destruct j as [|[|[|[|[|]]]]]; try lia;
      unfold pa_stk, add_vec_int; rewrite add_vec_off2;
      f_equal; apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* what an ARM must prove, at its OWN table index [k]: from the
     pre-jump state plus the caller's four saved stack cells, hand
     [Hcont] the eventual return.  [M]'s sp is tied to the function's
     TRUE entry [m] via [pa_stk] (NOT equality: [M] is still INSIDE the
     pushed frame here) -- but [M]'s s0/s1/s2 are NOT tied to [m]'s own:
     syscall() itself REUSES them as locals (s0 := the frame pointer,
     s1 := [p], s2 := [p->trapframe]), restored from the STACK (not from
     a live-register invariant) only by [sysc_epilogue_tail]'s own
     reloads.  What every RETURNING arm DOES need is [M]'s s2 value, to
     store its own return value at [p->trapframe->a0] before reaching the
     epilogue -- exposed here as the trapframe-pointer equation, tied to
     the SAME [V] the arm's own [proc_priv] call already carries.  [av]
     is the WHOLE FUNCTION's own budget; the arm's own [sie_cap_gpr] runs
     at [av - 4] (syscall's own 4-slot frame cost, restored only at the
     final pop inside [sysc_epilogue_tail]) -- mirrors [ProofSysGetpid]/
     [ProofArgraw]'s own "(av-k)...+k=av" bookkeeping.  [sys_exit] (table
     index 2)'s own contract DIVERGES (no continuation at all --
     SpecSysExit.v), so it does not fit this shape and has its own arm at a
     bespoke type. *)
  Definition sysc_arm_goal `{CIDh : CpuId} (k : nat) (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) : Prop :=
    (* WHICH process this is, in the vocabulary the per-process entries state
       their own contracts in: [sys_wait]/[sys_kill]/[sys_pause]/... take the
       proc array's ghost names and an INDEX, and address the running process
       as [proc_addr j] rather than as an opaque pointer.  All three come
       straight off [wp_syscall_sconf_body]'s own binder list. *)
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    pj = proc_addr j ->
    M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    M !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)) ->
    (* WHERE THE CALLEE RETURNS TO.  The [c.jalr] wrote [syscall + 0x3a] into
       [ra] just before the jump, and every entry's own contract answers at
       [ret_pc (its own entry [ra])] -- so without this the arm cannot even
       say which instruction runs next.  [ra] is NOT callee-saved, so the
       clause above says nothing about it. *)
    M !!! Regidx Rra = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64) ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       M !!! Regidx r = m !!! Regidx r) ->
    (K_syscall <= av)%nat ->
    (* the tie [syscall_env]'s indices cannot reach -- SpecSyscall.v's note *)
    fcn_pid fn = pid ->
    sysc_arm_pre γf pj γs bn fn dqi ip pid V lks (av - 4)%nat M (mword_of_int (sysc_target k)) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    kernel_data -∗
    sysc_exit_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* THE SHARED EPILOGUE TAIL: +0x58 (first reload) through +0x62
     ([c.jr ra]), reused by every returning arm AND the printk fallback --
     both of those have already done their own store to
     [p->trapframe->a0] before reaching here, so this piece never touches
     memory at all, only the frame.  Only [E]'s sp needs to be tied to
     [m] (via [pa_stk], to compute the reload addresses): s0/s1/s2 are
     NOT ([syscall()] reuses them as locals, per [sysc_arm_goal]'s own
     comment) -- they are recovered from the STACK CELLS below, whose
     content is [m]'s own saved values by construction, regardless of
     what [E] currently holds live.  [E]'s own [sie_cap_gpr] is at
     [av - 4], same convention as [sysc_arm_goal]. *)
  Lemma sysc_epilogue_tail
      (γf : gname) (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      (dqi : dfrac) (ip : mword 64) (pid : mword 32) (V V' : pprivate)
      (lks : gset string) (av : nat)
      (m E : regfile) :
    E !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       E !!! Regidx r = m !!! Regidx r) ->
    (4 <= av)%nat ->
    ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ->
    (* ...and the fd-state ghost name, which no syscall moves *)
    pv_fdg V' = pv_fdg V ->
    sie_cap_gpr KT1 E (av - 4)%nat true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    bslots 3 -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
    syscall_env γf pj bn fn -∗ proc_priv γf pj pid V' -∗
    fd_frags_any (pv_fdg V) -∗
    pc_is (mword_of_int (KernelSyms.syscall + 0x58) : mword 64) -∗
    sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HEsp Hrest Hav4 Hud Hfg.
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hcpu #Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir HR Hpriv Hufrag Hpc Hcont".
    assert (Hb1 : pa_stk sp0 1 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 1 3); lia).
    assert (Hb2 : pa_stk sp0 2 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 2 2); lia).
    assert (Hb3 : pa_stk sp0 3 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 3 1); lia).
    assert (Hb4 : pa_stk sp0 4 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 4 0); lia).
    (* +0x58: c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x58)) (mword_of_int 3 : mword 6) Rra
              E (av - 4)%nat (m !!! Regidx Rra) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hra]").
    { iApply (syci_58 with "Htext"). }
    { iEval (rewrite HEsp -Hb1). iExact "Hra". }
    iIntros (CID1 Hst1) "Hcg Hpc Hra".
    set (T1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E) with T1.
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [rewrite HEsp; reflexivity | vm_compute; discriminate]).
    (* +0x5a: c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5a)) (mword_of_int 2 : mword 6) Rs0
              T1 (av - 4)%nat (m !!! Regidx Rs0) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs0]").
    { iApply (syci_5a with "Htext"). }
    { iEval (rewrite HT1sp -Hb2). iExact "Hs0". }
    iIntros (CID2 Hst2) "Hcg Hpc Hs0".
    set (T2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1) with T2.
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.syscall + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* +0x5c: c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5c)) (mword_of_int 1 : mword 6) Rs1
              T2 (av - 4)%nat (m !!! Regidx Rs1) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs1]").
    { iApply (syci_5c with "Htext"). }
    { iEval (rewrite HT2sp -Hb3). iExact "Hs1". }
    iIntros (CID3 Hst3) "Hcg Hpc Hs1".
    set (T3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2).
    change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2) with T3.
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    (* +0x5e: c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5e)) (mword_of_int 0 : mword 6) Rs2
              T3 (av - 4)%nat (m !!! Regidx Rs2) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs2]").
    { iApply (syci_5e with "Htext"). }
    { iEval (rewrite HT3sp -Hb4). iExact "Hs2". }
    iIntros (CID4 Hst4) "Hcg Hpc Hs2".
    set (T4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> T3).
    change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> T3) with T4.
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    (* +0x60: c.addi16sp sp,32 -- the frame pop *)
    assert (Hup : add_vec (pa_stk sp0 4) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      assert (HAB : add_vec (mword_of_int (-8 * 4)%Z : mword 64)
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply kv_addv_zero. }
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HT4sp; exact Hup).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HT4sp; reflexivity).
    iEval (rewrite HEsp -Hb1) in "Hra". iEval (rewrite HT1sp -Hb2) in "Hs0".
    iEval (rewrite HT2sp -Hb3) in "Hs1". iEval (rewrite HT3sp -Hb4) in "Hs2".
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hra Hs0 Hs1 Hs2]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hra". { iExists _. iExact "Hra". }
      iSplitL "Hs0". { iExists _. iExact "Hs0". }
      iSplitL "Hs1". { iExists _. iExact "Hs1". }
      iSplitL "Hs2". { iExists _. iExact "Hs2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.syscall + 0x60)) (mword_of_int 2 : mword 6) T4
              (av - 4)%nat 4 true Hpop
              with "Hcg Hpc [] Hframe4").
    { iApply (syci_60 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4) with T5.
    assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* +0x62: c.jr ra *)
    assert (HT5ra : T5 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.syscall + 0x62)) Rra T5 av true
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (syci_62 with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    assert (Hrafinal : ret_pc (T5 !!! Regidx Rra) = ret_pc (m !!! Regidx Rra)) by (rewrite HT5ra; reflexivity).
    iEval (rewrite Hrafinal) in "Hpc".
    (* the postcondition -- sp/s0/s1/s2 restored to [m]'s own; everything
       else in [callee_saved m T5] came along for the ride via [E]'s own
       tie to [m] on those four registers plus [T5]'s upd-chain never
       touching any other register. *)
    assert (HT5sp : T5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1) by (rewrite /T5 upd_eq; exact Hwv).
    assert (HT5s0 : T5 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq. reflexivity. }
    assert (HT5s1 : T5 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq. reflexivity. }
    assert (HT5s2 : T5 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq. reflexivity. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                     T5 !!! Regidx r = E !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence]. reflexivity. }
    iSpecialize ("Hcont" $! CID6 with "[%]").
    { intro Hd. destruct Hd as [Hbad | Hgood]; [discriminate Hbad|].
      rewrite (Hst6 (or_intror Hgood)) (Hst5 (or_intror Hgood)) (Hst4 (or_intror Hgood))
              (Hst3 (or_intror Hgood)) (Hst2 (or_intror Hgood)) (Hst1 (or_intror Hgood)).
      reflexivity. }
    iApply ("Hcont" $! T5 V' with "[%] [%] [%] Hcg Hcpu Hbs Hip Hfd Hir HR Hpriv Hufrag Hpc").
    { unfold callee_saved.
      split_and!.
      - exact HT5sp.
      - exact HT5s0.
      - exact HT5s1.
      - exact HT5s2.
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate].
      - rewrite Hthr; [(apply Hrest; vm_compute; first [reflexivity | discriminate]) | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate]. }
    { exact Hud. }
    exact Hfg.
  Qed.

  (* the jalr's target, at a symbolic table index -- [ret_pc] is the
     identity on every [sysc_target k] (all even/2-aligned instruction
     addresses); mirrors [sysc_tbl_bytes]/[sysc_target_nz]'s own 22-way
     destruct. *)
  Lemma sysc_target_ret_pc (k : nat) : (1 <= k <= 22)%nat ->
    ret_pc (mword_of_int (sysc_target k) : mword 64) = mword_of_int (sysc_target k).
  Proof.
    intro Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]]; try lia;
      apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* [p->trapframe->a0]'s address, in the two spellings that have to meet:
     what the [sd a0,112(s2)] leaf computes from the base register, and what
     [ProcInv.tf_page_word_upd_mem] hands out.  Same shape (and same proof) as
     [ProofPrepareReturnParts.prr_tf_addr_00]'s family, at the ARGUMENT index
     rather than a kernel slot: [tf_arg_idx 0 = 14] and [8 * 14 = 112]. *)
  Lemma sysc_tf_addr_112 (tfp : mword 44) :
    add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 112 : mword 12))
    = tf_pa tfp (8 * Z.of_nat (tf_arg_idx 0)).
  Proof.
    assert (Hse : (sign_extend' 64 (mword_of_int 112 : mword 12) : mword 64)
                  = (mword_of_int 112 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hse.
    rewrite (tf_pa_eq_pa_add8 tfp (tf_arg_idx 0) ltac:(vm_compute; lia)).
    rewrite /pa_add /tf_arg_idx. f_equal.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PRINTK FALLBACK'S VOCABULARY.                                     *)

  Lemma sysc_fmt_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int sysc_fmt_a : mword 64) ↦ₛ□ sysc_fmt.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string sysc_fmt_a sysc_fmt _ eq_refl
              ltac:(unfold text_end, sysc_fmt_a; lia)
              ltac:(vm_compute; discriminate) sysc_fmt_bytes with "Hd").
  Qed.

  (* [p->name]'s sixteen bytes as a byte CURSOR from its own base -- the
     bridge [pname_cells] (element-indexed) needs before it can meet
     [string_pointsto] (cursor-indexed).  Mirrors ProofKforkParts'
     [kfk_name_addr], re-derived here rather than importing a proof file. *)
  Lemma sysc_name_addr (pa : mword 64) (i : nat) :
    pa_add (p_name pa 0) i = p_name pa i.
  Proof.
    unfold pa_add, p_name.
    change (add_vec pa (mword_of_int (344 + Z.of_nat 0))) with (add_vec_int pa 344).
    rewrite avi_assoc. reflexivity.
  Qed.

  (* the sixteen raw bytes, SPLIT at the NUL: a real C string in front,
     whatever gcc left behind it.  Over [pname_bytes], the bare big-op --
     [pname_cells] now carries [ProcGeom.pname_wf] as well, and this lemma is
     the byte-level half. *)
  Lemma sysc_pname_app (pa : mword 64) (dq : dfrac) (nm : string) (pad : list (bv 8)) :
    pname_bytes pa dq (List.app (cstring_bytes nm) pad) ⊣⊢
    (p_name pa 0 ↦ₛ{dq} nm ∗
     [∗ list] i ↦ b ∈ pad, p_name pa (length (cstring_bytes nm) + i) ↦ₘ{dq} b).
  Proof.
    rewrite /pname_bytes big_sepL_app /string_pointsto.
    apply bi.sep_proper; [| reflexivity].
    apply big_sepL_proper. intros k x Hk. by rewrite sysc_name_addr.
  Qed.

  (* [&p->name] is never null: the proc array sits far above 0, exactly as
     [ProcGeom.proc_addr_nonzero] says of its base. *)
  Lemma sysc_name_unsigned (i : nat) : (i < NPROC)%nat ->
    bv_unsigned (p_name (proc_addr i) 0)
    = KernelSyms.proc + proc_size * Z.of_nat i + 344.
  Proof.
    intro Hi. assert (Hi' := Hi). unfold NPROC in Hi'.
    unfold p_name.
    rewrite add_vec64_unsigned (proc_addr_unsigned i Hi) moi64_unsigned.
    rewrite bv_wrap_add_idemp_r.
    apply bv_wrap_small.
    unfold KernelSyms.proc, proc_size. rewrite bv_modulus64. lia.
  Qed.

  Lemma sysc_name_nonzero (i : nat) : (i < NPROC)%nat ->
    eq_vec (p_name (proc_addr i) 0) (zero_reg : mword 64) = false.
  Proof.
    intro Hi. apply eq_vec_false_iff. intro Hc.
    assert (Hz : bv_unsigned (p_name (proc_addr i) 0) = 0)
      by (rewrite Hc; vm_compute; reflexivity).
    rewrite (sysc_name_unsigned i Hi) in Hz.
    unfold KernelSyms.proc, proc_size in Hz. lia.
  Qed.

  (* [proc_priv_name]'s give-back, at the SAME byte list -- so a reader that
     hands the sixteen bytes straight back gets [V] itself, not
     [upd_name V (pv_name V)]. *)
  Lemma sysc_upd_name_id (V : pprivate) : upd_name V (pv_name V) = V.
  Proof. by destruct V. Qed.

  Lemma sysc_priv_name (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    ⌜length (pv_name V) = PNAMELEN⌝ ∗
    pname_cells pa (DfracOwn 1) (pv_name V) ∗
    (pname_cells pa (DfracOwn 1) (pv_name V) -∗ proc_priv γf pa pid V).
  Proof.
    iIntros "Hp".
    iDestruct (proc_priv_name with "Hp") as "(%Hl & Hnm & Hb)".
    iSplitR; [iPureIntro; exact Hl|].
    iSplitL "Hnm"; [iExact "Hnm"|].
    iIntros "Hnm".
    iDestruct ("Hb" $! (pv_name V) with "[] Hnm") as "H".
    { iPureIntro. exact Hl. }
    iEval (rewrite (sysc_upd_name_id V)) in "H". iExact "H".
  Qed.

  (* printk's vararg descriptions for [printk("%d %s: unknown sys call %d\n",
     p->pid, p->name, num)] -- only the middle one costs anything.  Mirrors
     ProofProcdumpLoop's [pdl_descs_mk]/[pdl_descs_take] pair. *)
  Lemma sysc_descs_mk (M : regfile) (nmp : mword 64) (nm : string) (dqn : dfrac) :
    pk_vararg M 1%nat = nmp ->
    PrintkFmt.nonul nm = true -> eq_vec nmp (zero_reg : mword 64) = false ->
    nmp ↦ₛ{dqn} nm -∗
    ([∗ list] i ↦ d ∈ [PkANum; PkAStr dqn nm; PkANum], pk_desc_res (pk_vararg M i) d).
  Proof.
    intros H1 Hnm Hnz. iIntros "Hn".
    rewrite !big_sepL_cons big_sepL_nil H1.
    iSplitR. { unfold pk_desc_res; cbn match. done. }
    iSplitL "Hn".
    { unfold pk_desc_res; cbn match.
      iSplit; [iPureIntro; exact Hnm|].
      iSplit; [iPureIntro; exact Hnz|]. iExact "Hn". }
    iSplitR; [unfold pk_desc_res; cbn match; done | done].
  Qed.

  Lemma sysc_descs_take (M : regfile) (nmp : mword 64) (nm : string) (dqn : dfrac) :
    pk_vararg M 1%nat = nmp ->
    ([∗ list] i ↦ d ∈ [PkANum; PkAStr dqn nm; PkANum], pk_desc_res (pk_vararg M i) d) -∗
    nmp ↦ₛ{dqn} nm.
  Proof.
    intros H1. iIntros "H".
    rewrite !big_sepL_cons big_sepL_nil H1.
    unfold pk_desc_res; cbn match.
    iDestruct "H" as "(_ & (_ & _ & $) & _)".
  Qed.

  (* ===================================================================== *)
  (* THE BUFFER-CACHE SLOT BUDGET, split and rejoined.  Three units is what
     [wp_syscall_sconf_body] carries and what every fs entry that goes
     through [fileclose_fs_env] wants whole; the two entries whose contracts
     ask for ONE ([filestat]'s and [fileread]'s bundles each carry a single
     [bslot], because ilock's bread takes it and brelse gives it back) take
     it out of the three and put it back. *)
  Lemma sysc_bslot_split : bslots 3 -∗ bslot ∗ bslots 2.
  Proof.
    assert (H3 : 3%nat = (1 + 2)%nat) by lia.
    rewrite /bslot H3 bslots_op. iIntros "$".
  Qed.

  Lemma sysc_bslot_join : bslot -∗ bslots 2 -∗ bslots 3.
  Proof.
    assert (H3 : 3%nat = (1 + 2)%nat) by lia.
    rewrite /bslot H3 bslots_op. iIntros "H1 H2". iFrame "H1 H2".
  Qed.

  (* ===================================================================== *)
  (* THE CONTENT-INDEPENDENT FILE-SYSTEM BUNDLES, AT THE DISPATCH'S NAMES.

     [SpecFilestat] and [SpecFileread] each state their environment over
     their OWN names record ([fstat_names], [fread_names]) rather than over
     [fclose_names], because neither function is a closer and neither wants
     the bitmap or the pid cell.  The records are strict SUBSETS of
     [fclose_names]'s fields, so the dispatch builds each one out of [fn] --
     the ONE thing that makes this work is that both bundles are stated at
     the AMBIENT [icfg_dev]/[icfg_nib], which [sysc_ties] says are [fn]'s own
     ([sysc_fs_env_all]'s first two rows).  Before [fs_ready], the bundle
     these are carved out of held its fabric at fresh existentials and this
     carving was impossible -- SpecSyscall.v's UNREACHABLE-WITNESS problem,
     in the shape it takes for a NON-closer callee. *)
  Definition sysc_fstat_names (bn : bio_names) (fn : fclose_names) : fstat_names :=
    MkFStatNames (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
      (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn
      DfracDiscarded.

  (* =================================================================== *)
  (*  ENTRY 5, [read].  [SpecFileread.fileread_fs_env] is FIELD FOR FIELD   *)
  (*  [SpecFilestat.filestat_fs_env] -- same twelve conjuncts, same order,  *)
  (*  only the record prefix differs -- so the carve below is                *)
  (*  [sysc_filestat_env]'s, and the names record is [sysc_fstat_names]'s    *)
  (*  plus the four fields fileread has and filestat does not: the running   *)
  (*  process (readi copies into user memory), the cons lock, and the        *)
  (*  device column's value/fraction functions.                              *)
  (*                                                                        *)
  (*  THE COLUMN IS PINNED TO THE CONSOLE TABLE, not left as a family this   *)
  (*  arm would have to own: [frn_rp] IS [ConsoleInv.devsw_read_val] and     *)
  (*  every cell is held at [DfracDiscarded], which is what                  *)
  (*  [SpecFileread.fileread_devsw_of_console] needs and what makes both     *)
  (*  equations [reflexivity] at the call.  [γc] comes from destructing      *)
  (*  [ConsoleInv.console_ready] out of [syscall_env] ONCE -- which is why   *)
  (*  the gname is existential there and not a field of [fclose_names].      *)
  (* =================================================================== *)
  Definition sysc_fread_names (γc : gname) (bn : bio_names) (fn : fclose_names)
      : fread_names :=
    MkFReadNames (fcn_procs fn) (fcn_j fn) (fcn_plock fn)
      (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn) γc
      (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn
      DfracDiscarded
      ConsoleInv.devsw_read_val (fun _ => DfracDiscarded).

  Lemma sysc_fileread_env (γf : gname) (γc : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗ bslot -∗
    SpecFileread.fileread_fs_env γf (sysc_fread_names γc bn fn) ∗
    (SpecFileread.fileread_fs_out (sysc_fread_names γc bn fn) -∗ bslot).
  Proof.
    iIntros "#Hfs Hsl".
    iDestruct (sysc_fs_env_all with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & %Hlg &
        _ & _ & #Hbio & _ & _ & _ & #Hdevi & #Hgeom & #Hdlock & _ & _ &
        _ )".
    iDestruct (sysc_ic_env_of_ready with "Hfs") as
      "( _ & _ & _ & _ & %Hist0 & %Hib & _ & #Hit & #Hitinv & #Hesc &
        #Hireg & _ & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfs") as "(_ & #Hisp & _)".
    iSplitL "Hsl".
    { rewrite /SpecFileread.fileread_fs_env /sysc_fread_names; cbn.
      (* conjunct by conjunct, not [iFrame]: the tail is [dev_inv] /
         [disk_geom] / an [is_lock] over [disk_res], and a frame prices each
         name against each of those as a CONVERSION (33.1 s, measured on
         [sysc_filestat_env]).  Each line below is a syntactic check. *)
      iSplit; [ iPureIntro; exact Hlg |].
      iSplit; [ iPureIntro; exact Hist0 |].
      iSplit.
      { iPureIntro. intros inum Hi. exact (proj1 (Hib inum Hi)). }
      iSplitR; [ iExact "Hbio"   |].
      iSplitR; [ iExact "Hitinv" |].
      iSplitR; [ iExact "Hesc"   |].
      iSplitR; [ iExact "Hireg"  |].
      iSplitR; [ iExact "Hsl2"   |].
      iSplitR; [ iExact "Hisp"   |].
      iSplitR; [ iExact "Hdevi"  |].
      iSplitR; [ iExact "Hgeom"  |].
      iSplitR; [ iExact "Hdlock" |].
      iExact "Hsl". }
    iIntros "Hout".
    rewrite /SpecFileread.fileread_fs_out /sysc_fread_names; cbn.
    by iDestruct "Hout" as "[_ $]".
  Qed.

  Lemma sysc_filestat_env (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      :
    sysc_fs_env pj bn fn -∗ bslot -∗
    SpecFilestat.filestat_fs_env (sysc_fstat_names bn fn) ∗
    (SpecFilestat.filestat_fs_out (sysc_fstat_names bn fn) -∗ bslot).
  Proof.
    iIntros "#Hfs Hsl".
    iDestruct (sysc_fs_env_all with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & %Hlg &
        _ & _ & #Hbio & _ & _ & _ & #Hdevi & #Hgeom & #Hdlock & _ & _ &
        _ )".
    iDestruct (sysc_ic_env_of_ready with "Hfs") as
      "( _ & _ & _ & _ & %Hist0 & %Hib & _ & #Hit & #Hitinv & #Hesc &
        #Hireg & _ & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfs") as "(_ & #Hisp & _)".
    iSplitL "Hsl".
    { rewrite /SpecFilestat.filestat_fs_env /sysc_fstat_names; cbn.
      (* assembled conjunct by conjunct rather than with a named [iFrame]:
         the goal's tail is [dev_inv] / [disk_geom] / an [is_lock] over
         [disk_res], so a frame prices each of the ten names against each of
         those as a CONVERSION -- 33.1 s of this file, measured.  The chain
         below is a syntactic check each. *)
      iSplit; [ iPureIntro; exact Hlg |].
      iSplit; [ iPureIntro; exact Hist0 |].
      iSplit.
      { iPureIntro. intros inum Hi. exact (proj1 (Hib inum Hi)). }
      iSplitR; [ iExact "Hbio"   |].
      iSplitR; [ iExact "Hitinv" |].
      iSplitR; [ iExact "Hesc"   |].
      iSplitR; [ iExact "Hireg"  |].
      iSplitR; [ iExact "Hsl2"   |].
      iSplitR; [ iExact "Hisp"   |].
      iSplitR; [ iExact "Hdevi"  |].
      iSplitR; [ iExact "Hgeom"  |].
      iSplitR; [ iExact "Hdlock" |].
      iExact "Hsl". }
    iIntros "Hout".
    rewrite /SpecFilestat.filestat_fs_out /sysc_fstat_names; cbn.
    by iDestruct "Hout" as "[_ $]".
  Qed.

  (* ===================================================================== *)
  (* THE TWO CLOSING BUNDLES, ASSEMBLED.  [sys_close] and [sys_pipe] are the
     entries that close a descriptor of UNKNOWN type, so each carries both of
     fileclose's environments and hands over whichever the type selects.
     Neither is a new resource: the pipe arm is [procs_inv] plus the
     allocator (at the SEALED count, which is what makes it persistent), and
     the FS arm is the whole fabric plus the three block slots and the
     bitmap.

     THE PID QUARTER IS NOT HERE, and that is the point.  [fileclose]'s FS
     arm wants a quarter of [p->pid]; [ProcInv.proc_priv] owns one half and
     [SchedCtx]'s state resource the other, so a dispatch holding
     [proc_priv] cannot ALSO hold a quarter -- three quarters is more than
     exists outside the proc lock.  So these hand over the NOPID bundle and
     the two entries lend the quarter out of their own [proc_priv] (see
     SpecSysClose.v's note; [SpecFileclose.fileclose_loop_open] is the
     pairing). *)
  Lemma sysc_fclose_pipe_env (pj : mword 64) (bn : bio_names) (fn : fclose_names) :
    sysc_fs_env pj bn fn -∗ fileclose_pipe_env fn None 0%nat.
  Proof.
    iIntros "#Hfs".
    iDestruct (sysc_fs_env_all with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & _ & #Hpi & _ & _ & _ & _ & _ & _ & _ & _ & #Hkm & #Hav & _ )".
    rewrite /fileclose_pipe_env.
    iSplit; [ iPureIntro; cbn; lia |].
    iFrame "Hpi Hkm Hav".
  Qed.

  (* THE BUNDLE IS SEVEN ROWS SHORTER THAN THE OLD ONE, and every row it
     lost it lost to [FsReady.fs_ready]: the block/log fabric, the crash
     seam, the era certificate, the icache's own bundle, the bitmap and --
     since the ring pages stopped being [fscfg] fields -- the two disk rows
     as well are all projections of the ONE predicate this carries.  What is
     left to assemble is the four process pures, the ties, [procs_inv],
     [fs_ready] itself, and the slots. *)
  Lemma sysc_fclose_fs_env (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      (eb : bool) :
    sysc_fs_env pj bn fn -∗ bslots 3 -∗
    fileclose_fs_env_nopid fn 0%nat eb pj.
  Proof.
    iIntros "#Hfs Hbs".
    iDestruct (sysc_fs_env_ties with "Hfs") as "%T".
    iDestruct "Hfs" as "(_ & #Hpi & _ & _ & #Hrdy)".
    (* the [fcn_bio] tie has nothing left to rewrite: the slot supply is at
       the canonical ghost name, so [bslots] does not mention the bio record
       and this goal never names [bn]. *)
    rewrite /fileclose_fs_env_nopid.
    iSplit; [ iPureIntro; reflexivity |].
    iSplit; [ iPureIntro; exact (sct_pj _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_j _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sct_plock _ _ _ T) |].
    iSplit; [ iPureIntro; exact (sysc_fclose_ties _ _ _ T) |].
    (* conjunct by conjunct, not [iFrame]: the goal's tail is [fs_ready] and
       [bslots], both definition-valued, so a frame walks each name past them
       by CONVERSION -- 58.4 s, measured on this sentence's predecessor. *)
    iSplitR; [ iExact "Hpi"    |].
    iSplitR; [ iExact "Hrdy"   |].
    iExact "Hbs".
  Qed.

  (* =================================================================== *)
  (*  ENTRY 16, [write].  Heavier than read's: filewrite's FD_INODE arm     *)
  (*  runs writei under begin_op/end_op and through balloc, so on top of    *)
  (*  read's twelve conjuncts it wants the log, the crash seam, the era      *)
  (*  certificate, balloc's printk credentials, the bitmap and its two       *)
  (*  superblock cells, and THREE block slots rather than one.  Every one    *)
  (*  of those is already in [sysc_fs_env] -- they are what the create /     *)
  (*  namei entries run on -- so this is assembly, not new resource.         *)
  (*                                                                        *)
  (*  TWO GNAMES ARE DESTRUCTED, not carried: [γpr] and the tx lock's [γl],  *)
  (*  both out of [printk_env]'s own existential.  The tx lock is what       *)
  (*  filewrite's DEVICE arm needs -- consolewrite drives the UART, so its   *)
  (*  caps are [dev_inv] plus the tx lock and NOT the cons lock, which is    *)
  (*  the one place the two syscalls' device arms differ.                    *)
  (* =================================================================== *)
  (* the process triple is a PARAMETER, not read off [fn]: [SpecSysWrite]
     ties [fwn_j]/[fwn_procs] to the dispatch's own [j]/[γs] (its FD_INODE
     arm's callees are all indexed by them), and taking them here makes both
     equations [reflexivity] at the call instead of an injectivity argument
     about [proc_addr]. *)
  Definition sysc_fwrite_names (γpr γl : gname)
      (γs : list gname) (j : nat) (γlp : gname) (bn : bio_names)
      (fn : fclose_names) : fwrite_names :=
    MkFWriteNames γs j γlp
      (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn) γl
      (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn
      γpr
      (fcn_bmapstart fn) (fcn_size fn)
      DfracDiscarded DfracDiscarded DfracDiscarded
      ConsoleInv.devsw_write_val (fun _ => DfracDiscarded).

  (* [γpr] is [fsc_printk] and not an existential witness: the gen-contract
     fact [filewrite_fs_env] wants exists only AT that name, and
     [syscall_env_all]'s [∃ γpr] would hand out a name nothing says it of.
     The tx lock's [γl] IS existential -- [printk_env] closes over it -- so
     it stays a parameter and the arm destructs it once. *)
  Lemma sysc_filewrite_env (γf γl : gname) (γs : list gname) (j : nat)
      (γlp : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) :
    kernel_data -∗ is_txlock γl (fcn_uart fn) -∗
    sysc_fs_env pj bn fn -∗ bslots 3 -∗
    SpecFilewrite.filewrite_fs_env γf (sysc_fwrite_names fsc_printk γl γs j γlp bn fn).
  Proof.
    iIntros "#Hkd #Htx #Hfs Hbs".
    iDestruct (sysc_fs_env_all with "Hfs") as
      "( _ & _ & _ & _ & _ & _ & _ & %Hlg &
        _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom & #Hdlock &
        _ & _ & _ & %Hbg & _ & _ & #Hsz & %Hpg & #Hpe )".
    iDestruct (sysc_ic_env_of_ready with "Hfs") as
      "( _ & _ & _ & _ & %Hist0 & %Hib & _ & #Hit & #Hitinv & #Hesc &
        #Hireg & _ & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfs") as "(#Hbmst & #Hisp & #Hbmr)".
    rewrite /SpecFilewrite.filewrite_fs_env /sysc_fwrite_names; cbn.
    iSplit; [ iPureIntro; exact Hlg |].
    iSplit; [ iPureIntro; exact Hist0 |].
    iSplit.
    { iPureIntro. intros inum Hi. exact (proj1 (Hib inum Hi)). }
    iSplit.
    { iPureIntro. intros inum Hi. exact (proj2 (Hib inum Hi)). }
    iSplit; [ iPureIntro; exact Hbg |].
    iSplit; [ iPureIntro; exact Hpg |].
    (* conjunct by conjunct, for [sysc_fclose_fs_env]'s measured reason: the
       goal's tail is definition-valued, so a named [iFrame] prices every one
       of these against each of those as a CONVERSION. *)
    iSplitR; [ iExact "Hbio"   |].
    iSplitR; [ iExact "Hlog"   |].
    iSplitR; [ iExact "Hseam"  |].
    iSplitR; [ iExact "Hgen"   |].
    iSplitR; [ iExact "Hkd"    |].
    iSplitR; [ iExact "Hpe"    |].
    iSplitR; [ iExact "Hitinv" |].
    iSplitR; [ iExact "Hesc"   |].
    iSplitR; [ iExact "Hireg"  |].
    iSplitR; [ iExact "Hsl2"   |].
    iSplitR; [ iExact "Hisp"   |].
    iSplitR; [ iExact "Hsz"    |].
    iSplitR; [ iExact "Hbmst"  |].
    iSplitR; [ iExact "Hbmr"   |].
    iSplitR; [ iExact "Hdevi"  |].
    iSplitR; [ iExact "Hgeom"  |].
    iSplitR; [ iExact "Hdlock" |].
    iExact "Hbs".
  Qed.

  (* ...and the inverse, for the two entries' RETURN: the nopid bundle's own
     three block slots, back out.  THE BITMAP IS NO LONGER PART OF IT --
     [bitmap_inv] is persistent and rides inside [fs_ready] -- so the block
     slots are the whole of what a caller has to recover. *)
  Lemma sysc_fclose_fs_out (bn : bio_names) (fn : fclose_names)
      (n : nat) (eb : bool) (pj : mword 64) :
    fcn_bio fn = bn ->
    fileclose_fs_env_nopid fn n eb pj -∗ bslots 3.
  Proof.
    (* [Hb] is vestigial now: the slot supply is at the canonical ghost
       name, so the count on either side names no bio record. *)
    intro Hb. rewrite /fileclose_fs_env_nopid.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & $)".
  Qed.

End SyscallVocab.

(* ===================================================================== *)
(* S2 -- THE RETURN TAIL every wired arm shares: +0x3a (store the callee's
   [a0] into [p->trapframe->a0]) and +0x3e (jump to the epilogue), then
   [sysc_epilogue_tail].  Its own two crossings are why it cannot sit beside
   the epilogue it applies.

   It is deliberately VALUE-AGNOSTIC: [syscall]'s own postcondition says
   nothing about what a table entry returned (only that the trapframe POINTER
   did not move), so the tail never needs to know [a0]'s value and one lemma
   serves all 22 entries.  [V'] is the callee's own outgoing private block,
   which the store then advances to [upd_tf V' _]. *)
Section SyscallRet.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sysc_ret_tail
      (γf : gname) (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      (dqi : dfrac) (ip : mword 64) (pid : mword 32) (V V' : pprivate)
      (lks : gset string) (av : nat)
      (m E : regfile) :
    E !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    E !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V')) ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       E !!! Regidx r = m !!! Regidx r) ->
    (4 <= av)%nat ->
    ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ->
    (* ...and the fd-state ghost name, which no syscall moves *)
    pv_fdg V' = pv_fdg V ->
    sie_cap_gpr KT1 E (av - 4)%nat true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    bslots 3 -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
    syscall_env γf pj bn fn -∗ proc_priv γf pj pid V' -∗
    fd_frags_any (pv_fdg V) -∗
    pc_is (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64) -∗
    sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HEsp HEs2 Hrest Hav4 Hud Hfg.
    iIntros "Hcg Hcpu #Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir HR Hpriv Hufrag Hpc Hcont".
    set (tfp := ud_tfp (pv_upt V')).
    (* the trapframe page, opened for WRITING out of [proc_priv] *)
    iDestruct (sysc_tfp_valid with "Hpriv") as "%Hpv".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
    iPoseProof (pt_node_claim_from_static tfp Hpv with "Hkmapb") as "#Hptc".
    iDestruct (proc_priv_tf_upd with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    assert (Hi14 : (tf_arg_idx 0 < length (pv_tf V'))%nat)
      by (rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia).
    destruct (lookup_lt_is_Some_2 (pv_tf V') (tf_arg_idx 0) Hi14) as [w0 Hw0].
    iDestruct (tf_page_word_upd_mem tfp (pv_tf V') (tf_arg_idx 0) w0
                 ltac:(vm_compute; lia) Hw0 with "Hptc Htfp") as "(Hcell & Hcback)".
    (* ---- +0x3a: sd a0,112(s2) -- p->trapframe->a0 = the return value ---- *)
    assert (HEs2r : rget E Rs2 = page_base tfp) by (rgne; exact HEs2).
    iEval (rewrite -(sysc_tf_addr_112 tfp) -HEs2r) in "Hcell".
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.syscall + 0x3a)) Ra0 Rs2
              (mword_of_int 112 : mword 12) E (av - 4)%nat w0 true
              with "Hcg Hpc [] Hcell").
    { iApply (syci_3a with "Htext"). }
    iIntros (CIDa Hsa) "Hcg Hpc Hcell".
    iEval (rewrite HEs2r (sysc_tf_addr_112 tfp)) in "Hcell".
    iDestruct ("Hcback" $! (rget E Ra0) with "Hcell") as "Htfp".
    iDestruct ("Hpvback" $! (<[tf_arg_idx 0 := rget E Ra0]> (pv_tf V'))
                 with "Htfc Htfp") as "Hpriv".
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x3e)) by pcw.
    iEval (rewrite Hp3e) in "Hpc".
    (* ---- +0x3e: c.j +0x1a -- over the fallback block, into the epilogue ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.syscall + 0x3e))
              (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
              E (av - 4)%nat true ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (syci_3e with "Htext"). }
    iIntros (CIDb Hsb). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hp58 : add_vec (mword_of_int (KernelSyms.syscall + 0x3e) : mword 64)
                     (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0"))))
                   = mword_of_int (KernelSyms.syscall + 0x58)) by pcw.
    iEval (rewrite Hp58) in "Hpc".
    (* the epilogue runs at the hart the jump landed on *)
    assert (Hcrb : true = false \/ pj = zero_reg -> (CIDb : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDb true pj _ Hcrb with "Hcont") as "Hcont".
    iDestruct (cpu_own_transport CID CIDb 0%nat true pj true Hcrb with "Hcpu") as "Hcpu".
    iApply (sysc_epilogue_tail (CID := CIDb) γf pj bn fn dqi ip pid V
              (upd_tf V' (<[tf_arg_idx 0 := rget E Ra0]> (pv_tf V')))
              lks av m E HEsp Hrest Hav4 Hud
              ltac:(cbn [pv_fdg upd_tf]; exact Hfg)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir HR Hpriv Hufrag Hpc Hcont").
  Qed.

End SyscallRet.

(* ===================================================================== *)
(* S3 -- THE DISPATCH ARMS, one per table entry, plus the combinator the
   capstone applies.  An arm calls its entry's own whole-function contract
   and hands the result to S2's [sysc_ret_tail]; since the callee's post is
   delivered at a REBOUND hart, the tail has to come from an earlier
   section. *)
Section SyscallArms.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ------------------------------------------------------------------- *)
  (* THE FIRST REAL ARM: k = 11, [sys_getpid].  It is the entry that needs
     the LEAST from the environment -- [proc_priv] and nothing else (no lock,
     no fs fabric, no [γl]; see SpecSysGetpid.v's own header) -- so it is
     where the arm shape is established.  Everything specific to getpid is
     the two lines that call its contract and read [callee_saved] out of its
     post; the rest is [sysc_ret_tail], shared with every other entry. *)
  Lemma sysc_arm_getpid (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 11 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    (* the table entry's address IS [sys_getpid]'s entry pc *)
    assert (Hpce : (mword_of_int (sysc_target 11) : mword 64)
                   = mword_of_int KernelSyms.sys_getpid) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    (* ---- the call ---- *)
    iApply (SysGetpid.wp_sys_getpid_sconf γf M (av - 4)%nat 0%nat true pj pid V true lks
              ltac:(lia) ltac:(lia)
              with "Hcg Hcpu Htext Hpc Hpriv").
    iIntros (CIDy Hsy mf) "%Hmf Hcg Hcpu Hpc Hpriv".
    destruct Hmf as [Hcs _].
    (* ---- what the callee's [callee_saved] gives the shared tail ---- *)
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* ---- the shared return tail, at the hart the callee returned on ---- *)
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V lks av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE SECOND ARM: k = 12, [sys_sbrk].  Beyond [proc_priv] it wants only
     [kalloc_env] -- which [syscall_env] carries -- plus its two syscall
     arguments, which are words of the trapframe page [proc_priv] already
     owns, so the arm reads their EXISTENCE off the page's length and never
     inspects them.  Unlike getpid it MOVES the private block (both the size
     and, on the eager path, the page-table descriptor), which is why the
     trapframe page's immobility has to be extracted from [sys_sbrk_ok]. *)
  Lemma sysc_sbrk_tfp (V : pprivate) (v0 v1 : mword 64)
      (P' : uptd) (szv' r : mword 64) :
    sys_sbrk_ok V v0 v1 P' szv' r -> ud_tfp P' = ud_tfp (pv_upt V).
  Proof.
    intro Hok.
    destruct Hok as [ (_ & HP & _) | (_ & [ (_ & Hg) | (_ & _ & HP & _ & _) ]) ].
    - rewrite HP. reflexivity.
    - destruct Hg as [ (_ & HP & _)
                     | [ (_ & _ & _ & _ & (_ & Htf & _) & _)
                       | [ (_ & _ & HP & _) | (_ & _ & HP & _) ] ] ].
      + rewrite HP. reflexivity.
      + exact Htf.
      + rewrite HP. reflexivity.
      + rewrite HP. reflexivity.
    - rewrite HP. reflexivity.
  Qed.

  Lemma sysc_arm_sbrk (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 12 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 12) : mword 64)
                   = mword_of_int KernelSyms.sys_sbrk) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    (* the two argument words exist because the trapframe page has 36 of
       them -- read off [proc_priv] and handed straight back *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    (* [kalloc_env], peeled off a COPY of the (fully persistent) environment
       bundle, so the original stays available to hand back verbatim *)
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _)".
    (* ---- the call ---- *)
    iApply (SysSbrk.wp_sys_sbrk_sconf γa γf M (av - 4)%nat true pj pid V v0 v1 true lks
              Hv0 Hv1 ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Hpriv Hkalloc").
    iIntros (CIDy Hsy mf P' szv') "%Hcs %Hok Hcg Hcpu Hpc Hpriv".
    assert (Htfp' : ud_tfp P' = ud_tfp (pv_upt V))
      by exact (sysc_sbrk_tfp V v0 v1 P' szv' (mf !!! Regidx Ra0) Hok).
    (* ---- what the shared tail needs of the returned register file ---- *)
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2
                    = page_base (ud_tfp (pv_upt (upd_sz (upd_upt V P') szv')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      cbn [pv_upt upd_sz upd_upt pv_fdg]. rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V
              (upd_sz (upd_upt V P') szv') lks av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE THIRD ARM: k = 3, [sys_wait].  The first entry that PARKS -- kwait
     sleeps on the wait lock, so its own crossing may resume the process on
     another hart -- and the first that needs the process TRIPLE ([γs]/[j]/
     [γl], with the running process addressed as [proc_addr j]) plus
     [procs_inv].  Everything else it wants is in
     [syscall_env]: [kalloc_env] and the "wait_lock" lock.  It moves the
     private block's page-table descriptor (the reaped child's pages are
     freed through it), and [uptd_ext_sz] is what pins the trapframe page. *)
  Lemma sysc_arm_wait (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 3 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 3) : mword 64)
                   = mword_of_int KernelSyms.sys_wait) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    (* argument 0 (the user's status pointer) exists because the trapframe
       page has 36 words; sys_wait never inspects it here *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & #Hwaitlk & _)".
    (* ---- the call ---- *)
    iApply (SysWait.wp_sys_wait_sconf γa γf γw γs j γl M (av - 4)%nat true true lks pid V v0
              Hj Hgamma Hv0 ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hdata Hpc Hprocs Hwaitlk Hkalloc Hpriv").
    iIntros (CIDy Hsy mf P' rv) "%Hcs %Hext Hcg Hcpu Hpc Hpriv".
    destruct Hcs as [Hcs _].
    assert (Htfp' : ud_tfp P' = ud_tfp (pv_upt V)).
    { destruct (uptd_ext_sz_ext (pv_sz V) (pv_upt V) P' Hext) as (_ & Htf & _).
      exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      cbn [pv_upt upd_upt pv_fdg]. rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') lks av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE RANK BOUND IS FREE AT THIS ALTITUDE -- every arm below uses it.
     dup/fork/kill/pause/uptime each demand [locks_below lks "<rank>"] and
     [wp_syscall_sconf_body] says nothing about [lks]; it does not have to.
     [syscall()] runs at push_off level 0, so [sysc_arm_pre] carries
     [cpu_own 0 ...], and [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] from
     it -- after which [LockRank.locks_below_empty] discharges the premise at
     ANY rank.  Two lines per arm, no contract change, no ripple into
     usertrap's cone; SpecSysLink.v's header documents the same derivation at
     its own altitude. *)
  Local Lemma sysc_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
  Proof. vm_compute; reflexivity. Qed.

  Local Lemma sysc_noff0b : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
  Proof. vm_compute; reflexivity. Qed.

  (* THE FOURTH ARM: k = 14, [sys_uptime].  After getpid the entry that asks
     for the least: it is niladic, touches no per-process state at all (no
     [proc_priv], no trapframe word), and wants exactly the tickslock out of
     [syscall_env] plus the rank bound its [acquire] raises. *)
  Lemma sysc_arm_uptime (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 14 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 14) : mword 64)
                   = mword_of_int KernelSyms.sys_uptime) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & _ & #Hticks & _)".
    (* ---- the call ---- *)
    iApply (SysUptime.wp_sys_uptime_sconf γtk M 0%nat true pj (av - 4)%nat true ∅
              sysc_noff0 ltac:(lia) (locks_below_empty "time")
              with "Hcg Hcpu Htext Hpc Hticks").
    iIntros (CIDy Hsy mf t) "%Hmf Hcg Hcpu Hpc".
    destruct Hmf as [Hcs _].
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE FIFTH ARM: k = 6, [sys_kill].  The first entry that reads a syscall
     ARGUMENT out of the raw trapframe word list rather than out of
     [pv_tf V] as an opaque existential: its [argint] wants
     [p_trapframe ↦₈{dq}] and the whole [tf_page] SEPARATELY, which is
     exactly what [ProcInv.proc_priv_tf] lends (at the quarter fraction) and
     takes back.  Beyond that it is [procs_inv] (kkill's
     scan) and the [length γs = NPROC] that scan's bound needs, which
     [procs_inv] itself carries. *)
  Lemma sysc_arm_kill (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 6 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 6) : mword 64)
                   = mword_of_int KernelSyms.sys_kill) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (procs_inv_len with "Hprocs") as "%Hlen".
    iDestruct (sysc_tfp_valid with "Hpriv") as "%Hpv".
    (* argint's two trapframe resources, lent out of [proc_priv] *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    (* ---- the call ---- *)
    iApply (SysKill.wp_sys_kill_sconf γs M (av - 4)%nat 0%nat true pj
              (ud_tfp (pv_upt V)) (pv_tf V) v0 (DfracOwn (1/4)) true ∅
              Hlen Hv0 sysc_noff0 ltac:(lia) (locks_below_empty "proc") Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp Hprocs").
    iIntros (CIDy Hsy mf rv) "%Hmf Hcg Hcpu Hpc Htfc Htfp".
    destruct Hmf as [Hcs _].
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE SIXTH ARM: k = 13, [sys_pause].  kill's trapframe borrow plus the
     tickslock, and -- because it SLEEPS on the tick counter -- the running
     process's own triple ([γs]/[j]/[γl], the process addressed as
     [proc_addr j]) and [procs_inv], exactly as sys_wait
     needs.  Its [eb = true] parking premise is what [sysc_arm_pre]'s own
     [cpu_own 0 true ...] already says. *)
  Lemma sysc_arm_pause (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 13 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 13) : mword 64)
                   = mword_of_int KernelSyms.sys_pause) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (sysc_tfp_valid with "Hpriv") as "%Hpv".
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & _ & #Hticks & _)".
    (* ---- the call ---- *)
    iApply (SysPause.wp_sys_pause_sconf γs j γl γtk M (av - 4)%nat true 0%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v0 (DfracOwn (1/4)) true ∅
              Hj Hgamma eq_refl Hv0 ltac:(lia) eq_refl (locks_below_empty "time") Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp Hticks Hprocs").
    iIntros (CIDy Hsy mf rv) "%Hmf Hcg Hcpu Hpc Htfc Htfp".
    destruct Hmf as [Hcs _].
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V ∅ av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* [sys_dup]'s three-way post, collapsed to what the shared tail needs: SOME
     private block, with the trapframe page unmoved.  Only the success arm
     moves [V] at all, and [upd_ofile] rewrites the fd array alone -- the
     descriptor [pv_upt] (hence [ud_tfp]) is the same record field. *)
  Lemma sysc_dup_priv (γf : gname) (p : mword 64) (pid : mword 32)
      (V : pprivate) (v r : mword 64) :
    sys_dup_post γf p pid V v r -∗
    ∃ V' : pprivate, ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗
      (* the fd-state ghost name does not move: every arm returns either [V]
         itself or an [upd_ofile] of it *)
      ⌜pv_fdg V' = pv_fdg V⌝ ∗
      proc_priv γf p pid V' ∗ fd_frags_any (pv_fdg V).
  Proof.
    rewrite /sys_dup_post.
    iIntros "[[_ [Hp Hfr]] | [Hb | Hc]]".
    - iExists V. iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; reflexivity | iFrame "Hp Hfr"].
    - iDestruct "Hb" as (fd0 fv) "[_ [Hp Hfr]]".
      iExists V. iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; reflexivity | iFrame "Hp Hfr"].
    - iDestruct "Hc" as (fd0 fd1 fv l) "[_ [Hp Hfr]]".
      iExists (upd_ofile V fd1 fv). iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; reflexivity | iFrame "Hp Hfr"].
  Qed.

  (* THE SEVENTH ARM: k = 10, [sys_dup].  Beyond [proc_priv] it wants only the
     ftable lock (for filedup's ghost step) out of [syscall_env], plus its own
     argument word -- which, unlike kill's, it reads through [proc_priv] and so
     needs only as an EXISTENCE fact about [pv_tf V], the way sbrk's two are
     read.  Its post is the named [sys_dup_post], collapsed by
     [sysc_dup_priv]: which of the three exits ran is invisible to the tail. *)
  Lemma sysc_arm_dup (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 10 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 10) : mword 64)
                   = mword_of_int KernelSyms.sys_dup) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & #Hftable & _)".
    (* ---- the call ---- *)
    iApply (SysDup.wp_sys_dup_sconf γft γf M (av - 4)%nat 0%nat true pj v0 pid V true ∅
              Hv0 sysc_noff0 ltac:(lia) (locks_below_empty "ftable")
              with "Hcg Hcpu Htext Hdata Hpc Hftable Hpriv Hufrag").
    iIntros (CIDy Hsy mf) "%Hcs Hcg Hcpu Hpc Hpost".
    iDestruct (sysc_dup_priv with "Hpost") as (V') "(%Htfp' & %Hfg' & Hpriv & Hufrag)".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V' ∅ av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE EIGHTH ARM: k = 1, [sys_fork].  The widest premise list of any wired
     entry -- kfork reaches allocproc, the fd table and idup -- and every one
     of its seven persistent handles ("nextpid", "wait_lock", the ftable, the
     itable and its invariant, [procs_avail None], [kalloc_env _ None]) is
     already inside [syscall_env].  It is also the only wired entry with NO
     process indexing: it takes the running process as a bare pointer and
     hands [proc_priv] back verbatim, kfork having only read it. *)
  Lemma sysc_arm_fork (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 1 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 1) : mword 64)
                   = mword_of_int KernelSyms.sys_fork) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & #Hnextpid & #Hpav & #Hwaitlk & #Hftable & _ & _ & #Hfsenv)".
    (* the itable's names are [fn]'s own now, and they reach this arm through
       [sysc_ic_env_of_ready] rather than as [syscall_env] conjuncts of their
       own (see [sysc_fs_env]).  [SpecSysFork] spells the device at the
       AMBIENT [icfg_dev], so the tie is what bridges the two spellings. *)
    iDestruct (sysc_fs_env_all with "Hfsenv") as "( _ & _ & _ & _ & _ & _ & _ & _ &
                            _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ )".
    (* the REGION handle comes out of the same bundle, one conjunct past
       [ic_escrows]: idup's [ref++] is a ledger move since increment IVe
       (iclaim-ledger.md §3.19), so [SpecSysFork] passes it down to kfork. *)
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & #Hitable & #Hitinv & _ & #Hireg & _ )".
    (* the child's token's source, and the world its park needs *)
    iDestruct (syscall_env_first with "Henvc") as "#Hfdone".
    iDestruct (syscall_env_world with "Henvc") as "#Hworld".
    iDestruct (syscall_env_token with "Henvc") as "#Htoken".
    (* the proc array at [fn]'s OWN spelling: the world and the token are
       stated there, so the callee is instantiated there too *)
    iDestruct "Hfsenv" as "(_ & #Hprocs' & _)".
    (* ---- the call ---- *)
    iApply (SysFork.wp_sys_fork_sconf γa γp γw γft γf
              (fcn_procs fn)

              M 0%nat (av - 4)%nat true pj true pid V ∅
              ltac:(lia) sysc_noff0b
              (locks_below_empty "wait_lock")
              with "Hcg Hcpu Htext Hpc Hprocs' Hnextpid Hwaitlk Hftable Hitable Hitinv Hireg Hkalloc Hpav Hworld Htoken Hfdone Hpriv").
    iIntros (CIDy Hsy mf) "%Hcs Hcg Hcpu Hpc Hpriv Hka %Hrv".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ pj = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true pj _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE NINTH ARM: k = 18, [sys_unlink] -- the one table entry with no proof
     anywhere in the tree, standing on LinkSysUnlink.v's [Axiom].  Its
     contract (SpecSysUnlink.v) was written to BE [wp_syscall_sconf_body]
     with the entry point changed, abstract environment [R] and all, so the
     arm is the shortest of the nine: hand it [syscall_env] for [R] and every
     other resource verbatim, and its post is [sysc_ret_tail]'s premise list
     already.  Nothing here is weaker than the axiom; wiring it is what makes
     [Print Assumptions] name sys_unlink rather than the dispatch's own
     placeholder. *)
  (* sys_unlink's ARM IS WITHDRAWN, not written.  Origin's arm applied
     [SysUnlink.wp_sys_unlink_sconf] at a leading [syscall_env] bundle;
     our line's b284fecb replaced the syscall-shaped placeholder with a
     REAL contract taking [(γf) (γa) (γpr) (gs) (j) (gl) (gu) (gd) (gk)
     (pd pav pu) ...].  Both are real, the shapes disagree, and index 18
     was settled by giving index 18 its own arm at the real shape --
     see claude-notes/projects/fs-sysfile.md, "S7-unlink". *)

  (* ------------------------------------------------------------------- *)
  (* THE TENTH ARM: k = 7, [sys_exec] -- the first of the eight entries the
     file header calls the GENUINE SPEC GAP, and the one that shows what
     closing that gap actually costs.  Its contract (SpecSysExec.v) is
     kexec's precondition marshalled: the whole FS fabric, the two
     superblock cells, [bitmap_inv], the kalloc environment and two units of
     the inode-reference allowance.

     THREE THINGS MAKE IT UNLIKE THE NINE ARMS ABOVE, and each was a design
     question rather than a proof detail:

     (1) THE FABRIC IS NOT A NEW INDEX.  sys_exec wants [fs_fabric] over the
         SAME file system its bitmap and superblock rows describe, and those
         are stated at [fn]'s fields -- so the fabric had to move from
         [syscall_env]'s fresh existentials to [fn]'s own names
         ([sysc_fs_env]).  Its two remaining pieces, [procs_inv γs] and
         [kernel_data], are drawn from [sysc_arm_pre] instead, which is what
         keeps [fcn_procs fn] out of the story: the dispatch's own [γs]/[j]/
         [γl] go straight into the call, so none of the three ties
         SpecSyscall.v's header shows sys_exit needing is needed here.
     (2) THE BITMAP NO LONGER CROSSES AT ALL.  It used to be the one mutable
         thing that did -- it came back SMALLER ([used' ⊆ used], kexec's cone
         being the only mover), and [sysc_hcont_ty] carried an [∃ us'] purely
         to re-index it.  [BitmapInv] made it a persistent invariant, so the
         arm takes a copy off [sysc_bm_cells], keeps it across the call, and
         the continuation's binder is gone.
     (3) THE TRAPFRAME PAGE SURVIVES TWO MOVES, NOT ONE.  The copy-ins grow
         the page table before kexec runs ([uptd_ext (pv_upt V) P']) and
         kexec then replaces the address space outright ([kexec_ok] against
         [upd_upt V P']); [ud_tfp] is pinned by BOTH -- by [uptd_ext]'s
         second conjunct and by [kexec_ok]'s success arm -- and composing the
         two is what [sysc_ret_tail]'s immobility premise needs.

     The budget is exact rather than slack: [K_syscall = 4 + K_sys_exec], so
     an arm running at [av - 4] has precisely sys_exec's own bound. *)
  Lemma sysc_arm_exec (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 7 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* a RETURNING arm takes the left conjunct and forgets the closer *)
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 7) : mword 64)
                   = mword_of_int KernelSyms.sys_exec) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    (* argaddr and argstr read trapframe arguments 1 and 0; the arm only has
       to say the two words EXIST, which the page's length gives *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    (* ---- the environment: the fabric, the allocator, and the pure ties ---- *)
    iPoseProof (sysc_fs_fabric γf (proc_addr j) γs bn fn
                  with "Hdata Hprocs Henv") as "#Hfab".
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    (* the ties, then the icache bundle's own nine pure facts *)
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hireg & %Hcb & _ )".
    (* ---- the three consumable families, carved to sys_exec's own shape ---- *)
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iDestruct (sysc_iref_split with "Hir") as "[Hirk Hire]".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    (* ---- the call ---- *)
    iApply (SysExec.wp_sys_exec_sconf γf γa γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 (fcn_size fn)
              DfracDiscarded DfracDiscarded v0 v1 pid V M (av - 4)%nat true true lks
              ltac:(lia) Hroot Hnib0 Hlg Hsize
              Hbm0 Hbmc Hbml Hist0 Hcb Hireg Hj Hgamma eq_refl Hv0 Hv1
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hfab Hbmp Hisp Hbmr Hbs
                    Hkalloc Hire Hpriv").
    iIntros (CIDy Hsy mf P') "%Hcs %Hext Hcg Hcpu Htcx' Hccx' Hpc
                              _ _ Hbs Hka' Hire' Hpost".
    iDestruct "Hpost" as (V' na alen entry spv szv') "[%Hkok Hpriv]".
    (* ---- the trapframe page, across BOTH moves (see (3) in the header) ---- *)
    assert (Htfp' : ud_tfp (pv_upt V') = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _).
      destruct Hkok as [ (_ & HV') | (_ & _ & _ & _ & _ & Htf' & _) ].
      - rewrite HV'. cbn [pv_upt upd_upt pv_fdg]. exact Htf.
      - rewrite Htf'. cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    (* ...and the fd-state ghost name, which exec does not move either:
       [SpecKexec.kexec_ok] states it because this is where it is needed. *)
    assert (Hfg' : pv_fdg V' = pv_fdg V).
    { destruct Hkok as [ (_ & HV') | Hs ].
      - rewrite HV'. reflexivity.
      - destruct Hs as (_ & _ & _ & _ & _ & _ & _ & _ & Hfg & _).
        revert Hfg. cbn [pv_fdg upd_upt]. exact id. }
    (* ---- what the shared tail needs of the returned state ---- *)
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* ---- the one family re-folded: the bitmap no longer travels ---- *)
    iDestruct (sysc_iref_join with "Hirk Hire'") as "Hir".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V'
              lks av m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ELEVENTH ARM: k = 2, [sys_exit] -- THE ENTRY THAT NEVER RETURNS.

     Everything unusual about it is in the contract, not the walk; the walk
     is the shortest of the eleven, because there is no return tail.

     (1) IT DROPS THE CALLER'S CONTINUATION AND TAKES THE CLOSER INSTEAD.
         [sysc_arm_goal] hands the exit slot as [sysc_exit_ty], the additive
         conjunction SpecSyscall.v's note argues for; this arm is the only
         consumer of the right conjunct.  [kstack_closer_frame] walks the
         anchor down syscall's own four frame cells -- which is what the
         four [word_pointsto]s [sysc_arm_goal] carries ARE, once
         [stack_own_4_intro] folds them -- landing on exactly the anchor and
         depth [SpecSysExit] names one frame further down.  Those cells are
         spent, and rightly: nothing pops this frame.
     (2) IT NAMES THE PROCESS THROUGH [fn], NOT THROUGH THE DISPATCH.
         [sys_exit] wants [fn] to BE the record built from the running
         process's names.  Rather than tie [fn]'s fields to the dispatch's
         own [γs]/[j]/[γl], the arm instantiates the callee AT [fn]'s fields
         and draws [procs_inv (fcn_procs fn)] and the two lookup facts from
         [sysc_fs_env] -- which is why four of the six ties the file header
         once attributed to this entry never appear.  [sysc_fn_eta] is the
         premise itself, and the only ties left are the two [sysc_fs_env]
         states ([fcn_bio], [fcn_dq]) plus the one premise
         [wp_syscall_sconf_body] carries ([fcn_pid fn = pid]).
     (3) IT DIVERGES, AND THAT COSTS NOTHING.  [iProp] is affine, so the
         bare [WP Loop] the contract concludes in discharges
         [sysc_arm_goal]'s own conclusion with the continuation simply
         dropped.  The "bespoke branch" the header used to promise is one
         [iApply]. *)
  Lemma sysc_arm_exit (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 2 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    assert (Hpce : (mword_of_int (sysc_target 2) : mword 64)
                   = mword_of_int KernelSyms.sys_exit) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    (* argint's word: sys_exit reads status out of the trapframe page *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    (* ---- the environment ---- *)
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & #Hwaitlk & #Hftable & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & %Hdq & %Hbio & %Hpja & %Hjn & %Hlk & %Hlg &
        #Hpi & #Hpanic & #Hbio' & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & #Hkmem & #Hka & _ )".
    (* THE TWO ROWS THAT REPLACED [fileclose_ic_env fn]: the twelve-equation
       tie record and the ONE predicate every fs fact is a projection of.
       Both persistent, both already in hand -- the ties come off
       [sysc_ties], which says everything [fclose_ties] does and more. *)
    iDestruct (sysc_fs_env_ties with "Hfsenv") as "%T".
    iAssert (⌜fclose_ties fn⌝)%I as "#Hties".
    { iPureIntro. exact (sysc_fclose_ties _ _ _ T). }
    iDestruct "Hfsenv" as "(_ & _ & _ & _ & #Hrdy)".
    (* ---- the closer, walked down syscall's own frame ---- *)
    iDestruct "Hcont" as "[_ Hkcl]".
    iDestruct (stack_own_4_intro (m !!! Regidx csp_rs1)
                 with "Hra Hs0 Hs1 Hs2") as "Hfr".
    iDestruct (kstack_closer_frame pj (m !!! Regidx csp_rs1)
                 (trap_res true + av)%nat 4 ltac:(unfold trap_res; lia)
                 with "Hkcl Hfr") as "Hkcl4".
    assert (Hdepth : ((trap_res true + av) - 4)%nat
                     = (trap_res true + (av - 4))%nat)
      by (unfold trap_res in *; lia).
    iEval (rewrite Hdepth -HMsp) in "Hkcl4".
    (* THE CALLEE ADDRESSES THE PROCESS AS [proc_addr (fcn_j fn)], the
       dispatch as [pj], and [sysc_fs_env] is what says they are the same.
       The rewrite is deliberately un-scoped: the proofmode goal IS
       [envs_entails Δ _], so this re-spells every hypothesis at once, which
       is what the call needs. *)
    rewrite Hpja.
    (* ---- the call: it does not return ---- *)
    iApply (SysExit.wp_sys_exit_sconf γft γf γw
              (fcn_procs fn) (fcn_j fn) (fcn_plock fn)
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

 ip dqi
              (fcn_kmem fn) (fcn_kalloc fn)
              (fcn_bmapstart fn) (fcn_size fn)
              None fn
              M (av - 4)%nat true true pid V v0 ∅
              (sysc_fn_eta fn bn pid Hbio Hpidt Hdq)
              Hjn Hlk Hv0 ltac:(lia) Hlg eq_refl (locks_below_empty "log")
              with "Hcg Hkcl4 Hcpu Htext Hdata Hpc Hpi Hpanic Hwaitlk Hftable
                    Hkmem Hka Hbio' Hlog Hseam Hgen Hdevi Hgeom Hdlock Hbs
                    Hties Hrdy Hip Hfd Hir Hpriv Hufrag").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TWELFTH ARM: k = 22, [sys_sync] -- the narrowest fs entry there is.
     It wants ONE resource, [log_ctx], plus the running-thread triple its
     interior [sleep] needs; no process block, no bitmap, no allowance.  It
     was on the GAP list only because [syscall_env] held the log at a fresh
     existential; at [fn]'s own names (which is what [sysc_ties] makes the
     ambient ones) it is a two-line call. *)
  Lemma sysc_arm_sync (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 22 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 22) : mword 64)
                   = mword_of_int KernelSyms.sys_sync) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & #Hlog & _ )".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iApply (SysSync.wp_sys_sync_sconf γs j γl bn icfg_log fsc_fs
              fsc_cov fsc_logst icfg_dev
              M (av - 4)%nat true true ∅
              ltac:(lia) Hj Hgamma (locks_below_empty "log")
              with "Hcg Hcpu Htcx Hccx Htext Hpc Hlog Hprocs").
    iIntros (CIDy Hsy mf) "%Hcs %Hr0 Hcg Hcpu _ _ Hpc".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V
              ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE THIRTEENTH ARM: k = 8, [sys_fstat].  The entry the file header
     called obstacle (2) -- "a CONSUMED-AND-NOT-RETURNED environment" -- and
     the obstacle is gone for a reason worth recording: [filestat_fs_env] is
     PERSISTENT except for two rows (the [sb_inodestart] fraction and one
     [bslot]), and those two are EXACTLY [filestat_fs_out].  So the arm does
     not have to hand the environment back at all: it rebuilds it from
     [fs_ready] (persistent, still in hand) plus what the postcondition
     returns.  [sysc_filestat_env] is that carve-and-regather, and the
     "shape decision" the header warned about ([syscall_env] would stop
     being fully persistent) never arises. *)
  Lemma sysc_arm_write (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 16 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 16) : mword 64)
                   = mword_of_int KernelSyms.sys_write) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (procs_inv_len with "Hprocs") as "%Hlen".
    (* the two trapframe argument words -- only their EXISTENCE is asked *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    (* the count, the third trapframe word.  [SpecSysWrite] takes no numeric
       premise about it at all: 31f115a's guard in filewrite makes [0 <= n] a
       fact of the code, so the syscall says nothing about what the user
       wrote there. *)
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 2)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v2 Hv2].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    (* [printk_env] is taken HERE and not out of [syscall_env_all]: that
       projection closes over the uart/disk names existentially, so its
       [is_txlock] would be at a gname nothing ties to [fcn_uart fn].  This
       one states it at the record's own names. *)
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ &
        _ & #Hpanic & _ & _ & _ & _ & #Hdevi & _ & _ &
        _ & _ & _ & _ & _ & _ & _ & _ & #Hpe )".
    (* filewrite's FD_INODE arm is the whole log cone, so it wants all THREE
       block slots -- unlike fstat/read, which take one and hand it back. *)
    (* filewrite's DEVICE arm wants the TX lock, not the cons lock --
       consolewrite drives the UART -- so what is destructed here is
       [printk_env]'s own existential.  The console table still comes from
       [console_ready], but without its gname: the write column does not
       mention it. *)
    iDestruct (syscall_env_console with "Henvc") as "#Hcr".
    iPoseProof (ConsoleInv.console_ready_devsw with "Hcr") as "#Htbl".
    iDestruct "Hpe" as "(_ & _ & _ & Hxl & _)".
    iDestruct "Hxl" as (γtxl) "#Htx".
    (* the ambient log, named: filewrite's FD_INODE arm write-locks inside
       its own transaction and the escrow parks at [icfg_log] (durable-disk
       B''-tx).  [sysc_ties] has said so all along. *)
    iDestruct (sysc_fs_env_ties with "Hfsenv") as %Twr.
    iAssert (SpecFilewrite.filewrite_dev_caps
               (sysc_fwrite_names fsc_printk γtxl γs j γl bn fn)) as "#Hcaps".
    { rewrite /SpecFilewrite.filewrite_dev_caps /sysc_fwrite_names; cbn.
      iSplitR; [iExact "Hdevi" | iExact "Htx"]. }
    iDestruct (sysc_filewrite_env γf γtxl γs j γl (proc_addr j) bn fn
                 with "Hdata Htx Hfsenv Hbs") as "Hfse".
    iApply (SysWrite.wp_sys_write_sconf γa γf γs j γl
              (sysc_fwrite_names fsc_printk γtxl γs j γl bn fn)
              pid V v0 v2 M (av - 4)%nat true true ∅
              ltac:(lia) Hj Hgamma Hlen eq_refl eq_refl Hv0
              (ex_intro _ v1 Hv1) Hv2 eq_refl eq_refl eq_refl
              with "Hcg Hcpu Htext Hdata Hpc Hpanic Hpriv Hkalloc Hprocs
                    Hfse Hcaps Htbl").
    iIntros (CIDy Hsy mf r P') "%Hcs %Hext %Hret' %Hmfa0 Hcg Hcpu Hpc Hpriv _ Hout".
    (* NOTHING ABOUT THE BITMAP COMES BACK any more -- filewrite's FD_INODE
       arm ballocs, and the pool it draws from is an invariant now, so the
       postcondition says nothing about which blocks are in use.  The three
       superblock cells are DISCARDED, hence dropped here; the three block
       slots are the whole of the out-bundle the arm still needs. *)
    rewrite /SpecFilewrite.filewrite_fs_out /sysc_fwrite_names; cbn.
    iDestruct "Hout" as "(_ & _ & _ & Hbs)".
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _). cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r' : mword 5, is_cs_idx r' = true ->
              r' <> csp_rs1 -> r' <> Rs0 -> r' <> Rs1 -> r' <> Rs2 ->
              mf !!! Regidx r' = m !!! Regidx r').
    { intros r' Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r' Hr). exact (HMother r' Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  Lemma sysc_arm_read (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 5 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 5) : mword 64)
                   = mword_of_int KernelSyms.sys_read) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (procs_inv_len with "Hprocs") as "%Hlen".
    (* the two trapframe argument words -- only their EXISTENCE is asked *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    (* sys_read reads a THIRD trapframe word -- the count -- and says nothing
       about it: [SpecSysRead] takes no numeric premise at all, because the
       guard 31f115a added to fileread makes [0 <= n] a fact of the code. *)
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 2)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v2 Hv2].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ &
        _ & #Hpanic & _ )".
    (* the environment, carved out of [fs_ready] plus one slot unit *)
    iDestruct (sysc_bslot_split with "Hbs") as "[Hsl Hbs2]".
    (* THE CONSOLE, destructed ONCE: the arm builds the names record around
       the gname it gets, which is the whole reason [console_ready] hides it
       rather than [fclose_names] carrying it. *)
    iDestruct (syscall_env_console with "Henvc") as (γc) "#Hci".
    iDestruct (sysc_fileread_env γf γc (proc_addr j) bn fn with "Hfsenv Hsl")
      as "[Hfse Hback]".
    iApply (SysRead.wp_sys_read_sconf γa γf γs j γl (sysc_fread_names γc bn fn)
              pid V v0 v2 M (av - 4)%nat true true ∅
              ltac:(lia) Hj Hgamma Hlen Hv0 (ex_intro _ v1 Hv1) Hv2
              eq_refl eq_refl eq_refl
              with "Hcg Hcpu Htext Hdata Hpc Hpanic Hpriv Hkalloc Hprocs Hfse Hci").
    iIntros (CIDy Hsy mf r P') "%Hcs %Hext %Hret' %Hmfa0 Hcg Hcpu Hpc Hpriv _ Hout".
    iDestruct ("Hback" with "Hout") as "Hsl".
    iDestruct (sysc_bslot_join with "Hsl Hbs2") as "Hbs".
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _). cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r' : mword 5, is_cs_idx r' = true ->
              r' <> csp_rs1 -> r' <> Rs0 -> r' <> Rs1 -> r' <> Rs2 ->
              mf !!! Regidx r' = m !!! Regidx r').
    { intros r' Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r' Hr). exact (HMother r' Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  Lemma sysc_arm_fstat (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 8 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 8) : mword 64)
                   = mword_of_int KernelSyms.sys_fstat) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (procs_inv_len with "Hprocs") as "%Hlen".
    (* the two trapframe argument words -- only their EXISTENCE is asked *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ &
        _ & #Hpanic & _ )".
    (* the environment, carved out of [fs_ready] plus one slot unit *)
    iDestruct (sysc_bslot_split with "Hbs") as "[Hsl Hbs2]".
    iDestruct (sysc_filestat_env (proc_addr j) bn fn with "Hfsenv Hsl")
      as "[Hfse Hback]".
    iApply (SysFstat.wp_sys_fstat_sconf γa γf γs j γl (sysc_fstat_names bn fn)
              pid V v0 M (av - 4)%nat true true ∅
              ltac:(lia) Hj Hgamma Hlen Hv0 (ex_intro _ v1 Hv1) eq_refl
              with "Hcg Hcpu Htext Hdata Hpc Hpanic Hpriv Hkalloc Hprocs Hfse").
    iIntros (CIDy Hsy mf r P') "%Hcs %Hext %Hret' %Hmfa0 Hcg Hcpu Hpc Hpriv _ Hout".
    iDestruct ("Hback" with "Hout") as "Hsl".
    iDestruct (sysc_bslot_join with "Hsl Hbs2") as "Hbs".
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _). cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r' : mword 5, is_cs_idx r' = true ->
              r' <> csp_rs1 -> r' <> Rs0 -> r' <> Rs1 -> r' <> Rs2 ->
              mf !!! Regidx r' = m !!! Regidx r').
    { intros r' Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r' Hr). exact (HMother r' Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE FOURTEENTH ARM: k = 9, [sys_chdir].  The first of the four
     create/namei-family entries, and the ONE of them whose reference ledger
     CLOSES ([SpecSysChdir.v]'s header: [iref_slots 2] goes in and comes back
     out unchanged on all four arms, because the reference namei made is
     iput's on the failure arms and REPLACES [p->cwd]'s on the success arm,
     whose old one is iput as well).  That is what lets the dispatch hand it
     half its own [IREFSPARE] allowance and get the half back. *)
  Lemma sysc_arm_chdir (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 9 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 9) : mword 64)
                   = mword_of_int KernelSyms.sys_chdir) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & #Hpanic & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iDestruct (sysc_iref_split with "Hir") as "[Hirk Hirc]".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iApply (SysChdir.wp_sys_chdir_sconf γf γa γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 (fcn_size fn)
              DfracDiscarded DfracDiscarded v0 pid V M (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hib Hj Hgamma eq_refl Hv0
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpanic Hbio Hlog Hseam
                    Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg
                    Hropen Hbmp Hisp Hbmr Hkalloc Hprocs Hirc Hpriv").
    iIntros (CIDy Hsy mf P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ Hirc Hpost".
    (* the two arms of [sys_chdir_post] differ only in [V'], and neither
       moves the trapframe page: [upd_cwd] does not touch [pv_upt] at all. *)
    iAssert (∃ V' : pprivate,
               ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗
               (* ...and the fd-state ghost name: chdir moves neither *)
               ⌜pv_fdg V' = pv_fdg V⌝ ∗
               proc_priv γf (proc_addr j) pid V')%I with "[Hpost]" as
      (V') "(%Htfp' & %Hfg' & Hpriv)".
    { destruct Hext as (_ & Htf & _).
      iDestruct "Hpost" as "[[_ Hpv] | (%ipv & _ & Hpv)]".
      - iExists (upd_upt V P'). iFrame "Hpv". iSplitR; iPureIntro.
        + cbn [pv_upt upd_upt pv_fdg]. exact Htf.
        + reflexivity.
      - iExists (upd_cwd (upd_upt V P') ipv). iFrame "Hpv". iSplitR; iPureIntro.
        + cbn [pv_upt upd_upt upd_cwd pv_fdg]. exact Htf.
        + reflexivity. }
    iDestruct (sysc_iref_join with "Hirk Hirc") as "Hir".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V'
              ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE FIFTEENTH AND SIXTEENTH ARMS: k = 18, [sys_unlink] and k = 19,
     [sys_link].  The two directory-mutating entries, and they are the same
     arm twice over: identical premise lists (the icache's four ties, the
     block layer's nine geometry facts, mkfs's [ushort] tie and the printk
     contract balloc's out-of-blocks arm needs), identical resource lists,
     and identical postconditions except for how much of the allowance the
     walk borrows -- TWO for unlink's single resolve, THREE for link's pair.
     Both ledgers CLOSE ([SpecSysLink.v] / [SpecSysUnlink.v] headers), which
     is what lets the dispatch split its own [IREFSPARE] and get the split
     back.

     THE THREE ROWS THAT WERE MISSING BEFORE [fs_ready] are visible here:
     [sb_size] (no [fclose_names] field names it, so the old closer bundle
     never carried it), [bitmap_geom_ok] and the [ushort] tie.  All three now come
     off [sysc_fs_env_all]'s tail, out of [FsReady.fs_geom_ok] and
     [FsReady.fs_sb_cells]. *)
  Lemma sysc_arm_unlink (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 18 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 18) : mword 64)
                   = mword_of_int KernelSyms.sys_unlink) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ & %Hbg & %Hnin & _ & #Hsbs & %Hprg & #Hpr )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iDestruct (sysc_iref_split with "Hir") as "[Hirk Hiru]".
    iApply (SysUnlink.wp_sys_unlink_sconf γf γa fsc_printk γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 (fcn_size fn)
              DfracDiscarded DfracDiscarded DfracDiscarded v0 pid V M
              (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hbg Hib (proj2 (proj2 (proj2 Hnin))) Hprg Hj Hgamma
              eq_refl Hv0
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hbio Hlog Hseam
                    Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg
                    Hropen Hbmp Hisp Hsbs Hbmr Hkalloc Hprocs Hiru Hpriv").
    iIntros (CIDy Hsy mf P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ _ Hiru Hpriv %Hrv".
    iDestruct (sysc_iref_join with "Hirk Hiru") as "Hir".
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _). cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.


  Lemma sysc_arm_link (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 19 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 19) : mword 64)
                   = mword_of_int KernelSyms.sys_link) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ & %Hbg & %Hnin & _ & #Hsbs & %Hprg & #Hpr )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iDestruct (sysc_iref_split3 with "Hir") as "[Hirl Hirk]".
    iApply (SysLink.wp_sys_link_sconf γf γa fsc_printk γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 (fcn_size fn)
              DfracDiscarded DfracDiscarded DfracDiscarded v0 v1 pid V M
              (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hbg Hib (proj2 (proj2 (proj2 Hnin))) Hprg Hj Hgamma
              eq_refl Hv0 Hv1
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hbio Hlog Hseam
                    Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg
                    Hropen Hbmp Hisp Hsbs Hbmr Hkalloc Hprocs Hirl Hpriv").
    iIntros (CIDy Hsy mf P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ _ Hirl Hpriv %Hrv".
    iDestruct (sysc_iref_join3 with "Hirl Hirk") as "Hir".
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V)).
    { destruct Hext as (_ & Htf & _). cbn [pv_upt upd_upt pv_fdg]. exact Htf. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE SEVENTEENTH ARM: k = 21, [sys_close].  The entry whose contract had
     to CHANGE before it could be wired at all, and the change was a
     correctness fix rather than a convenience: it used to take
     [fileclose_fs_env], whose pid quarter no holder of [proc_priv] can also
     own (SpecSysClose.v's own note now records why).  It takes the NOPID
     bundle and lends the quarter out of its own process block, so what the
     dispatch owes is exactly what the dispatch has. *)
  Lemma sysc_arm_close (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 21 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 21) : mword 64)
                   = mword_of_int KernelSyms.sys_close) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & #Hftable & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_ties with "Hfsenv") as "%T".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hpanic & _ )".
    iPoseProof (sysc_fclose_pipe_env (proc_addr j) bn fn with "Hfsenv") as "#Hpenv".
    iDestruct (sysc_fclose_fs_env (proc_addr j) bn fn true
                 with "Hfsenv Hbs") as "Hfenv".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    (* fileclose's loan, out of the dispatch's four spare iref units and
       straight back in below -- see [SpecFileclose]'s [iref_slot] row. *)
    iDestruct (sysc_iref_split3 with "Hir") as "[Hir Hiru]".
    iApply (SysClose.wp_sys_close_sconf γft γf fn None M (av - 4)%nat 0%nat
              true (proc_addr j) v0 pid V true ∅
              Hv0 ltac:(cbn; lia) ltac:(lia) (locks_below_empty "log")
              Hpidt (sct_dq _ _ _ T)
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hftable Hpanic Hpriv
                    Hufrag Hiru Hpenv Hfenv").
    iIntros (CIDy Hsy mf) "%Hcs Hcg Hcpu _ _ Hpc Hpost Hpe' Hfe' Hiru".
    (* the three block slots, back out of the nopid bundle.  THE BITMAP DOES
       NOT COME WITH THEM any more -- it is an invariant, so the bundle never
       had to give it back and the post no longer quantifies a used-set. *)
    iDestruct (sysc_fclose_fs_out bn fn 0%nat true (proc_addr j)
                 (sct_bio _ _ _ T) with "Hfe'") as "Hbs".
    iAssert (∃ V' : pprivate,
               ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗
               (* ...and the ghost name: close retypes a descriptor, not the
                  process's fd-state identity *)
               ⌜pv_fdg V' = pv_fdg V⌝ ∗
               proc_priv γf (proc_addr j) pid V' ∗ fd_frags_any (pv_fdg V))%I
      with "[Hpost]" as (V') "(%Htfp' & %Hfg' & Hpriv & Hufrag)".
    { iDestruct "Hpost" as "[[_ [Hpv Hfr]] | (%fd & %fv & _ & [Hpv Hfr])]".
      - iExists V. iFrame "Hpv Hfr". iSplitR; iPureIntro; reflexivity.
      - iExists (upd_ofile V fd (zero_reg : mword 64)). iFrame "Hpv Hfr".
        iSplitR; iPureIntro; cbn [pv_upt upd_ofile pv_fdg]; reflexivity. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V'
              ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd [Hir Hiru] Henv Hpriv Hufrag Hpc Hcont").
    iApply (sysc_iref_join3 with "Hir Hiru").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ENTRY 4, `pipe`.  Shaped exactly like `sysc_arm_close` -- both close
     descriptors they took back out of the fd table, so both carry BOTH of
     fileclose's bundles and let the type select -- with three differences,
     all of them visible in the [with] list:

       - it needs [kalloc_env], because pipealloc allocates the pipe page and
         copyout's vmfault allocates again.  It comes off the environment
         like everything else ([syscall_env_all]'s first conjunct).
       - it takes TWO of the four spare fd units.  sys_pipe can hold two
         references in locals before either reaches a descriptor; both come
         back in its post, which is why [sysc_ret_tail] gets [FDSPARE] again.
       - its post moves the page table.  copyout writes the two descriptor
         numbers into user memory and may fault a page in on the way, so the
         block returns at [upd_upt V P'] rather than at [V] -- and the
         trapframe page, which is what the epilogue's [Rs2] names, is pinned
         by [uptd_ext]'s own second conjunct.

     THE PID FRACTION USED TO BLOCK THIS ENTRY and no longer does: this
     contract takes the NOPID bundle beside [proc_priv] and lends the block
     out of it at each fileclose call.  Its two remaining tie premises are
     discharged the way sys_close's are -- [fcn_pid] from the dispatch's own
     [Hpidt], [fcn_dq] off the [sysc_ties] record. *)
  Lemma sysc_arm_pipe (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 4 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 4) : mword 64)
                   = mword_of_int KernelSyms.sys_pipe) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    (* syscall argument 0 -- the user address of the two-int array -- out of
       the trapframe page the block carries.  Nothing is assumed about it;
       copyout is the check. *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & #Hftable & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_ties with "Hfsenv") as "%T".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hpanic & _ )".
    iPoseProof (sysc_fclose_pipe_env (proc_addr j) bn fn with "Hfsenv") as "#Hpenv".
    iDestruct (sysc_fclose_fs_env (proc_addr j) bn fn true
                 with "Hfsenv Hbs") as "Hfenv".
    (* two of the four spare units out, and the same two back below *)
    iDestruct (fd_slots_split 1 3 with "Hfd") as "[Hfd0 Hfd]".
    iDestruct (fd_slots_split 1 2 with "Hfd") as "[Hfd1 Hfd]".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    (* fileclose's loan -- see [SpecFileclose]'s [iref_slot] row.  sys_pipe
       reaches fileclose on three error paths and through pipealloc, and one
       unit serves them all. *)
    iDestruct (sysc_iref_split3 with "Hir") as "[Hir Hiru]".
    iApply (SysPipe.wp_sys_pipe_sconf γa γft γf fn None M (av - 4)%nat
              true (proc_addr j) v0 pid V true ∅
              Hv0 ltac:(lia) (locks_below_empty "log")
              Hpidt (sct_dq _ _ _ T)
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpanic Hftable Hkalloc
                    Hpriv Hufrag Hfd0 Hfd1 Hiru Hpenv Hfenv").
    iIntros (CIDy Hsy mf P') "%Hcs %Hupt Hcg Hcpu _ _ Hpc Hpost Hiru Hpe' Hfe'".
    (* the three block slots, back out of the nopid bundle.  THE BITMAP DOES
       NOT COME WITH THEM any more -- it is an invariant, so the bundle never
       had to give it back and the post no longer quantifies a used-set. *)
    iDestruct (sysc_fclose_fs_out bn fn 0%nat true (proc_addr j)
                 (sct_bio _ _ _ T) with "Hfe'") as "Hbs".
    iDestruct "Hpost" as "(Hpv & Hufrag & Hfd0 & Hfd1)".
    iDestruct (fd_slots_combine 1 2 with "Hfd1 Hfd") as "Hfd".
    iDestruct (fd_slots_combine 1 3 with "Hfd0 Hfd") as "Hfd".
    (* BOTH ARMS RETURN THE BLOCK, and the epilogue needs only that its
       trapframe page has not moved -- which is [uptd_ext]'s own second
       conjunct, at whichever [V'] the arm hands back. *)
    destruct Hupt as (_ & Htfpe & _).
    iAssert (∃ V' : pprivate,
               ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗
               (* ...and the ghost name: pipe opens descriptors, it does not
                  reassign the process's fd-state identity *)
               ⌜pv_fdg V' = pv_fdg V⌝ ∗
               proc_priv γf (proc_addr j) pid V')%I with "[Hpv]" as
      (V') "(%Htfp' & %Hfg' & Hpriv)".
    { iDestruct "Hpv" as
        "[[_ Hpv] | (%fd0 & %fd1 & %l & %k0 & %k1 & _ & Hpv)]".
      - iExists (upd_upt V P'). iFrame "Hpv". iSplitR; iPureIntro.
        + cbn [pv_upt upd_upt pv_fdg]. exact Htfpe.
        + reflexivity.
      - iExists (upd_ofile (upd_ofile (upd_upt V P') fd0 (fnode k0)) fd1 (fnode k1)).
        iFrame "Hpv". iSplitR; iPureIntro.
        + cbn [pv_upt upd_ofile upd_upt pv_fdg]. exact Htfpe.
        + reflexivity. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hret : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V'
              ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd [Hir Hiru] Henv Hpriv Hufrag Hpc Hcont").
    iApply (sysc_iref_join3 with "Hir Hiru").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ENTRIES 20 and 17, `mkdir` and `mknod` -- the two create-family entries
     whose ledgers CLOSE.  They are one arm twice over: identical premise
     lists (the icache's four ties, the block layer's nine geometry facts,
     mkfs's inode geometry and the printk credential pair ialloc's
     out-of-inodes arm needs) and identical resource lists, differing only in
     how many syscall arguments they read -- one for mkdir, three for mknod.

     WHAT USED TO BLOCK THEM was debt (A) in this file's header, and only
     half of it: create returned its slot ledger as the INTERVAL
     [ns - create_slots <= ns' <= ns], while `wp_syscall_sconf_body` hands
     out [iref_slots IREFSPARE] and must get IREFSPARE back -- it must,
     because [UsertrapRes.ut_own] carries the allowance at that literal and
     the trap loop gets its residue back unchanged, so a leak of one unit per
     mkdir would break the Löb invariant.  The header also recorded that the
     fact was TRUE and only the statement weak, and that tightening it was
     create's job.  It is done: [SpecCreate]'s post states the figure
     exactly ([if ok then S ns' = ns else ns' = ns]) -- all nine of its
     continuation sites already computed it and then weakened -- so
     mkdir's and mknod's own posts say [ns' = ns] and this arm can pass the
     whole allowance in and take the whole allowance out.

     NO SPLIT of [iref_slots], unlike the chdir/link/unlink arms: create
     wants [create_slots = 3] and IREFSPARE is 4, so the entry takes the
     ledger whole.  Both superblock cells create needs beyond the two in
     the old closer bundle -- [sb_ninodes] and [sb_size] -- come off [fs_ready] at
     [DfracDiscarded], which is the second of the four rows the old
     twenty-five-conjunct environment could not state at all. *)
  Lemma sysc_arm_mkdir (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 20 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 20) : mword 64)
                   = mword_of_int KernelSyms.sys_mkdir) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ & %Hbmgeo & %Hnin & #Hsbn & #Hsbs &
        %Hprg & #Hpr )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    destruct Hnin as (Hn1 & Hn2 & Hn3 & Hn4).
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iApply (SysMkdir.wp_sys_mkdir_sconf γf γa fsc_printk γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 fsc_ninodes (fcn_size fn)
 IREFSPARE
              DfracDiscarded DfracDiscarded DfracDiscarded DfracDiscarded
              v0 pid V M (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hbmgeo Hib Hn1 Hn2 Hn3 Hn4 Hprg
              ltac:(compute; lia) Hj Hgamma eq_refl Hv0
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hbio Hlog Hseam
                    Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg
                    Hropen Hsbn Hisp Hsbs Hbmp Hbmr Hkalloc Hprocs Hir Hpriv").
    iIntros (CIDy Hsy mf ns' P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ _ _ %Hns Hir Hpriv %Hret0".
    (* THE LEDGER CLOSES: [ns' = ns = IREFSPARE], so what the epilogue hands
       on is the allowance the trap loop expects, unchanged. *)
    subst ns'.
    (* the trapframe page has not moved -- [uptd_ext]'s own second conjunct *)
    destruct Hext as (_ & Htfpe & _).
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V))
      by (cbn [pv_upt upd_upt pv_fdg]; exact Htfpe).
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hretpc : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hretpc) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ENTRY 17, `mknod` -- [sysc_arm_mkdir]'s twin.  The only difference is
     that it reads THREE syscall arguments (path, major, minor) where mkdir
     reads one, so it takes three [tf_arg_idx] witnesses out of the same
     trapframe page.  Everything else -- premise list, resource list,
     postcondition, and the ledger that closes at [IREFSPARE] -- is the
     same; see [sysc_arm_mkdir] for why the entry is wirable at all. *)
  Lemma sysc_arm_mknod (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 17 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 17) : mword 64)
                   = mword_of_int KernelSyms.sys_mknod) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 2)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v2 Hv2].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & _ & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ & %Hbmgeo & %Hnin & #Hsbn & #Hsbs &
        %Hprg & #Hpr )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    destruct Hnin as (Hn1 & Hn2 & Hn3 & Hn4).
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iApply (SysMknod.wp_sys_mknod_sconf γf γa fsc_printk γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 fsc_ninodes (fcn_size fn)
 IREFSPARE
              DfracDiscarded DfracDiscarded DfracDiscarded DfracDiscarded
              v0 v1 v2 pid V M (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hbmgeo Hib Hn1 Hn2 Hn3 Hn4 Hprg
              ltac:(compute; lia) Hj Hgamma eq_refl Hv0 Hv1 Hv2
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hbio Hlog Hseam
                    Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg
                    Hropen Hsbn Hisp Hsbs Hbmp Hbmr Hkalloc Hprocs Hir Hpriv").
    iIntros (CIDy Hsy mf ns' P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ _ _ %Hns Hir Hpriv %Hret0".
    (* THE LEDGER CLOSES: [ns' = ns = IREFSPARE], so what the epilogue hands
       on is the allowance the trap loop expects, unchanged. *)
    subst ns'.
    (* the trapframe page has not moved -- [uptd_ext]'s own second conjunct *)
    destruct Hext as (_ & Htfpe & _).
    assert (Htfp' : ud_tfp (pv_upt (upd_upt V P')) = ud_tfp (pv_upt V))
      by (cbn [pv_upt upd_upt pv_fdg]; exact Htfpe).
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt (upd_upt V P')))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hretpc : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hretpc) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V
              (upd_upt V P') ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' ltac:(reflexivity)
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ENTRY 15, `open`.  The create-family shape (`mkdir`/`mknod`) with two
     differences, both of them visible in the [with] list:

       - it takes ONE of the four spare fd units.  sys_open holds a
         reference in a local [struct file *f] between filealloc and
         fdalloc, and hands the unit back either way -- installed in the
         descriptor on success, freed by fileclose on the D-FAIL arm --
         which is why [sysc_ret_tail] gets [FDSPARE] again.
       - it needs [is_ftable], because filealloc, fdalloc and fileclose all
         run inside it.  It comes off the environment like everything else
         ([syscall_env_all]'s fifth conjunct, whose lock ghost is [γft]).

     THE IREF LEDGER USED TO BLOCK THIS ENTRY.  sys_open's contract said
     `ns - sys_open_slots <= ns' <= ns`, and this dispatch lends [IREFSPARE]
     and must get [IREFSPARE] back, so no instantiation could close.  The
     interval was an artefact: publishing a file releases the untyped
     entry's own unit in exchange for the inode reference it parks, so
     nothing is spent -- see [SpecSysOpen]'s post.  With the equality the
     arm is the same three lines every other create-family entry is. *)
  Lemma sysc_arm_open (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    sysc_arm_goal 15 γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav Hpidt.
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct "Hcont" as "[Hcont _]".
    assert (Hpce : (mword_of_int (sysc_target 15) : mword 64)
                   = mword_of_int KernelSyms.sys_open) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    iDestruct ("Hpvback" with "Htfc Htfp") as "Hpriv".
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v0 Hv0].
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 1)
                ltac:(rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia)) as [v1 Hv1].
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(#Hkalloc & _ & _ & _ & #Hftable & _ & _ & #Hfsenv)".
    iDestruct (sysc_fs_env_all with "Hfsenv") as
      "( %Hroot & %Hnib0 & _ & _ & _ & _ & _ &
        %Hlg & _ & _ & #Hbio & #Hlog & #Hseam & #Hgen & #Hdevi & #Hgeom &
        #Hdlock & _ & _ & _ & %Hbmgeo & %Hnin & #Hsbn & #Hsbs &
        %Hprg & #Hpr )".
    iDestruct (sysc_ic_env_of_ready with "Hfsenv") as
      "( %Hsize & %Hbm0 & %Hbmc & %Hbml & %Hist0 & %Hib & %Hcb &
        #Hit & #Hitinv & #Hesc & #Hireg & #Hropen & #Hsl2 )".
    destruct Hnin as (Hn1 & Hn2 & Hn3 & Hn4).
    iDestruct (sysc_bm_cells with "Hfsenv") as "(#Hbmp & #Hisp & #Hbmr)".
    (* the one fd unit the local [struct file *f] rides in, out of the four *)
    iDestruct (fd_slots_split 1 3 with "Hfd") as "[Hfd0 Hfd]".
    iPoseProof sysc_trap_ext_true as "Htcx".
    iPoseProof (sysc_claim_ext_true (proc_addr j)) as "Hccx".
    iApply (SysOpen.wp_sys_open_sconf γft γf γa fsc_printk γs j γl
              (fcn_uart fn) (fcn_disk fn) (fcn_dlock fn)
              (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) bn

              (fcn_bmapstart fn)
 fsc_ninodes (fcn_size fn)
 IREFSPARE
              DfracDiscarded DfracDiscarded DfracDiscarded DfracDiscarded
              v0 v1 pid V M (av - 4)%nat true true ∅
              ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
              Hbml Hist0 Hcb Hbmgeo Hib Hn1 Hn2 Hn3 Hn4 Hprg
              ltac:(compute; lia) Hj Hgamma eq_refl Hv0 Hv1
              with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hftable Hbio Hlog
                    Hseam Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2
                    Hireg Hropen Hsbn Hisp Hsbs Hbmp Hbmr Hkalloc Hprocs Hir
                    Hfd0 Hpriv Hufrag").
    iIntros (CIDy Hsy mf ns' P')
      "%Hcs %Hext Hcg Hcpu _ _ Hpc Hbs _ _ _ _ %Hns Hir Hpost".
    (* THE LEDGER CLOSES: [ns' = ns = IREFSPARE], so what the epilogue hands
       on is the allowance the trap loop expects, unchanged. *)
    subst ns'.
    (* the fd unit, back: installed in a descriptor on the success arm and
       freed by fileclose on the others, but a unit either way *)
    iDestruct "Hpost" as "(Hpv & Hufrag & Hfd0)".
    iDestruct (fd_slots_combine 1 3 with "Hfd0 Hfd") as "Hfd".
    (* the trapframe page has not moved -- [uptd_ext]'s own second conjunct *)
    destruct Hext as (_ & Htfpe & _).
    (* BOTH ARMS RETURN THE BLOCK, at a state that differs only in the
       descriptor array, which the epilogue does not read. *)
    iAssert (∃ V' : pprivate,
               ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗
               (* ...and the ghost name, which open does not move *)
               ⌜pv_fdg V' = pv_fdg V⌝ ∗
               proc_priv γf (proc_addr j) pid V')%I with "[Hpv]" as
      (V') "(%Htfp' & %Hfg' & Hpriv)".
    { iDestruct "Hpv" as "[[_ Hpv] | (%fd & %ll & %kf & _ & Hpv)]".
      - iExists (upd_upt V P'). iFrame "Hpv". iSplitR; iPureIntro.
        + cbn [pv_upt upd_upt pv_fdg]. exact Htfpe.
        + reflexivity.
      - iExists (upd_ofile (upd_upt V P') fd (fnode kf)). iFrame "Hpv".
        iSplitR; iPureIntro.
        + cbn [pv_upt upd_ofile upd_upt pv_fdg]. exact Htfpe.
        + reflexivity. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V'))).
    { rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
      rewrite Htfp'. exact HMs2. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcs r Hr). exact (HMother r Hr Ncsp N8 N9 N18). }
    assert (Hretpc : ret_pc (M !!! Regidx Rra)
                   = (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64))
      by (rewrite HMra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hretpc) in "Hpc".
    assert (Hcry : true = false \/ proc_addr j = zero_reg -> (CIDy : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDy true (proc_addr j) _ Hcry with "Hcont") as "Hcont".
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V'
              ∅ av m mf Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp' Hfg'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

  (* THE COMBINATOR.  One [decide (k = <literal>)] branch per wired entry,
     ahead of the generic placeholder: adding an arm is adding a branch, and
     nothing already wired moves.  Kept in THIS section (rather than beside
     the capstone) because the capstone applies it AFTER the [c.jalr]'s own
     hart crossing. *)
  Lemma sysc_arm_dispatch (k : nat) (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    (1 <= k <= 22)%nat ->
    sysc_arm_goal k γf pj γs j γl bn fn dqi ip pid V lks av m M.
  Proof.
    intro Hk.
    destruct (decide (k = 1%nat)) as [-> | Hne1].
    { exact (sysc_arm_fork γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 2%nat)) as [-> | Hne2].
    { exact (sysc_arm_exit γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 3%nat)) as [-> | Hne3].
    { exact (sysc_arm_wait γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 6%nat)) as [-> | Hne4].
    { exact (sysc_arm_kill γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 7%nat)) as [-> | Hne5].
    { exact (sysc_arm_exec γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 10%nat)) as [-> | Hne6].
    { exact (sysc_arm_dup γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 11%nat)) as [-> | Hne7].
    { exact (sysc_arm_getpid γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 12%nat)) as [-> | Hne8].
    { exact (sysc_arm_sbrk γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 13%nat)) as [-> | Hne9].
    { exact (sysc_arm_pause γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 14%nat)) as [-> | Hne10].
    { exact (sysc_arm_uptime γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 8%nat)) as [-> | Hne11].
    { exact (sysc_arm_fstat γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 9%nat)) as [-> | Hne12].
    { exact (sysc_arm_chdir γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 18%nat)) as [-> | Hne13].
    { exact (sysc_arm_unlink γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 19%nat)) as [-> | Hne14].
    { exact (sysc_arm_link γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 21%nat)) as [-> | Hne15].
    { exact (sysc_arm_close γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 22%nat)) as [-> | Hne16].
    { exact (sysc_arm_sync γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 4%nat)) as [-> | Hne17].
    { exact (sysc_arm_pipe γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 20%nat)) as [-> | Hne18].
    { exact (sysc_arm_mkdir γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 17%nat)) as [-> | Hne19].
    { exact (sysc_arm_mknod γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 15%nat)) as [-> | Hne20].
    { exact (sysc_arm_open γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 5%nat)) as [-> | Hne21].
    { exact (sysc_arm_read γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    destruct (decide (k = 16%nat)) as [-> | Hne22].
    { exact (sysc_arm_write γf pj γs j γl bn fn dqi ip pid V lks av m M). }
    (* EVERY ONE of the 22 is above, so with [Hk] this case is empty.  This
       is what retires [sysc_arm_placeholder] -- the tree's only [Admitted]. *)
    exfalso. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PRINTK FALLBACK (unknown syscall number), +0x40 .. +0x56, falling
     THROUGH into the shared epilogue -- it needs no [c.j], the block sits
     immediately above +0x58.

       printk("%d %s: unknown sys call %d\n", p->pid, p->name, num);
       p->trapframe->a0 = -1;

     Three things make it unlike a table arm.  (1) It reads [p] out of s1,
     not s2, at all three memory accesses ([&p->name] at +0x40, [p->pid] at
     +0x44, [p->trapframe] at +0x52), so the caller has to say what s1 holds
     -- a premise no returning arm needs, since those reach the trapframe
     through s2.  (2) The third vararg [num] is [a3], computed at +0x1a
     BEFORE the range check and never touched since; it costs nothing, since
     [PkANum]'s [pk_desc_res] is [True] and printk's contract constrains no
     vararg it is not told to walk.  (3) [p->name] is the one argument that
     does cost something: printk WALKS it, so it must be a real C string, and
     [ProcDefs.pname_cells] carries exactly that ([ProcGeom.pname_wf], "there
     is a NUL in the sixteen bytes", established at every write site).
     [CstringInv.bytes_string_split] turns it into the C string plus padding,
     and [sysc_pname_app] turns those bytes into the [string_pointsto]
     printk's [PkAStr] wants.  None of it is assumed.

     The WEAK general corollary [wp_printk_gen_sconf] is what is called (the
     one procdump's own loop uses): syscall makes no claim about what reached
     the UART, so the trace-carrying contract's [uart_sent_sub] postcondition
     would be pure overhead.  [printk_env] comes out of [syscall_env], the
     "pr" rank premise out of [cpu_own 0], and the 48-slot budget out of
     [K_syscall]'s own 82. *)
  Lemma sysc_fallback (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (bn : bio_names) (fn : fclose_names)
      (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) :
    (j < NPROC)%nat ->
    pj = proc_addr j ->
    M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    M !!! Regidx Rs1 = pj ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       M !!! Regidx r = m !!! Regidx r) ->
    (K_syscall <= av)%nat ->
    sysc_arm_pre γf pj γs bn fn dqi ip pid V lks (av - 4)%nat M
      (mword_of_int (KernelSyms.syscall + 0x40) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := KT1) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    kernel_data -∗
    sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hj Hpj HMsp HMs1 HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hip & Hfd & Hir & Hpriv & Hufrag)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct (syscall_env_all with "Henvc") as (γa γp γw γft γtk γpr γud γvd)
      "(_ & _ & _ & _ & _ & _ & #Hpenv & _)".
    (* ---- +0x40: addi a2,s1,344 -- a2 := &p->name ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x40)) Ra2 Rs1
              (mword_of_int 344 : mword 12) M (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_40 with "Htext"). }
    iIntros (CIDa Hsa) "Hcg Hpc".
    set (F0 := <[Regidx Ra2 := regval_into_reg
        (add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M).
    change (<[Regidx Ra2 := regval_into_reg
        (add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M) with F0.
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x40) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x44)) by pcw.
    iEval (rewrite Hp44) in "Hpc".
    assert (HF0a2 : F0 !!! Regidx Ra2 = p_name (proc_addr j) 0).
    { rewrite /F0 upd_eq. rgne. rewrite HMs1. unfold p_name.
      apply (f_equal (add_vec (proc_addr j))). apply bv_eq; vm_compute; reflexivity. }
    assert (HF0s1 : F0 !!! Regidx Rs1 = proc_addr j)
      by (rewrite /F0 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HF0sp : F0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4)
      by (rewrite /F0 upd_ne; [exact HMsp | vm_compute; discriminate]).
    (* ---- +0x44: c.lw a1,48(s1) -- a1 := p->pid ---- *)
    iDestruct (proc_priv_pid with "Hpriv") as "[Hpidc Hpidback]".
    assert (Ha44 : add_vec (rget F0 Rs1) (sign_extend' 64 (mword_of_int 48 : mword 12))
                   = p_pid (proc_addr j)).
    { rgne. rewrite HF0s1. reflexivity. }
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x44)) Ra1 Rs1
              (mword_of_int 48 : mword 12) F0 (av - 4)%nat pid true
              (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hpidc]").
    { iApply (syci_44 with "Htext"). }
    { iEval (rewrite Ha44). iExact "Hpidc". }
    iIntros (CIDb Hsb) "Hcg Hpc Hpidc".
    iEval (rewrite Ha44) in "Hpidc".
    iDestruct ("Hpidback" with "Hpidc") as "Hpriv".
    set (F1 := <[Regidx Ra1 := regval_into_reg (sign_extend' 64 (pid : mword 32))]> F0).
    change (<[Regidx Ra1 := regval_into_reg (sign_extend' 64 (pid : mword 32))]> F0) with F1.
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x44) : mword 64) 2
                   = mword_of_int (KernelSyms.syscall + 0x46)) by pcw.
    iEval (rewrite Hp46) in "Hpc".
    (* ---- +0x46 / +0x4a: a0 := the format string ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.syscall + 0x46)) Ra0
              (mword_of_int 5 : mword 20) F1 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_46 with "Htext"). }
    iIntros (CIDc Hsc) "Hcg Hpc".
    set (F2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.syscall + 0x46) : mword 64)
                 (auipc_off (mword_of_int 5 : mword 20)))]> F1).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.syscall + 0x46) : mword 64)
                 (auipc_off (mword_of_int 5 : mword 20)))]> F1) with F2.
    assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x46) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x4a)) by pcw.
    iEval (rewrite Hp4a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x4a)) Ra0 Ra0
              (mword_of_int 2750 : mword 12) F2 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_4a with "Htext"). }
    iIntros (CIDd Hsd) "Hcg Hpc".
    set (F3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (rget F2 Ra0) (sign_extend' 64 (mword_of_int 2750 : mword 12)))]> F2).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (rget F2 Ra0) (sign_extend' 64 (mword_of_int 2750 : mword 12)))]> F2) with F3.
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x4a) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x4e)) by pcw.
    iEval (rewrite Hp4e) in "Hpc".
    assert (HF3a0 : F3 !!! Regidx Ra0 = (mword_of_int sysc_fmt_a : mword 64)).
    { rewrite /F3 upd_eq. rgne. rewrite /F2 upd_eq.
      unfold sysc_fmt_a. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0x4e: jal ra,printk ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.syscall + 0x4e)) Rra
              (mword_of_int 2087976 : mword 21) F3 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (syci_4e with "Htext"). }
    iIntros (CIDe Hse) "Hcg Hpc".
    set (F4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64) 4)]> F3).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64) 4)]> F3) with F4.
    assert (Hjpk : add_vec (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087976 : mword 21))
                   = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Hjpk) in "Hpc".
    assert (HF4a0 : F4 !!! Regidx Ra0 = (mword_of_int sysc_fmt_a : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3a0 | vm_compute; discriminate]).
    assert (HF4s1 : F4 !!! Regidx Rs1 = proc_addr j).
    { rewrite /F4 upd_ne; [| vm_compute; discriminate].
      rewrite /F3 upd_ne; [| vm_compute; discriminate].
      rewrite /F2 upd_ne; [| vm_compute; discriminate].
      rewrite /F1 upd_ne; [| vm_compute; discriminate].
      exact HF0s1. }
    assert (HF4sp : F4 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite /F4 upd_ne; [| vm_compute; discriminate].
      rewrite /F3 upd_ne; [| vm_compute; discriminate].
      rewrite /F2 upd_ne; [| vm_compute; discriminate].
      rewrite /F1 upd_ne; [| vm_compute; discriminate].
      exact HF0sp. }
    assert (HF4va1 : pk_vararg F4 1%nat = p_name (proc_addr j) 0).
    { rewrite /pk_vararg.
      replace (mword_of_int (11 + Z.of_nat 1) : mword 5) with (Ra2 : mword 5)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite /F4 upd_ne; [| vm_compute; discriminate].
      rewrite /F3 upd_ne; [| vm_compute; discriminate].
      rewrite /F2 upd_ne; [| vm_compute; discriminate].
      rewrite /F1 upd_ne; [| vm_compute; discriminate].
      exact HF0a2. }
    assert (Hpc52 : ret_pc (F4 !!! Regidx Rra : mword 64)
                    = (mword_of_int (KernelSyms.syscall + 0x52) : mword 64))
      by (rewrite /F4 upd_eq; pcw).
    (* ---- p->name as a C STRING, derived not assumed: the invariant gives
       the NUL, [CstringInv] gives the split ---- *)
    iDestruct (sysc_priv_name with "Hpriv") as "(%Hnlen & Hnm & Hnmback)".
    (* [Hnwf] is the invariant [pname_cells] carries -- "there is a NUL in
       p->name" -- and [CstringInv.bytes_string_split] turns it into the C
       string plus padding that [printk("%s", ...)] wants. *)
    iDestruct (pname_cells_open with "Hnm") as "(%Hnwf & Hnm)".
    destruct (CstringInv.bytes_string_split (pv_name V) Hnwf) as (pad & Hsplit).
    set (nm := CstringInv.bytes_string (pv_name V)).
    assert (Hnonul : PrintkFmt.nonul nm = true)
      by apply CstringInv.bytes_string_nonul.
    iEval (rewrite Hsplit) in "Hnm".
    iDestruct (sysc_pname_app (proc_addr j) (DfracOwn 1) nm pad with "Hnm") as "[Hstr Hpad]".
    iPoseProof (sysc_fmt_str with "Hdata") as "Hfmt".
    iDestruct (cpu_own_transport CID CIDe 0%nat true (proc_addr j) true
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Printk.wp_printk_gen_sconf KT1 (CID := CIDe) γpr γud γvd F4 (av - 4)%nat true
              (proc_addr j) (dqf := DfracDiscarded) sysc_fmt
              [PkANum; PkAStr (DfracOwn 1) nm; PkANum] true ∅
              ltac:(lia) sysc_fmt_len sysc_fmt_nonul
              ltac:(rewrite sysc_fmt_kinds; reflexivity)
              ltac:(cbn [length]; lia) (locks_below_empty "pr")
              with "Hcg Htext Hdata Hpc Hcpu Hpenv [Hfmt] [Hstr]").
    { rewrite HF4a0. iExact "Hfmt". }
    { iApply (sysc_descs_mk F4 (p_name (proc_addr j) 0) nm (DfracOwn 1)
                HF4va1 Hnonul (sysc_name_nonzero j Hj) with "Hstr"). }
    iIntros (CIDf Hsf mf) "Hcg Hpc %Hcsp Hcpu Hfmt2 Hdescs".
    destruct Hcsp as [Hcs Hra0].
    iDestruct (sysc_descs_take F4 (p_name (proc_addr j) 0) nm (DfracOwn 1) HF4va1
                 with "Hdescs") as "Hstr".
    iDestruct (sysc_pname_app (proc_addr j) (DfracOwn 1) nm pad with "[Hstr Hpad]")
      as "Hnm"; [iFrame "Hstr Hpad"|].
    iEval (rewrite -Hsplit) in "Hnm".
    iDestruct (pname_cells_intro _ _ _ Hnwf with "Hnm") as "Hnm".
    iDestruct ("Hnmback" with "Hnm") as "Hpriv".
    iEval (rewrite Hpc52) in "Hpc".
    (* what the printk call preserved of the registers the tail still reads *)
    assert (Hmfs1 : mf !!! Regidx Rs1 = proc_addr j).
    { rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact HF4s1. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF4sp. }
    assert (Hmfrest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcs r Hr).
      rewrite /F4 upd_ne; [| congruence].
      rewrite /F3 upd_ne; [| congruence].
      rewrite /F2 upd_ne; [| congruence].
      rewrite /F1 upd_ne; [| congruence].
      rewrite /F0 upd_ne; [| congruence].
      exact (HMother r Hr Ncsp N8 N9 N18). }
    (* ---- the trapframe page, opened for the [-1] store ---- *)
    set (tfp := ud_tfp (pv_upt V)).
    iDestruct (sysc_tfp_valid with "Hpriv") as "%Hpv".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
    iPoseProof (pt_node_claim_from_static tfp Hpv with "Hkmapb") as "#Hptc".
    iDestruct (proc_priv_tf_upd with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    assert (Hi14 : (tf_arg_idx 0 < length (pv_tf V))%nat)
      by (rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia).
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0) Hi14) as [w0 Hw0].
    iDestruct (tf_page_word_upd_mem tfp (pv_tf V) (tf_arg_idx 0) w0
                 ltac:(vm_compute; lia) Hw0 with "Hptc Htfp") as "(Hcell & Hcback)".
    (* ---- +0x52: c.ld a5,88(s1) -- a5 := p->trapframe ---- *)
    assert (Ha52 : add_vec (rget mf Rs1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                   = p_trapframe (proc_addr j)).
    { rgne. rewrite Hmfs1. reflexivity. }
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x52)) Ra5 Rs1
              (mword_of_int 88 : mword 12) mf (av - 4)%nat (page_base tfp) true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Htfc]").
    { iApply (syci_52 with "Htext"). }
    { iEval (rewrite Ha52). iExact "Htfc". }
    iIntros (CIDg Hsg) "Hcg Hpc Htfc". iEval (rewrite Ha52) in "Htfc".
    set (G0 := <[Regidx Ra5 := regval_into_reg (page_base tfp)]> mf).
    change (<[Regidx Ra5 := regval_into_reg (page_base tfp)]> mf) with G0.
    assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x52) : mword 64) 2
                   = mword_of_int (KernelSyms.syscall + 0x54)) by pcw.
    iEval (rewrite Hp54) in "Hpc".
    assert (HG0a5 : G0 !!! Regidx Ra5 = page_base tfp) by (rewrite /G0 upd_eq; reflexivity).
    (* ---- +0x54: c.li a4,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.syscall + 0x54)) Ra4
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              G0 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (syci_54 with "Htext"). }
    iIntros (CIDh Hsh) "Hcg Hpc".
    set (G1 := <[Regidx Ra4 := regval_into_reg (mword_of_int (-1) : mword 64)]> G0).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int (-1) : mword 64)]> G0) with G1.
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x54) : mword 64) 2
                   = mword_of_int (KernelSyms.syscall + 0x56)) by pcw.
    iEval (rewrite Hp56) in "Hpc".
    assert (HG1a5 : G1 !!! Regidx Ra5 = page_base tfp)
      by (rewrite /G1 upd_ne; [exact HG0a5 | vm_compute; discriminate]).
    (* ---- +0x56: c.sd a4,112(a5) -- p->trapframe->a0 = -1 ---- *)
    assert (HG1a5r : rget G1 Ra5 = page_base tfp) by (rgne; exact HG1a5).
    iEval (rewrite -(sysc_tf_addr_112 tfp) -HG1a5r) in "Hcell".
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.syscall + 0x56)) Ra4 Ra5
              (mword_of_int 112 : mword 12) G1 (av - 4)%nat w0 true
              with "Hcg Hpc [] Hcell").
    { iApply (syci_56 with "Htext"). }
    iIntros (CIDi Hsi) "Hcg Hpc Hcell".
    iEval (rewrite HG1a5r (sysc_tf_addr_112 tfp)) in "Hcell".
    iDestruct ("Hcback" $! (rget G1 Ra4) with "Hcell") as "Htfp".
    iDestruct ("Hpvback" $! (<[tf_arg_idx 0 := rget G1 Ra4]> (pv_tf V))
                 with "Htfc Htfp") as "Hpriv".
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x56) : mword 64) 2
                   = mword_of_int (KernelSyms.syscall + 0x58)) by pcw.
    iEval (rewrite Hp58) in "Hpc".
    (* ---- the shared epilogue, at the hart the block ended on ---- *)
    assert (HG1sp : G1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite /G1 upd_ne; [| vm_compute; discriminate].
      rewrite /G0 upd_ne; [| vm_compute; discriminate]. exact Hmfsp. }
    assert (HG1rest : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              G1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /G1 upd_ne; [| congruence].
      rewrite /G0 upd_ne; [| congruence].
      exact (Hmfrest r Hr Ncsp N8 N9 N18). }
    assert (Hcri : true = false \/ proc_addr j = zero_reg -> (CIDi : CPU) = (CID : CPU))
      by wp_next_chain.
    iDestruct (wp_next_retarget CID CIDi true (proc_addr j) _ Hcri with "Hcont") as "Hcont".
    assert (Hcrfi : true = false \/ proc_addr j = zero_reg -> (CIDi : CPU) = (CIDf : CPU))
      by wp_next_chain.
    iDestruct (cpu_own_transport CIDf CIDi 0%nat true (proc_addr j) true Hcrfi
                 with "Hcpu") as "Hcpu".
    iApply (sysc_epilogue_tail (CID := CIDi) γf (proc_addr j) bn fn dqi ip pid V
              (upd_tf V (<[tf_arg_idx 0 := rget G1 Ra4]> (pv_tf V)))
              ∅ av m G1 HG1sp HG1rest ltac:(lia) eq_refl eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hip Hfd Hir Henv Hpriv Hufrag Hpc Hcont").
  Qed.

End SyscallArms.

(* ===================================================================== *)
(* S4 -- THE CAPSTONE. *)
Section SyscallMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* CAPSTONE.  The shared scaffolding (`sysc_arm_pre`/`sysc_hcont_ty`/
     `sysc_arm_goal`, the trapframe-extraction/bitvector-bridge lemmas, and
     `sysc_epilogue_tail`) is assembled here with the real PROLOGUE (frame
     push, the `myproc()` call, the two trapframe reads, the fused range
     check driving the data-dependent `k`, the address computation, the
     table read, the redundant `beqz`, the `c.jalr`) into a full dispatch:
     every one of the 22 table entries reaches `sysc_arm_goal k` for its
     own `k`, discharged by `sysc_arm_dispatch` -- twenty-two real arms, no
     placeholder and no `Admitted`.  A new arm would be one more
     `decide (k = <literal>)` branch inside that combinator and NOTHING here
     would move. *)
  Lemma wp_syscall_sconf (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string)
    : wp_syscall_sconf_body syscall_env γf γs j γl bn fn ip dqi m av pid V lks.
  Proof.
    cbv beta delta [wp_syscall_sconf_body].
    intros pcE pj ret_tgt Hj Hgamma Hav Hpidt.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hprocs Hbs Hip Hfd Hir HR Hpriv Hufrag Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 true ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (syci_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24". iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".  iDestruct "S4c" as (vr0) "Hr0".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (sysc_stk sp0 1 3); lia. }
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (sysc_stk sp0 2 2); lia. }
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (sysc_stk sp0 3 1); lia. }
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (sysc_stk sp0 4 0); lia. }
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (av - 4)%nat vr24 true with "Hcg Hpc [] [Hr24]").
    { iApply (syci_02 with "Htext"). }
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (av - 4)%nat vr16 true with "Hcg Hpc [] [Hr16]").
    { iApply (syci_04 with "Htext"). }
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (av - 4)%nat vr8 true with "Hcg Hpc [] [Hr8]").
    { iApply (syci_06 with "Htext"). }
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x08)) (mword_of_int 0 : mword 6) Rs2
              A0 (av - 4)%nat vr0 true with "Hcg Hpc [] [Hr0]").
    { iApply (syci_08 with "Htext"). }
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr0". }
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a: c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.syscall + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              A0 (av - 4)%nat true
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.syscall + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    assert (HA1sp : A1 !!! Regidx csp_rs1 = spd)
      by (rewrite /A1 upd_ne; [exact HcspA0 | vm_compute; discriminate]).
    (* +0x0c: jal ra,myproc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.syscall + 0x0c)) Rra (mword_of_int 2093122 : mword 21)
              A1 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (syci_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)]> A1).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)]> A1) with A2.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2093122 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd)
      by (rewrite /A2 upd_ne; [exact HA1sp | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID CID7 0%nat true pj true ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    (* ---- myproc(): a0 := p, callee-saved preserved ---- *)
    iApply (Myproc.wp_myproc_sconf A2 (av - 4)%nat 0%nat true pj true lks
              ltac:(lia) ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID8 Hs8 ms MF) "%Hms Hcg Hcpu Hpc %HcsMF".
    destruct HcsMF as [HcsMF HMFa0].
    assert (Hp10 : ret_pc (A2 !!! Regidx Rra) = mword_of_int (KernelSyms.syscall + 0x10))
      by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    assert (HMFsp : MF !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup HcsMF csp_rs1 ltac:(vm_compute; reflexivity)). exact HA2sp. }
    (* ---- +0x10: c.mv s1,a0 -- s1 := p ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.syscall + 0x10)) Rs1 Ra0 MF (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_10 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B0 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (MF !!! Regidx Ra0))]> MF).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (MF !!! Regidx Ra0))]> MF) with B0.
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    assert (HB0a0 : B0 !!! Regidx Ra0 = pj)
      by (rewrite /B0 upd_ne; [exact HMFa0 | vm_compute; discriminate]).
    assert (HB0sp : B0 !!! Regidx csp_rs1 = spd)
      by (rewrite /B0 upd_ne; [exact HMFsp | vm_compute; discriminate]).
    (* ---- +0x12: ld s2,88(a0) -- s2 := p->trapframe ---- *)
    iDestruct "Hpriv" as "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hcwd) Hof]".
    rewrite {1}/proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    assert (Ha12 : add_vec (B0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 88 : mword 12)) = p_trapframe pj).
    { rewrite HB0a0. reflexivity. }
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x12)) Rs2 Ra0 (mword_of_int 88 : mword 12)
              B0 (av - 4)%nat (page_base (ud_tfp (pv_upt V))) true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Htfc]").
    { iApply (syci_12 with "Htext"). }
    { iEval (rewrite Ha12). iExact "Htfc". }
    iIntros (CID10 Hs10) "Hcg Hpc Htfc". iEval (rewrite Ha12) in "Htfc".
    set (B1 := <[Regidx Rs2 := regval_into_reg (page_base (ud_tfp (pv_upt V)))]> B0).
    change (<[Regidx Rs2 := regval_into_reg (page_base (ud_tfp (pv_upt V)))]> B0) with B1.
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    assert (HB1s2 : B1 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V))) by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spd)
      by (rewrite /B1 upd_ne; [exact HB0sp | vm_compute; discriminate]).
    (* ---- +0x16: ld a5,168(s2) -- a5 := RAWNUM = trapframe->a7 ---- *)
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    assert (Htf21is : is_Some (pv_tf V !! 21%nat)).
    { apply lookup_lt_is_Some_2. rewrite Htflen. unfold TFWORDS. lia. }
    destruct Htf21is as [RAWNUM Htf21].
    iDestruct (sysc_tfp_valid with "[Hpid Hf Hpg Htfc Hptt Htfp Hcwd Hof]") as "%Hpv".
    { iSplitL "Hpid Hf Hpg Htfc Hptt Htfp Hcwd"; [| iExact "Hof"].
      iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid Hf". iSplitL "Hpg Htfc Hptt"; [iFrame|iFrame]. }
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
    iPoseProof (pt_node_claim_from_static (ud_tfp (pv_upt V)) Hpv with "Hkmapb") as "#Hptc".
    iDestruct (tf_page_word_mem (ud_tfp (pv_upt V)) (pv_tf V) 21%nat RAWNUM ltac:(lia) Htf21 with "Hptc Htfp") as "[Htfw Htfwback]".
    assert (Ha16 : add_vec (B1 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 168 : mword 12)) = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat 21%nat)).
    { rewrite HB1s2 (tf_pa_eq_pa_add8 (ud_tfp (pv_upt V)) 21%nat ltac:(lia)).
      unfold pa_add, add_vec_int. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x16)) Ra5 Rs2 (mword_of_int 168 : mword 12)
              B1 (av - 4)%nat RAWNUM true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Htfw]").
    { iApply (syci_16 with "Htext"). }
    { iEval (rewrite Ha16). iExact "Htfw". }
    iIntros (CID11 Hs11) "Hcg Hpc Htfw". iEval (rewrite Ha16) in "Htfw".
    iDestruct ("Htfwback" with "Htfw") as "Htfp".
    set (B2 := <[Regidx Ra5 := regval_into_reg RAWNUM]> B1).
    change (<[Regidx Ra5 := regval_into_reg RAWNUM]> B1) with B2.
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spd)
      by (rewrite /B2 upd_ne; [exact HB1sp | vm_compute; discriminate]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /B2 upd_ne; [exact HB1s2 | vm_compute; discriminate]).
    (* ---- proc_priv reassembled: nothing above wrote to it ---- *)
    iAssert (proc_priv γf pj pid V) with "[Hpid Hf Hpg Htfc Hptt Htfp Hcwd Hof]" as "Hpriv".
    { iSplitL "Hpid Hf Hpg Htfc Hptt Htfp Hcwd"; [| iExact "Hof"].
      iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid Hf". iSplitL "Hpg Htfc Hptt"; [iFrame|iFrame]. }
    (* ---- +0x1a: addiw a3,a5,0 -- a3 := sext32(RAWNUM) ---- *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.syscall + 0x1a)) Ra3 Ra5 (mword_of_int 0 : mword 12)
              B2 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_1a with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (B3 := <[Regidx Ra3 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (rget B2 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> B2).
    change (<[Regidx Ra3 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (rget B2 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> B2) with B3.
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    set (a3num := sign_extend' 64 (subrange_vec_dec RAWNUM 31 0) : mword 64).
    assert (Himm0 : (mword_of_int 0 : mword 12) = zeros' 12) by (apply bv_eq; vm_compute; reflexivity).
    assert (HB3a3 : B3 !!! Regidx Ra3 = a3num).
    { rewrite /B3 upd_eq. rgne. rewrite /B2 upd_eq Himm0 add_vec_zeros_r. reflexivity. }
    assert (HB3sp : B3 !!! Regidx csp_rs1 = spd)
      by (rewrite /B3 upd_ne; [exact HB2sp | vm_compute; discriminate]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /B3 upd_ne; [exact HB2s2 | vm_compute; discriminate]).
    assert (HB3a5 : B3 !!! Regidx Ra5 = RAWNUM)
      by (rewrite /B3 upd_ne; [rewrite /B2 upd_eq; reflexivity | vm_compute; discriminate]).
    (* ---- +0x1e: c.addiw a5,a5,-1 -- the fused range check's own decrement ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.syscall + 0x1e)) Ra5 (mword_of_int 63 : mword 6)
              B3 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (syci_1e with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (B4 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (rget B3 Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> B3).
    change (<[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (rget B3 Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> B3) with B4.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HB4a5 : B4 !!! Regidx Ra5
        = sign_extend' 64 (subrange_vec_dec (add_vec a3num (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).
    { rewrite /B4 upd_eq. rgne. rewrite HB3a5. unfold a3num, regval_into_reg.
      f_equal. symmetry.
      exact (sysc_a3_bltu_bridge RAWNUM (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))). }
    assert (HB4sp : B4 !!! Regidx csp_rs1 = spd)
      by (rewrite /B4 upd_ne; [exact HB3sp | vm_compute; discriminate]).
    assert (HB4s2 : B4 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /B4 upd_ne; [exact HB3s2 | vm_compute; discriminate]).
    assert (HB4a3 : B4 !!! Regidx Ra3 = a3num)
      by (rewrite /B4 upd_ne; [exact HB3a3 | vm_compute; discriminate]).
    (* ---- +0x20: c.li a4,21 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.syscall + 0x20)) Ra4 (mword_of_int 21 : mword 6)
              (mword_of_int 21 : mword 64) B4 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (syci_20 with "Htext"). }
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (B5 := <[Regidx Ra4 := regval_into_reg (mword_of_int 21 : mword 64)]> B4).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int 21 : mword 64)]> B4) with B5.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HB5a4 : B5 !!! Regidx Ra4 = mword_of_int 21) by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a5 : B5 !!! Regidx Ra5 = B4 !!! Regidx Ra5)
      by (rewrite /B5 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HB5sp : B5 !!! Regidx csp_rs1 = spd)
      by (rewrite /B5 upd_ne; [exact HB4sp | vm_compute; discriminate]).
    assert (HB5s2 : B5 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /B5 upd_ne; [exact HB4s2 | vm_compute; discriminate]).
    assert (HB5a3 : B5 !!! Regidx Ra3 = a3num)
      by (rewrite /B5 upd_ne; [exact HB4a3 | vm_compute; discriminate]).
    (* ================= +0x22: bltu a4,a5 -- THE DATA-DEPENDENT SPLIT ==== *)
    destruct (decide (1 <= bv_signed a3num <= 22)%Z) as [Hrange | Hrange].
    - (* ---------------- IN RANGE: the real dispatch ---------------- *)
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.syscall + 0x22)) (mword_of_int 30 : mword 13) Ra5 Ra4
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate))
                              (rget_ne B5 Ra4 ltac:(vm_compute; discriminate))
                              HB5a5 HB4a5 HB5a4;
                      exact (sysc_bltu_fall a3num Hrange))
                with "Hcg Hpc []").
      { iApply (syci_22 with "Htext"). }
      iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      pose (k := Z.to_nat (bv_signed a3num)).
      assert (Hk : (1 <= k <= 22)%nat) by (unfold k; lia).
      assert (Hzk : Z.of_nat k = bv_signed a3num) by (unfold k; lia).
      assert (Ha3k : a3num = mword_of_int (Z.of_nat k)) by (rewrite Hzk; exact (sysc_a3_val a3num Hrange)).
      (* ---- +0x26: slli a4,a3,3 ---- *)
      iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.syscall + 0x26)) Ra4 Ra3 (mword_of_int 3 : mword 6)
                (shift_bits_left (B5 !!! Regidx Ra3) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc []").
      { iApply (syci_26 with "Htext"). }
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (C0 := <[Regidx Ra4 := regval_into_reg
          (shift_bits_left (B5 !!! Regidx Ra3) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> B5).
      change (<[Regidx Ra4 := regval_into_reg
          (shift_bits_left (B5 !!! Regidx Ra3) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> B5) with C0.
      assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2a) in "Hpc".
      assert (HC0a4 : C0 !!! Regidx Ra4
          = shift_bits_left (mword_of_int (Z.of_nat k) : mword 64) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)).
      { rewrite /C0 upd_eq HB5a3 -Ha3k. reflexivity. }
      assert (HC0sp : C0 !!! Regidx csp_rs1 = spd)
        by (rewrite /C0 upd_ne; [exact HB5sp | vm_compute; discriminate]).
      assert (HC0s2 : C0 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
        by (rewrite /C0 upd_ne; [exact HB5s2 | vm_compute; discriminate]).
      (* ---- +0x2a/+0x2e: a5 := &syscalls[0] ---- *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.syscall + 0x2a)) Ra5 (mword_of_int 5 : mword 20)
                C0 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (syci_2a with "Htext"). }
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (C1 := <[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> C0).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> C0) with C1.
      assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2e) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x2e)) Ra5 Ra5 (mword_of_int 3802 : mword 12)
                C1 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (syci_2e with "Htext"). }
      iIntros (CID18 Hs18) "Hcg Hpc".
      (* [rget], NOT [!!!]: [wp_addi4_s_sconf]'s continuation spells the written
         value at the hart-indexed read, so a [set] written with [!!!] folds
         NOTHING and the [change] behind it silently no-ops -- see the note at
         [C3] below for what that costs. *)
      set (C2 := <[Regidx Ra5 := regval_into_reg
          (add_vec (rget C1 Ra5) (sign_extend' 64 (mword_of_int 3802 : mword 12)))]> C1).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (rget C1 Ra5) (sign_extend' 64 (mword_of_int 3802 : mword 12)))]> C1) with C2.
      assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp32) in "Hpc".
      assert (HC2a5 : C2 !!! Regidx Ra5 = mword_of_int KernelSyms.syscalls).
      { rewrite /C2 upd_eq. rgne. rewrite /C1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HC2a4 : C2 !!! Regidx Ra4 = C0 !!! Regidx Ra4)
        by (rewrite /C2 upd_ne; [rewrite /C1 upd_ne; [reflexivity|vm_compute;discriminate] | vm_compute; discriminate]).
      assert (HC2sp : C2 !!! Regidx csp_rs1 = spd)
        by (rewrite /C2 upd_ne; [rewrite /C1 upd_ne; [exact HC0sp|vm_compute;discriminate] | vm_compute; discriminate]).
      assert (HC2s2 : C2 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
        by (rewrite /C2 upd_ne; [rewrite /C1 upd_ne; [exact HC0s2|vm_compute;discriminate] | vm_compute; discriminate]).
      (* ---- +0x32: c.add a5,a5,a4 -- a5 := &syscalls[num] ---- *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.syscall + 0x32)) Ra5 Ra4 C2 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (syci_32 with "Htext"). }
      iIntros (CID19 Hs19) "Hcg Hpc".
      (* [rget], NOT [!!!] -- THE MAP THE LEAF ACTUALLY HANDS BACK.
         [wp_cadd_s_sconf]'s continuation is [<[rd := regval_into_reg (add_vec
         (rget m rd) (rget m rs2))]> m], and [rget] is the HART-INDEXED read.
         Spelled with [!!!] here, [set] finds no occurrence to fold and the
         [change] behind it silently succeeds doing nothing, so "Hcg" keeps the
         unfolded [rget]-spelled map while every later step passes [C3].  The
         two are convertible ([regfile] is a FUNCTION and [rget] only reroutes
         [tp]), but the conversion has to normalise the whole insert chain down
         to the symbolic entry map at every nested read -- one level costs
         ~0.1 s at +0x32, two levels never returns, and the [iApply] at +0x34
         reads as an infinite loop with no error. *)
      set (C3 := <[Regidx Ra5 := regval_into_reg (add_vec (rget C2 Ra5) (rget C2 Ra4))]> C2).
      change (<[Regidx Ra5 := regval_into_reg (add_vec (rget C2 Ra5) (rget C2 Ra4))]> C2) with C3.
      assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp34) in "Hpc".
      assert (HC3a5 : C3 !!! Regidx Ra5 = mword_of_int (KernelSyms.syscalls + 8 * Z.of_nat k)).
      { rewrite /C3 upd_eq. rgne. rgne. rewrite HC2a5 HC2a4 HC0a4.
        exact (sysc_addr_word k Hk). }
      assert (HC3sp : C3 !!! Regidx csp_rs1 = spd)
        by (rewrite /C3 upd_ne; [exact HC2sp | vm_compute; discriminate]).
      assert (HC3s2 : C3 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
        by (rewrite /C3 upd_ne; [exact HC2s2 | vm_compute; discriminate]).
      (* ---- +0x34: c.ld a5,0(a5) -- THE TABLE READ ---- *)
      iPoseProof (sysc_table_word k Hk with "Hdata") as "#Hent".
      assert (Ha34 : add_vec (C3 !!! Regidx Ra5) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                     = mword_of_int (KernelSyms.syscalls + 8 * Z.of_nat k)).
      { rewrite HC3a5. apply kv_addv_zero. }
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x34)) Ra5 Ra5
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) C3 (av - 4)%nat
                (mword_of_int (sysc_target k) : mword 64) true
                (dqm := DfracDiscarded)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] []").
      { iApply (syci_34 with "Htext"). }
      { iEval (rewrite Ha34). iExact "Hent". }
      iIntros (CID20 Hs20) "Hcg Hpc _".
      set (C4 := <[Regidx Ra5 := regval_into_reg (mword_of_int (sysc_target k) : mword 64)]> C3).
      change (<[Regidx Ra5 := regval_into_reg (mword_of_int (sysc_target k) : mword 64)]> C3) with C4.
      assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp36) in "Hpc".
      assert (HC4a5 : C4 !!! Regidx Ra5 = mword_of_int (sysc_target k)) by (rewrite /C4 upd_eq; reflexivity).
      assert (HC4sp : C4 !!! Regidx csp_rs1 = spd)
        by (rewrite /C4 upd_ne; [exact HC3sp | vm_compute; discriminate]).
      assert (HC4s2 : C4 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
        by (rewrite /C4 upd_ne; [exact HC3s2 | vm_compute; discriminate]).
      (* ---- +0x36: c.beqz a5,+10 -- refuted by [sysc_target_nz] ---- *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.syscall + 0x36)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                C4 (av - 4)%nat true ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne C4 Ra5 ltac:(vm_compute; discriminate)) HC4a5;
                      apply eq_vec_false_iff; intro Hc; exact (sysc_target_nz k Hk Hc))
                with "Hcg Hpc []").
      { iApply (syci_36 with "Htext"). }
      iIntros (CID21 Hs21) "Hcg Hpc".
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".
      (* ---- +0x38: c.jalr a5 -- THE INDIRECT CALL ---- *)
      iApply (wp_cjalr_s_sconf (mword_of_int (KernelSyms.syscall + 0x38)) Ra5 Rra C4 (av - 4)%nat true
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (syci_38 with "Htext"). }
      iIntros (CID22 Hs22) "Hcg Hpc".
      set (D0 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x38) : mword 64) 2)]> C4).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x38) : mword 64) 2)]> C4) with D0.
      assert (Htgt : ret_pc (rget C4 Ra5) = mword_of_int (sysc_target k)).
      { rgne. rewrite HC4a5. exact (sysc_target_ret_pc k Hk). }
      iEval (rewrite Htgt) in "Hpc".
      assert (HD0ra : D0 !!! Regidx Rra = mword_of_int (KernelSyms.syscall + 0x3a)).
      { rewrite /D0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HD0sp : D0 !!! Regidx csp_rs1 = spd)
        by (rewrite /D0 upd_ne; [exact HC4sp | vm_compute; discriminate]).
      assert (HD0s2 : D0 !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)))
        by (rewrite /D0 upd_ne; [exact HC4s2 | vm_compute; discriminate]).
      (* ================= landed at [sysc_target k]: dispatch the arm ===== *)
      assert (HD0armsp : D0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4)
        by (rewrite HD0sp; exact Hspd4).
      assert (HD0avb : (K_syscall <= av)%nat)
        by (lia).
      assert (HD0other : forall r : mword 5, is_cs_idx r = true ->
          r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
          D0 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /D0 upd_ne; [| congruence].
        rewrite /C4 upd_ne; [| congruence].
        rewrite /C3 upd_ne; [| congruence].
        rewrite /C2 upd_ne; [| congruence].
        rewrite /C1 upd_ne; [| congruence].
        rewrite /C0 upd_ne; [| congruence].
        rewrite /B5 upd_ne; [| congruence].
        rewrite /B4 upd_ne; [| congruence].
        rewrite /B3 upd_ne; [| congruence].
        rewrite /B2 upd_ne; [| congruence].
        rewrite /B1 upd_ne; [| congruence].
        rewrite /B0 upd_ne; [| congruence].
        rewrite (callee_saved_lookup HcsMF r Hr).
        rewrite /A2 upd_ne; [| congruence].
        rewrite /A1 upd_ne; [| congruence].
        rewrite /A0 upd_ne; [| congruence].
        reflexivity. }
      iEval (rewrite HcspA0 -Hb1) in "Hr24". iEval (rewrite HcspA0 -Hb2) in "Hr16".
      iEval (rewrite HcspA0 -Hb3) in "Hr8".  iEval (rewrite HcspA0 -Hb4) in "Hr0".
      (* THE ARM IS STATED AT THE HART THE DISPATCH LANDS ON, not at the
         section's.  [Loop] names [cpu_id], so a section-level lemma's
         conclusion is RIGID at the section [CID] and can never meet a goal
         that this proof's own [wp_next] crossings have carried to [CID22]
         (the failure is [iApply: cannot apply (WP Loop)], naming neither
         hart).  Hence the [`{CIDh : CpuId}] on the arm vocabulary, exactly
         as [ProofArgraw.ar_join] carries its own -- and the caller's
         continuation, still anchored at [CID], is re-anchored here. *)
      assert (Hcr22 : true = false \/ pj = zero_reg -> (CID22 : CPU) = (CID : CPU))
        by wp_next_chain.
      (* the WHOLE slot crosses here -- the arm this resolves to may be the
         one that never returns, so the closer has to survive the crossing
         with the continuation *)
      iDestruct (sysc_exit_retarget CID CID22 γf pj bn fn dqi ip pid V lks av m
                   (ret_pc (m !!! Regidx Rra)) Hcr22 with "Hcont") as "Hcont".
      assert (Hcr8_22 : true = false \/ pj = zero_reg -> (CID22 : CPU) = (CID8 : CPU))
        by wp_next_chain.
      iDestruct (cpu_own_transport CID8 CID22 0%nat true pj true Hcr8_22 with "Hcpu") as "Hcpu".
      iApply (sysc_arm_dispatch (CID := CID22) k γf pj γs j γl bn fn dqi ip pid V lks av m D0 Hk
                Hj Hgamma eq_refl HD0armsp HD0s2 HD0ra HD0other HD0avb Hpidt
                with "[Hpc Hcg Hcpu Htext Hprocs HR Hbs Hip Hfd Hir Hpriv Hufrag] Hr24 Hr16 Hr8 Hr0 Hdata Hcont").
      { iApply (sysc_arm_pre_intro with
          "Hpc Hcg Hcpu Htext Hprocs HR Hbs Hip Hfd Hir Hpriv Hufrag"). }
    - (* ---------------- OUT OF RANGE: the printk fallback ---------------- *)
      (* [a3num]'s value fits in [mword 32]'s signed range by construction
         (it IS a sign-extended 32-bit value), so [sysc_bltu_taken]'s extra
         premise is free. *)
      assert (Ha3sig : (-2147483648 <= bv_signed a3num < 2147483648)%Z).
      { unfold a3num.
        pose proof (bv_signed_in_range 32%N (subrange_vec_dec RAWNUM 31 0 : mword 32)
                      ltac:(done)) as Hr32.
        unfold bv_half_modulus, bv_modulus in Hr32.
        change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z in Hr32.
        (* [a3num] is a SIGNED reading, so the bridge is [bv_sign_extend_signed]
           (widening preserves the signed value), not [sysc_sext_uint] -- that
           one is about [uint] and matches nothing here. *)
        (* [exact], not [lia]: the two [bv_signed]s carry the SAME width by
           conversion ([MachineWord.Z_idx (31 - 0 + 1)] vs [Z_idx 32]) but are
           distinct ATOMS to [lia], which then reports "Cannot find witness". *)
        rewrite bv_sign_extend_signed;
          [ exact Hr32 | apply N.leb_le; vm_compute; reflexivity ]. }
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.syscall + 0x22)) (mword_of_int 30 : mword 13) Ra5 Ra4
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate))
                              (rget_ne B5 Ra4 ltac:(vm_compute; discriminate))
                              HB5a5 HB4a5 HB5a4;
                      exact (sysc_bltu_taken a3num Hrange Ha3sig))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (syci_22 with "Htext"). }
      iNext.
      iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hp40 : add_vec (mword_of_int (KernelSyms.syscall + 0x22) : mword 64) (sign_extend' 64 (mword_of_int 30 : mword 13)) = mword_of_int (KernelSyms.syscall + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp40) in "Hpc".
      (* THE PRINTK FALLBACK.  Unlike a table arm it reads [p] out of s1, so
         the one extra premise below is [B5]'s s1 -- set at +0x10 and never
         written since. *)
      assert (HB5s1 : B5 !!! Regidx Rs1 = pj).
      { rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate].
        rewrite /B0 upd_eq add_vec_zero_l. exact HMFa0. }
      assert (HB5armsp : B5 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4)
        by (rewrite HB5sp; exact Hspd4).
      assert (HB5avb : (K_syscall <= av)%nat)
        by (lia).
      assert (HB5other : forall r : mword 5, is_cs_idx r = true ->
          r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
          B5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B5 upd_ne; [| congruence].
        rewrite /B4 upd_ne; [| congruence].
        rewrite /B3 upd_ne; [| congruence].
        rewrite /B2 upd_ne; [| congruence].
        rewrite /B1 upd_ne; [| congruence].
        rewrite /B0 upd_ne; [| congruence].
        rewrite (callee_saved_lookup HcsMF r Hr).
        rewrite /A2 upd_ne; [| congruence].
        rewrite /A1 upd_ne; [| congruence].
        rewrite /A0 upd_ne; [| congruence].
        reflexivity. }
      iEval (rewrite HcspA0 -Hb1) in "Hr24". iEval (rewrite HcspA0 -Hb2) in "Hr16".
      iEval (rewrite HcspA0 -Hb3) in "Hr8".  iEval (rewrite HcspA0 -Hb4) in "Hr0".
      (* the landing hart again -- see the note at [sysc_arm_dispatch]. *)
      assert (Hcr15 : true = false \/ pj = zero_reg -> (CID15 : CPU) = (CID : CPU))
        by wp_next_chain.
      (* the fallback RETURNS, so it wants the bare continuation *)
      iDestruct "Hcont" as "[Hcont _]".
      iDestruct (wp_next_retarget CID CID15 true pj _ Hcr15 with "Hcont") as "Hcont".
      assert (Hcr8_15 : true = false \/ pj = zero_reg -> (CID15 : CPU) = (CID8 : CPU))
        by wp_next_chain.
      iDestruct (cpu_own_transport CID8 CID15 0%nat true pj true Hcr8_15 with "Hcpu") as "Hcpu".
      iApply (sysc_fallback (CID := CID15) γf pj γs j bn fn dqi ip pid V lks av m B5
                Hj eq_refl HB5armsp HB5s1 HB5other HB5avb
                with "[Hpc Hcg Hcpu Htext Hprocs HR Hbs Hip Hfd Hir Hpriv Hufrag] Hr24 Hr16 Hr8 Hr0 Hdata Hcont").
      { iApply (sysc_arm_pre_intro with
          "Hpc Hcg Hcpu Htext Hprocs HR Hbs Hip Hfd Hir Hpriv Hufrag"). }
  Qed.

End SyscallMain.
End SyscallProof.
