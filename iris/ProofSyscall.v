(* ProofSyscall.v -- the real proof of syscall(), replacing LinkSyscall.v's
   whole-function axiom.

   STATUS (read this before extending, and re-verify against the actual
   `Admitted`/`Qed` sites rather than trusting this note): the whole
   dispatch is `Qed`-sealed -- prologue, `myproc()`, the `p->trapframe->a7`
   read, the fused range check, the 22-entry jump-table read, the `c.jalr`,
   the shared return tail (`sysc_ret_tail`: the `sd a0,112(s2)` store into
   `p->trapframe->a0` and the jump into the epilogue), the epilogue
   (`sysc_epilogue_tail`: the four reloads, the frame pop, `c.ret`) AND the
   whole unknown-syscall printk fallback (`sysc_fallback`, +0x40..+0x56).
   NINE of the 22 table entries are REAL, `Qed`'d arms calling their own
   whole-function contracts:

     k =  1  sys_fork    (`sysc_arm_fork`)   -- the widest premise list of
                                                any wired entry, and every
                                                one of its seven persistent
                                                handles is in `syscall_env`;
                                                the only entry with no
                                                process indexing at all;
     k =  3  sys_wait    (`sysc_arm_wait`)   -- the process triple, plus
                                                `procs_inv`,
                                                `kalloc_env` and the
                                                "wait_lock" lock; it PARKS,
                                                and it moves `pv_upt`;
     k =  6  sys_kill    (`sysc_arm_kill`)   -- the first entry whose argint
                                                wants `p_trapframe ↦₈{dq}`
                                                and `tf_page` SEPARATELY:
                                                `ProcInv.proc_priv_tf` lends
                                                both and takes them back;
     k = 10  sys_dup     (`sysc_arm_dup`)    -- the ftable lock, and a post
                                                (`sys_dup_post`) whose three
                                                exits differ only in `V`;
     k = 11  sys_getpid  (`sysc_arm_getpid`) -- needs only `proc_priv`;
     k = 12  sys_sbrk    (`sysc_arm_sbrk`)   -- `proc_priv` + `kalloc_env`
                                                (out of `syscall_env`) plus
                                                its two trapframe argument
                                                words, whose EXISTENCE is all
                                                the contract asks for;
     k = 13  sys_pause   (`sysc_arm_pause`)  -- kill's trapframe borrow plus
                                                the tickslock; it SLEEPS on
                                                the tick counter, so it needs
                                                the process triple too;
     k = 14  sys_uptime  (`sysc_arm_uptime`) -- the tickslock and nothing
                                                else (no `proc_priv` at all);
     k = 18  sys_unlink  -- NOT WIRED.  Its arm was written against a
                                                SpecSysUnlink.v whose contract
                                                was `wp_syscall_sconf_body`
                                                with the entry point changed
                                                (`syscall_env` as an abstract
                                                `R`); that placeholder has
                                                since been replaced by a REAL
                                                contract of a different shape,
                                                and the two disagree.  Index 18
                                                falls through to the
                                                placeholder until the shape is
                                                settled cross-line.

   The file's ONE remaining `Admitted` is `sysc_arm_placeholder`, standing
   in for the other thirteen table entries (reached through
   `sysc_arm_dispatch`, which is where a new arm is wired: one
   `decide (k = <literal>)` branch, nothing already wired moves).

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

   WHAT BLOCKS THE REST -- measured against the actual `SpecSysXxx.v`
   premise lists, not against this file's older EASY/GAP catalogue below,
   which counted only resources and missed the pure premises entirely.
   Three obstacles, in increasing order of what they cost:

   (1) A PREMISE ABOUT UNCHECKED USER INPUT, which no dispatcher can ever
       supply.  `sys_read` takes `0 <= sys_rw_count v2` and
       `MAXFILE*BSIZE + sys_rw_count v2 < 2^31` about the count word the
       USER wrote (SpecSysRead.v's header says so outright: "neither
       premise can be discharged here"), and `sys_write` carries the lower
       bound too.  Widening `syscall_env` would not touch this: the debt is
       readi's/writei's overflow arm, settled in file.c's own specs or not
       at all.  So read/write are blocked for a STRONGER reason than the
       missing fs-fabric record everyone notices first.
   (2) A CONSUMED-AND-NOT-RETURNED environment.  `sys_fstat` has no
       unsatisfiable pure premise -- everything it asks for except
       `filestat_fs_env fn` (`fn : fstat_names`) is already here -- but its
       post returns only `filestat_fs_out fn`, which is strictly weaker, so
       `syscall_env` could not be handed back verbatim.  It IS reachable:
       `filestat_fs_env` splits into a persistent half and exactly
       `filestat_fs_out` (the `sb_inodestart` fraction and one `bslot`), so
       a `filestat_fs_env fn ⊣⊢ <persistent> ∗ filestat_fs_out fn` pair in
       SpecFilestat.v would let an arm reassemble.  The cost is that
       `syscall_env` stops being FULLY PERSISTENT -- which every arm here
       relies on (see the `#`-copy note below) -- so it is a shape decision,
       not a proof detail, and it buys exactly one entry.
   (3) Genuinely missing resources: `log_ctx` and
       `trap_csrs_ext`/`cpu_claim_ext` (sys_sync, which syscall does not
       thread at all), and, for the eight GAP entries, the whole fs fabric
       (`bio_ctx`, `fs_crash_seam`, `dev_inv`, `disk_geom`, the four
       superblock cells, `bitmap_res`, `ic_escrows`, `ireg_inv`) plus
       `fd_slot`/`iref_slots ns` allowances -- sys_open's contract
       (SpecSysOpen.v), though PROVEN, is the extreme case.

   `sys_exit` (k = 2) stays outside `sysc_arm_goal` regardless of any of
   this: its contract DIVERGES (bare `WP Loop`, no continuation), so it
   needs a bespoke branch -- and the divergence is the EASY half.  What
   actually blocks it, measured against `SpecSysExit.wp_sys_exit_sconf_body`:

     - Its `fn = MkFCloseNames γs j γl γkl γka γu γd γk pd pav pu bn γ γfs
       cov logstart dev pid (DfracOwn (1/4)) γi cn γtl bmapstart inodestart
       nib size dqb dqs` premise forces SIX ties between the ambient
       dispatch parameters and `fn`'s own fields: `fcn_procs fn = γs`,
       `fcn_j fn = j`, `fcn_plock fn = γl`, `fcn_bio fn = bn`,
       `fcn_pid fn = pid`, `fcn_dq fn = DfracOwn (1/4)`.  Only the last two
       of those six mention things `syscall_env γf pj bn fn` is INDEXED BY
       (`bn`, `fn`); `γs`, `j`, `γl` and `pid` are not indices of it, so the
       ties cannot be stated inside its body at all -- widening the body is
       not enough, `syscall_env`'s TYPE (SpecSyscall.v's `Parameter`, and
       with it `wp_syscall_sconf_body`'s `R` and `UsertrapRes.ut_own`'s
       `Rsys` slot) would have to grow a `pid` index at minimum.  (`j` alone
       IS recoverable, from `pj = proc_addr (fcn_j fn)` plus
       `ProcGeom.proc_addr_inj`; `γs`/`γl`/`pid` are not.)
     - Even granting the ties, NINE resource families it wants are absent:
       the kmem lock and `kalloc_avail` AT `fn`'s OWN `fcn_kmem`/`fcn_kalloc`
       (`syscall_env`'s `kalloc_env γa None` existentially quantifies its
       own, so the two can never be shown equal -- the unreachable-witness
       problem SpecSyscall.v's header names), `bio_ctx`, `log_ctx`,
       `fs_crash_seam`, `gen_cert`, `dev_inv` at `fn`'s `fcn_uart`/`fcn_disk`
       (again `printk_env`'s are existential), `disk_geom`, the virtio_disk
       lock, and `fileclose_ic_env fn` (whose `ic_escrows`/`ireg_inv`/
       `ic_sleeplocks` and nine pure geometry facts nothing here carries),
       plus the pure `log_geom_ok cov logstart`.
     Its BUDGET premise, by contrast, is exactly dischargeable:
     `K_syscall = 4 + K_sys_exit` and an arm runs at `av - 4`.  So sys_exit
     is a `syscall_env`-shape decision, not a proof detail -- the same one
     the eight GAP entries wait on, and the reason it is grouped with them
     rather than with the nine wired arms.

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
     mutable pieces do (`ut_own_rebuild_us` is the pattern for THOSE, not
     for this) -- derive a `#`-copy once and every arm (and the printk
     fallback) can peel out whichever pieces it needs while the original
     hypothesis stays available, unchanged, to hand back verbatim as `R γf
     pj bn fn` in the continuation.
   - The precondition catalogue below is the ORIGINAL, resource-only
     reading, and wiring the first arms showed it is optimistic: it counts
     only what `syscall_env` must SUPPLY and misses the PURE premises
     (`locks_below`, and sys_uptime's `tp = cid_word`) that turn out to
     block most of "EASY".  Read the STATUS block at the top of this file
     first; what follows is kept for the resource half, which is accurate.
     EASY (14) -- fork, wait, read, kill, fstat, dup, getpid,
     sbrk, pause, uptime, write, sync, open (axiom), unlink (axiom).  GAP
     (8, matching `SpecSyscall.v`'s own header exactly) -- exit, pipe,
     exec, chdir, mknod, link, mkdir, close.  `read`/`fstat`/`write` take
     their OWN `fread_names`/`fstat_names`/`fwrite_names` record (not
     `fclose_names`), so they carry no `fn`-tie at all.  `sys_close` is GAP
     despite taking `fn : fclose_names` opaquely (no `MkFCloseNames`
     premise, unlike sys_exit/kexit) -- it still needs `fileclose_fs_env`
     resources tied to a REAL `fn`, which `syscall_env`'s fresh existential
     cannot supply.
   - Syscall ARGUMENTS never cross this file's own concern: every `sys_xxx`
     is niladic in C and reads its own arguments out of `proc_priv`'s
     trapframe page via its own internal `argint`/`argraw`/... calls
     (`ProcGeom.tf_arg_idx`), so `syscall()`'s dispatch does no argument
     marshaling at the `c.jalr` site -- the live register file handed to
     the callee is unconstrained on entry, exactly as `wp_cjalr_s_sconf`'s
     own statement allows.
   - Budget (`av`): `K_syscall = 4 + K_sys_exit` is syscall's OWN 4-slot
     frame plus the deepest callee's own bound; myproc()'s call (BEFORE the
     dispatch) needs `(av-4) >= 10` (mirrors ProofSysGetpid.v/ProofArgraw.v
     verbatim), which `K_sys_exit`'s own depth trivially covers.  After
     myproc returns, `av` is back at the caller's own remaining `(av-4)`
     for the rest of the function, including the dispatch call -- each
     `SysXxx`'s own `K_sys_xxx <= K_sys_exit` bound (that inequality is
     what "the deepest table entry" in `K_syscall`'s own comment asserts)
     is what makes every arm's own `av` premise dischargeable from
     `Hav : K_syscall <= av` by `lia` once the two nats are unfolded.

   sys_open is PROVEN (SpecSysOpen.v / ProofSysOpen.v / LinkSysOpen.v), so
   index 15 would take the real [SYSOPEN] like any other arm -- what it is
   waiting on is obstacle (3) above, not a missing proof.  sys_unlink is the
   one table entry whose WALK is still being built: [SpecSysUnlink.v] is now
   the REAL contract (the placeholder that mirrored [wp_syscall_sconf_body]
   is gone), index 18 is wired to it, and LinkSysUnlink.v supplies it with
   an [Axiom] until [ProofSysUnlink.v] lands -- see
   claude-notes/projects/fs-sysfile.md, "S7-unlink". *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
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
Require Import InodeRegion.
Require Import IcacheEscrow IcacheInv.
Require Import IrefSlots FdSlots.
Require Import FileInvDefs FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import BioDefs.
Require Import SpecFileclose.
Require Import ProcAvail.
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
Require Import SpecSyscall.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ======================================================================= *)
(* THE p->name NUL-TERMINATION GAP.  [ProcInv.proc_priv]'s [pname_cells]
   hands back sixteen raw bytes with no NUL-termination fact -- nothing in
   the tree proves [allocproc]/[kfork]/[kexec] leave one -- so, exactly as
   [SpecProcdump.proc_dump_slot] does (`nonul nm` there, same gap), the
   fallback's printk("%s", p->name) call needs it as a small, HONEST, local
   assumption rather than a derivation from nothing.  Scoped to the actual
   sixteen bytes a caller holds (not a blanket claim over all byte lists),
   discharged as its own tiny axiom in LinkSyscall.v, parallel to the two
   syscall-entry axioms. *)
Module Type PROCNAME_OK.
  Parameter procname_ok :
    forall (bs : list (bv 8)), length bs = PNAMELEN ->
      exists nm : string, PrintkFmt.nonul nm = true /\
        exists pad : list (bv 8), bs = List.app (cstring_bytes nm) pad.
End PROCNAME_OK.

Module SyscallProof
    (SysFork : SYSFORK) (SysExit : SYSEXIT) (SysWait : SYSWAIT)
    (SysPipe : SYSPIPE) (SysRead : SYSREAD) (SysKill : SYSKILL)
    (SysExec : SYSEXEC) (SysFstat : SYSFSTAT) (SysChdir : SYSCHDIR)
    (SysDup : SYSDUP) (SysGetpid : SYSGETPID) (SysSbrk : SYSSBRK)
    (SysPause : SYSPAUSE) (SysUptime : SYSUPTIME) (SysWrite : SYSWRITE)
    (SysMknod : SYSMKNOD) (SysLink : SYSLINK) (SysMkdir : SYSMKDIR)
    (SysClose : SYSCLOSE) (SysSync : SYS_SYNC)
    (SysOpen : SYSOPEN) (SysUnlink : SYSUNLINK)
    (Myproc : MYPROC) (Printk : PRINTK_GEN) (PName : PROCNAME_OK) : SYSCALL.

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

Section SyscallVocab.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* ===================================================================== *)
  (* syscall_env -- the union of everything the FOURTEEN wired entries need
     that is NOT one of the five explicit families (bslots/fileclose_bm/
     initproc/fd_slots/iref_slots).  Every conjunct is Persistent (is_lock,
     kalloc_env at [None], procs_avail at [None], printk_env), so the whole
     bundle is held with [#] and never needs reassembly across a call --
     none of the fourteen entries write anything inside it. *)
  (* explicit (redundant-with-Section) binder list: [syscall_env]'s BODY
     does not need [bioG]/[logG]/[fsCrashG] (none of the fourteen wired
     entries touch bio/log/crash resources), so Section discharge would
     otherwise narrow its inferred signature below what the [SYSCALL]
     Module Type's [syscall_env] Parameter fixes -- pin the full fifteen
     explicitly so the two signatures match exactly at [End]. *)
  (* [bn]/[fn] are UNUSED by this body for now: the fourteen entries wired
     below all take their icache/fs-fabric ghost names (cov/logstart/nib/...)
     as free-standing parameters rather than bundled inside an opaque
     [fclose_names], so a fresh existential here is exactly as good as one
     tied to the ambient [fn] -- see SpecSyscall.v's header on why the two
     extra indices exist at all.  The eight GENUINE SPEC GAP entries (still
     [Admitted] below) are exactly the ones where that stops being true:
     closing them means replacing some of this body's fresh existentials
     with direct references to [fn]'s own fields (via [FCloseNames]'s
     accessors) plus a premise tying the ambient [fn]/[bn] to them, not
     changing this Definition's TYPE again. *)
  Definition syscall_env
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId}
      (γf : gname) (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      : iProp Σ :=
    (∃ (γa γp γw γft γtk γil γpr : gname) (cn : ic_names) (γics : fs_names)
       (γic : gname) (cov : gset Z) (logstart : Z) (nib : nat)
       (γud : uart_names) (γvd : disk_names),
       kalloc_env γa None ∗
       is_lock γp alp_pid_lock "nextpid"%string nextpid_res ∗
       procs_avail None ∗
       is_lock γw wait_lock_addr "wait_lock"%string wait_res ∗
       is_ftable γft γf ∗
       is_itable2 γil cn γics γic cov logstart nib icfg_dev ∗
       itable_inv ∗
       is_tickslock γtk ∗
       printk_env γpr γud γvd)%I.

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
    pose proof (sysc_tbl_bytes k Hk) as Hb.
    iIntros "#Hd". rewrite /word_pointsto. iSplit.
    { iPureIntro. destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]]]]]]]]]]];
        try lia; vm_compute; reflexivity. }
    iApply (kernel_data_window (KernelSyms.syscalls + 8 * Z.of_nat k)
              (mword_of_int (sysc_target k) : mword 64) 8%nat _ eq_refl Hle Hb with "Hd").
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
      (tgt : mword 64) (us : gset Z) :=
    (pc_is tgt ∗
     sie_cap_gpr kt M av true pj ∗
     cpu_own 0%nat true pj true lks ∗
     kernel_text ∗
     (* the proc array and the panic arms every [acquire]/[release] in the
        cone reaches -- both persistent, both already held by the capstone,
        and between them what most table entries need beyond [proc_priv] *)
     procs_inv (kt := kt) γs ∗
     syscall_env γf pj bn fn ∗
     bslots bn 3 ∗
     fileclose_bm fn us ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv γf pj pid V)%I.

  (* the OUTER [wp_syscall_sconf_body]'s own continuation, named so every
     arm/the epilogue can take it as an explicit parameter rather than
     restate it -- [V]/[m] here are the WHOLE FUNCTION's entry values,
     fixed for the whole proof; only [mf]/[V']/[us'] vary per return. *)
  Definition sysc_hcont_ty `{CIDh : CpuId} (γf : gname) (pj : mword 64) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (m : regfile)
      (ret_tgt : mword 64) : iProp Σ :=
    wp_next true pj (fun (CID : CpuId) =>
      (∀ (mf : regfile) (V' : pprivate) (us' : gset Z),
        ⌜ callee_saved m mf ⌝ -∗
        ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
        sie_cap_gpr kt mf av true pj -∗
        cpu_own 0%nat true pj true lks -∗
        bslots bn 3 -∗
        fileclose_bm fn us' -∗
        (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
        fd_slots FDSPARE -∗
        iref_slots IREFSPARE -∗
        syscall_env γf pj bn fn -∗
        proc_priv γf pj pid V' -∗
        pc_is ret_tgt -∗
        WP (Loop : expr riscv_lang))%I).

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
     SpecSysExit.v), so it does not fit this shape; it stays [Admitted]
     with the rest of the GAP entries, at a bespoke type. *)
  Definition sysc_arm_goal `{CIDh : CpuId} (k : nat) (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) (us : gset Z) : Prop :=
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
    sysc_arm_pre γf pj γs bn fn dqi ip pid V lks (av - 4)%nat M (mword_of_int (sysc_target k)) us -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    kernel_data -∗
    sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
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
      (lks : gset string) (av : nat) (us' : gset Z)
      (m E : regfile) :
    E !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       E !!! Regidx r = m !!! Regidx r) ->
    (4 <= av)%nat ->
    ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ->
    sie_cap_gpr kt E (av - 4)%nat true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    bslots bn 3 -∗ fileclose_bm fn us' -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
    syscall_env γf pj bn fn -∗ proc_priv γf pj pid V' -∗
    pc_is (mword_of_int (KernelSyms.syscall + 0x58) : mword 64) -∗
    sysc_hcont_ty γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HEsp Hrest Hav4 Hud.
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hcpu #Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir HR Hpriv Hpc Hcont".
    assert (Hb1 : pa_stk sp0 1 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 1 3); lia).
    assert (Hb2 : pa_stk sp0 2 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 2 2); lia).
    assert (Hb3 : pa_stk sp0 3 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 3 1); lia).
    assert (Hb4 : pa_stk sp0 4 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (apply (sysc_stk sp0 4 0); lia).
    (* +0x58: c.ldsp ra,24(sp) *)
    iPoseProof (syci_58 with "Htext") as "Hi58".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x58)) (mword_of_int 3 : mword 6) Rra
              E (av - 4)%nat (m !!! Regidx Rra) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [Hra]").
    { iEval (rewrite HEsp -Hb1). iExact "Hra". }
    iIntros (CID1 Hst1) "Hcg Hpc Hra".
    set (T1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E) with T1.
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [rewrite HEsp; reflexivity | vm_compute; discriminate]).
    (* +0x5a: c.ldsp s0,16(sp) *)
    iPoseProof (syci_5a with "Htext") as "Hi5a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5a)) (mword_of_int 2 : mword 6) Rs0
              T1 (av - 4)%nat (m !!! Regidx Rs0) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a [Hs0]").
    { iEval (rewrite HT1sp -Hb2). iExact "Hs0". }
    iIntros (CID2 Hst2) "Hcg Hpc Hs0".
    set (T2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1) with T2.
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.syscall + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* +0x5c: c.ldsp s1,8(sp) *)
    iPoseProof (syci_5c with "Htext") as "Hi5c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5c)) (mword_of_int 1 : mword 6) Rs1
              T2 (av - 4)%nat (m !!! Regidx Rs1) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c [Hs1]").
    { iEval (rewrite HT2sp -Hb3). iExact "Hs1". }
    iIntros (CID3 Hst3) "Hcg Hpc Hs1".
    set (T3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2).
    change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2) with T3.
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    (* +0x5e: c.ldsp s2,0(sp) *)
    iPoseProof (syci_5e with "Htext") as "Hi5e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x5e)) (mword_of_int 0 : mword 6) Rs2
              T3 (av - 4)%nat (m !!! Regidx Rs2) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e [Hs2]").
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
    iPoseProof (syci_60 with "Htext") as "Hi60".
    iEval (rewrite HEsp -Hb1) in "Hra". iEval (rewrite HT1sp -Hb2) in "Hs0".
    iEval (rewrite HT2sp -Hb3) in "Hs1". iEval (rewrite HT3sp -Hb4) in "Hs2".
    iAssert (stack_own (KTR := kt) sp0 4) with "[Hra Hs0 Hs1 Hs2]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hra". { iExists _. iExact "Hra". }
      iSplitL "Hs0". { iExists _. iExact "Hs0". }
      iSplitL "Hs1". { iExists _. iExact "Hs1". }
      iSplitL "Hs2". { iExists _. iExact "Hs2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.syscall + 0x60)) (mword_of_int 2 : mword 6) T4
              (av - 4)%nat 4 true Hpop
              with "Hcg Hpc Hi60 Hframe4").
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
    iPoseProof (syci_62 with "Htext") as "Hi62".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.syscall + 0x62)) Rra T5 av true
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi62").
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
    iApply ("Hcont" $! T5 V' us' with "[%] [%] Hcg Hcpu Hbs Hfc Hip Hfd Hir HR Hpriv Hpc").
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
    exact Hud.
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
              ltac:(unfold text_end, sysc_fmt_a; lia) sysc_fmt_bytes with "Hd").
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

  (* the sixteen raw bytes, SPLIT at the NUL [PROCNAME_OK] promises is there:
     a real C string in front, whatever gcc left behind it. *)
  Lemma sysc_pname_app (pa : mword 64) (dq : dfrac) (nm : string) (pad : list (bv 8)) :
    pname_cells pa dq (List.app (cstring_bytes nm) pad) ⊣⊢
    (p_name pa 0 ↦ₛ{dq} nm ∗
     [∗ list] i ↦ b ∈ pad, p_name pa (length (cstring_bytes nm) + i) ↦ₘ{dq} b).
  Proof.
    rewrite /pname_cells big_sepL_app /string_pointsto.
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Lemma sysc_ret_tail
      (γf : gname) (pj : mword 64) (bn : bio_names) (fn : fclose_names)
      (dqi : dfrac) (ip : mword 64) (pid : mword 32) (V V' : pprivate)
      (lks : gset string) (av : nat) (us' : gset Z)
      (m E : regfile) :
    E !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    E !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V')) ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       E !!! Regidx r = m !!! Regidx r) ->
    (4 <= av)%nat ->
    ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ->
    sie_cap_gpr kt E (av - 4)%nat true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    bslots bn 3 -∗ fileclose_bm fn us' -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
    syscall_env γf pj bn fn -∗ proc_priv γf pj pid V' -∗
    pc_is (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64) -∗
    sysc_hcont_ty (kt := kt) γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HEsp HEs2 Hrest Hav4 Hud.
    iIntros "Hcg Hcpu #Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir HR Hpriv Hpc Hcont".
    set (tfp := ud_tfp (pv_upt V')).
    (* the trapframe page, opened for WRITING out of [proc_priv] *)
    iDestruct (sysc_tfp_valid with "Hpriv") as "%Hpv".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
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
    iPoseProof (syci_3a with "Htext") as "Hi3a".
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.syscall + 0x3a)) Ra0 Rs2
              (mword_of_int 112 : mword 12) E (av - 4)%nat w0 true
              with "Hcg Hpc Hi3a Hcell").
    iIntros (CIDa Hsa) "Hcg Hpc Hcell".
    iEval (rewrite HEs2r (sysc_tf_addr_112 tfp)) in "Hcell".
    iDestruct ("Hcback" $! (rget E Ra0) with "Hcell") as "Htfp".
    iDestruct ("Hpvback" $! (<[tf_arg_idx 0 := rget E Ra0]> (pv_tf V'))
                 with "Htfc Htfp") as "Hpriv".
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x3a) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x3e)) by pcw.
    iEval (rewrite Hp3e) in "Hpc".
    (* ---- +0x3e: c.j +0x1a -- over the fallback block, into the epilogue ---- *)
    iPoseProof (syci_3e with "Htext") as "Hi3e".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.syscall + 0x3e))
              (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
              E (av - 4)%nat true ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e").
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
              lks av us' m E HEsp Hrest Hav4 Hud
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir HR Hpriv Hpc Hcont").
  Qed.

End SyscallRet.

(* ===================================================================== *)
(* S3 -- THE DISPATCH ARMS, one per table entry, plus the combinator the
   capstone applies.  An arm calls its entry's own whole-function contract
   and hands the result to S2's [sysc_ret_tail]; since the callee's post is
   delivered at a REBOUND hart, the tail has to come from an earlier
   section. *)
Section SyscallArms.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* PLACEHOLDER for a not-yet-specialized table entry: an honest
     [Admitted] stand-in so the dispatch machinery below can be assembled
     and validated end-to-end before every arm is filled in.  Real arms
     are wired in one at a time by branching on [decide (k = <literal>)]
     ahead of this generic fallback -- see [wp_syscall_sconf]'s own use;
     each such branch shrinks what this placeholder is still standing in
     for, without touching the branches already replaced. *)
  Lemma sysc_arm_placeholder (k : nat) (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) (us : gset Z) :
    (1 <= k <= 22)%nat ->
    sysc_arm_goal (kt := kt) k γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Admitted.

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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 11 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    (* the table entry's address IS [sys_getpid]'s entry pc *)
    assert (Hpce : (mword_of_int (sysc_target 11) : mword 64)
                   = mword_of_int KernelSyms.sys_getpid) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    (* ---- the call ---- *)
    iApply (SysGetpid.wp_sys_getpid_sconf kt γf M (av - 4)%nat 0%nat true pj pid V true lks
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
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V lks av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 12 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
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
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(#Hkalloc & _)".
    (* ---- the call ---- *)
    iApply (SysSbrk.wp_sys_sbrk_sconf kt γa γf M (av - 4)%nat true pj pid V v0 v1 true lks
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
      cbn [pv_upt upd_sz upd_upt]. rewrite Htfp'. exact HMs2. }
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
              (upd_sz (upd_upt V P') szv') lks av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 3 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
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
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(#Hkalloc & _ & _ & #Hwaitlk & _)".
    (* ---- the call ---- *)
    iApply (SysWait.wp_sys_wait_sconf kt γa γf γw γs j γl M (av - 4)%nat true true lks pid V v0
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
      cbn [pv_upt upd_upt]. rewrite Htfp'. exact HMs2. }
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
              (upd_upt V P') lks av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 14 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    assert (Hpce : (mword_of_int (sysc_target 14) : mword 64)
                   = mword_of_int KernelSyms.sys_uptime) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(_ & _ & _ & _ & _ & _ & _ & #Hticks & _)".
    (* ---- the call ---- *)
    iApply (SysUptime.wp_sys_uptime_sconf kt γtk M 0%nat true pj (av - 4)%nat true ∅
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
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 6 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
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
    iApply (SysKill.wp_sys_kill_sconf kt γs M (av - 4)%nat 0%nat true pj
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
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 13 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
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
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(_ & _ & _ & _ & _ & _ & _ & #Hticks & _)".
    (* ---- the call ---- *)
    iApply (SysPause.wp_sys_pause_sconf kt γs j γl γtk M (av - 4)%nat true 0%nat
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
    iApply (sysc_ret_tail (CID := CIDy) γf (proc_addr j) bn fn dqi ip pid V V ∅ av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
  Qed.

  (* [sys_dup]'s three-way post, collapsed to what the shared tail needs: SOME
     private block, with the trapframe page unmoved.  Only the success arm
     moves [V] at all, and [upd_ofile] rewrites the fd array alone -- the
     descriptor [pv_upt] (hence [ud_tfp]) is the same record field. *)
  Lemma sysc_dup_priv (γf : gname) (p : mword 64) (pid : mword 32)
      (V : pprivate) (v r : mword 64) :
    sys_dup_post γf p pid V v r -∗
    ∃ V' : pprivate, ⌜ud_tfp (pv_upt V') = ud_tfp (pv_upt V)⌝ ∗ proc_priv γf p pid V'.
  Proof.
    rewrite /sys_dup_post.
    iIntros "[[_ Hp] | [Hb | Hc]]".
    - iExists V. iSplitR; [iPureIntro; reflexivity | iExact "Hp"].
    - iDestruct "Hb" as (fd0 fv) "[_ Hp]".
      iExists V. iSplitR; [iPureIntro; reflexivity | iExact "Hp"].
    - iDestruct "Hc" as (fd0 fd1 fv l) "[_ Hp]".
      iExists (upd_ofile V fd1 fv). iSplitR; [iPureIntro; reflexivity | iExact "Hp"].
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 10 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
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
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(_ & _ & _ & _ & #Hftable & _)".
    (* ---- the call ---- *)
    iApply (SysDup.wp_sys_dup_sconf kt γft γf M (av - 4)%nat 0%nat true pj v0 pid V true ∅
              Hv0 sysc_noff0 ltac:(lia) (locks_below_empty "ftable")
              with "Hcg Hcpu Htext Hdata Hpc Hftable Hpriv").
    iIntros (CIDy Hsy mf) "%Hcs Hcg Hcpu Hpc Hpost".
    iDestruct (sysc_dup_priv with "Hpost") as (V') "[%Htfp' Hpriv]".
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
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V' ∅ av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) Htfp'
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
      (m M : regfile) (us : gset Z) :
    sysc_arm_goal (kt := kt) 1 γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    rewrite /sysc_arm_goal /sysc_arm_pre.
    intros Hj Hgamma Hpj HMsp HMs2 HMra HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    assert (Hpce : (mword_of_int (sysc_target 1) : mword 64)
                   = mword_of_int KernelSyms.sys_fork) by reflexivity.
    iEval (rewrite Hpce) in "Hpc".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(#Hkalloc & #Hnextpid & #Hpav & #Hwaitlk & #Hftable & #Hitable & #Hitinv & _)".
    (* ---- the call ---- *)
    iApply (SysFork.wp_sys_fork_sconf kt γa γp γw γft γf γil γic γs cn γics cov logstart nib
              M 0%nat (av - 4)%nat true pj true pid V ∅
              ltac:(lia) sysc_noff0b
              (locks_below_empty "wait_lock")
              with "Hcg Hcpu Htext Hpc Hprocs Hnextpid Hwaitlk Hftable Hitable Hitinv Hkalloc Hpav Hpriv").
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
    iApply (sysc_ret_tail (CID := CIDy) γf pj bn fn dqi ip pid V V ∅ av us m mf
              Hmfsp Hmfs2 Hmfrest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
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
     falls through to [sysc_arm_placeholder] until that is settled --
     see claude-notes/projects/fs-sysfile.md, "S7-unlink". *)

  (* THE COMBINATOR.  One [decide (k = <literal>)] branch per wired entry,
     ahead of the generic placeholder: adding an arm is adding a branch, and
     nothing already wired moves.  Kept in THIS section (rather than beside
     the capstone) because the capstone applies it AFTER the [c.jalr]'s own
     hart crossing. *)
  Lemma sysc_arm_dispatch (k : nat) (γf : gname) (pj : mword 64)
      (γs : list gname) (j : nat) (γl : gname) (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) (us : gset Z) :
    (1 <= k <= 22)%nat ->
    sysc_arm_goal (kt := kt) k γf pj γs j γl bn fn dqi ip pid V lks av m M us.
  Proof.
    intro Hk.
    destruct (decide (k = 1%nat)) as [-> | _].
    { exact (sysc_arm_fork γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 3%nat)) as [-> | _].
    { exact (sysc_arm_wait γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 6%nat)) as [-> | _].
    { exact (sysc_arm_kill γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 10%nat)) as [-> | _].
    { exact (sysc_arm_dup γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 11%nat)) as [-> | _].
    { exact (sysc_arm_getpid γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 12%nat)) as [-> | _].
    { exact (sysc_arm_sbrk γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 13%nat)) as [-> | _].
    { exact (sysc_arm_pause γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    destruct (decide (k = 14%nat)) as [-> | _].
    { exact (sysc_arm_uptime γf pj γs j γl bn fn dqi ip pid V lks av m M us). }
    (* index 18 (sys_unlink) is NOT wired: both lines made SpecSysUnlink real
       in incompatible shapes, so it falls through to the placeholder pending
       the cross-line shape decision.  See the header note. *)
    exact (sysc_arm_placeholder k γf pj γs j γl bn fn dqi ip pid V lks av m M us Hk).
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
     [ProcInv.proc_priv]'s [pname_cells] hands back sixteen raw bytes with no
     NUL in them -- [PName]'s [procname_ok] is where that gap is paid, and
     [sysc_pname_app] is what turns the bytes it splits into the
     [string_pointsto] printk's [PkAStr] wants.

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
      (m M : regfile) (us : gset Z) :
    (j < NPROC)%nat ->
    pj = proc_addr j ->
    M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    M !!! Regidx Rs1 = pj ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
       M !!! Regidx r = m !!! Regidx r) ->
    (K_syscall <= av)%nat ->
    sysc_arm_pre (kt := kt) γf pj γs bn fn dqi ip pid V lks (av - 4)%nat M
      (mword_of_int (KernelSyms.syscall + 0x40) : mword 64) us -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := kt) (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    kernel_data -∗
    sysc_hcont_ty (kt := kt) γf pj bn fn dqi ip pid V lks av m (ret_pc (m !!! Regidx Rra)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hj Hpj HMsp HMs1 HMother Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    subst pj.
    iIntros "(Hpc & Hcg & Hcpu & #Htext & #Hprocs & #Henv & Hbs & Hfc & Hip & Hfd & Hir & Hpriv)".
    iIntros "Hra Hs0 Hs1 Hs2 #Hdata Hcont".
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]". subst lks.
    iPoseProof "Henv" as "#Henvc".
    iDestruct "Henvc" as (γa γp γw γft γtk γil γpr cn γics γic cov logstart nib γud γvd)
      "(_ & _ & _ & _ & _ & _ & _ & _ & #Hpenv)".
    (* ---- +0x40: addi a2,s1,344 -- a2 := &p->name ---- *)
    iPoseProof (syci_40 with "Htext") as "Hi40".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x40)) Ra2 Rs1
              (mword_of_int 344 : mword 12) M (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40").
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
    iPoseProof (syci_44 with "Htext") as "Hi44".
    assert (Ha44 : add_vec (rget F0 Rs1) (sign_extend' 64 (mword_of_int 48 : mword 12))
                   = p_pid (proc_addr j)).
    { rgne. rewrite HF0s1. reflexivity. }
    iApply (wp_clw_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x44)) Ra1 Rs1
              (mword_of_int 48 : mword 12) F0 (av - 4)%nat pid true
              (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hpidc]").
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
    iPoseProof (syci_46 with "Htext") as "Hi46".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.syscall + 0x46)) Ra0
              (mword_of_int 5 : mword 20) F1 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46").
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
    iPoseProof (syci_4a with "Htext") as "Hi4a".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x4a)) Ra0 Ra0
              (mword_of_int 2766 : mword 12) F2 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a").
    iIntros (CIDd Hsd) "Hcg Hpc".
    set (F3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (rget F2 Ra0) (sign_extend' 64 (mword_of_int 2766 : mword 12)))]> F2).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (rget F2 Ra0) (sign_extend' 64 (mword_of_int 2766 : mword 12)))]> F2) with F3.
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x4a) : mword 64) 4
                   = mword_of_int (KernelSyms.syscall + 0x4e)) by pcw.
    iEval (rewrite Hp4e) in "Hpc".
    assert (HF3a0 : F3 !!! Regidx Ra0 = (mword_of_int sysc_fmt_a : mword 64)).
    { rewrite /F3 upd_eq. rgne. rewrite /F2 upd_eq.
      unfold sysc_fmt_a. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0x4e: jal ra,printk ---- *)
    iPoseProof (syci_4e with "Htext") as "Hi4e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.syscall + 0x4e)) Rra
              (mword_of_int 2087992 : mword 21) F3 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4e").
    iIntros (CIDe Hse) "Hcg Hpc".
    set (F4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64) 4)]> F3).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64) 4)]> F3) with F4.
    assert (Hjpk : add_vec (mword_of_int (KernelSyms.syscall + 0x4e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087992 : mword 21))
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
    (* ---- p->name as a C STRING: [PROCNAME_OK] is where the NUL comes from ---- *)
    iDestruct (sysc_priv_name with "Hpriv") as "(%Hnlen & Hnm & Hnmback)".
    destruct (PName.procname_ok (pv_name V) Hnlen) as (nm & Hnonul & pad & Hsplit).
    iEval (rewrite Hsplit) in "Hnm".
    iDestruct (sysc_pname_app (proc_addr j) (DfracOwn 1) nm pad with "Hnm") as "[Hstr Hpad]".
    iPoseProof (sysc_fmt_str with "Hdata") as "Hfmt".
    iDestruct (cpu_own_transport CID CIDe 0%nat true (proc_addr j) true
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Printk.wp_printk_gen_sconf kt (CID := CIDe) γpr γud γvd F4 (av - 4)%nat true
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
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iPoseProof (pt_node_claim_from_static tfp Hpv with "Hkmapb") as "#Hptc".
    iDestruct (proc_priv_tf_upd with "Hpriv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_length with "Htfp") as "%Htflen".
    assert (Hi14 : (tf_arg_idx 0 < length (pv_tf V))%nat)
      by (rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia).
    destruct (lookup_lt_is_Some_2 (pv_tf V) (tf_arg_idx 0) Hi14) as [w0 Hw0].
    iDestruct (tf_page_word_upd_mem tfp (pv_tf V) (tf_arg_idx 0) w0
                 ltac:(vm_compute; lia) Hw0 with "Hptc Htfp") as "(Hcell & Hcback)".
    (* ---- +0x52: c.ld a5,88(s1) -- a5 := p->trapframe ---- *)
    iPoseProof (syci_52 with "Htext") as "Hi52".
    assert (Ha52 : add_vec (rget mf Rs1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                   = p_trapframe (proc_addr j)).
    { rgne. rewrite Hmfs1. reflexivity. }
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x52)) Ra5 Rs1
              (mword_of_int 88 : mword 12) mf (av - 4)%nat (page_base tfp) true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Htfc]").
    { iEval (rewrite Ha52). iExact "Htfc". }
    iIntros (CIDg Hsg) "Hcg Hpc Htfc". iEval (rewrite Ha52) in "Htfc".
    set (G0 := <[Regidx Ra5 := regval_into_reg (page_base tfp)]> mf).
    change (<[Regidx Ra5 := regval_into_reg (page_base tfp)]> mf) with G0.
    assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x52) : mword 64) 2
                   = mword_of_int (KernelSyms.syscall + 0x54)) by pcw.
    iEval (rewrite Hp54) in "Hpc".
    assert (HG0a5 : G0 !!! Regidx Ra5 = page_base tfp) by (rewrite /G0 upd_eq; reflexivity).
    (* ---- +0x54: c.li a4,-1 ---- *)
    iPoseProof (syci_54 with "Htext") as "Hi54".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.syscall + 0x54)) Ra4
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              G0 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi54").
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
    iPoseProof (syci_56 with "Htext") as "Hi56".
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.syscall + 0x56)) Ra4 Ra5
              (mword_of_int 112 : mword 12) G1 (av - 4)%nat w0 true
              with "Hcg Hpc Hi56 Hcell").
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
              ∅ av us m G1 HG1sp HG1rest ltac:(lia) eq_refl
              with "Hcg Hcpu Htext Hra Hs0 Hs1 Hs2 Hbs Hfc Hip Hfd Hir Henv Hpriv Hpc Hcont").
  Qed.

End SyscallArms.

(* ===================================================================== *)
(* S4 -- THE CAPSTONE. *)
Section SyscallMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* CAPSTONE.  The shared scaffolding (`sysc_arm_pre`/`sysc_hcont_ty`/
     `sysc_arm_goal`, the trapframe-extraction/bitvector-bridge lemmas, and
     `sysc_epilogue_tail`) is assembled here with the real PROLOGUE (frame
     push, the `myproc()` call, the two trapframe reads, the fused range
     check driving the data-dependent `k`, the address computation, the
     table read, the redundant `beqz`, the `c.jalr`) into a full dispatch:
     every one of the 22 table entries reaches `sysc_arm_goal k` for its
     own `k`, discharged by `sysc_arm_dispatch` -- nine real arms (see the
     file header's list) and, for the other thirteen, the honest `Admitted`
     `sysc_arm_placeholder`.  A new arm is one more `decide (k = <literal>)`
     branch inside that combinator and NOTHING here moves; see the file
     header for what each remaining entry is still waiting on. *)
  Lemma wp_syscall_sconf (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string)
    : wp_syscall_sconf_body kt syscall_env γf γs j γl bn fn us ip dqi m av pid V lks.
  Proof.
    cbv beta delta [wp_syscall_sconf_body].
    intros pcE pj ret_tgt Hj Hgamma Hav.
    assert (Hav82 : (82 <= av)%nat)
      by (lia).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hprocs Hbs Hfc Hip Hfd Hir HR Hpriv Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (syci_00 with "Htext") as "Hi00".
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
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
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
    iPoseProof (syci_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (av - 4)%nat vr24 true with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (syci_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (av - 4)%nat vr16 true with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (syci_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (av - 4)%nat vr8 true with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iPoseProof (syci_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.syscall + 0x08)) (mword_of_int 0 : mword 6) Rs2
              A0 (av - 4)%nat vr0 true with "Hcg Hpc Hi08 [Hr0]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr0". }
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.syscall + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a: c.addi4spn s0,sp,32 *)
    iPoseProof (syci_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.syscall + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              A0 (av - 4)%nat true
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
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
    iPoseProof (syci_0c with "Htext") as "Hi0c".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.syscall + 0x0c)) Rra (mword_of_int 2093138 : mword 21)
              A1 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)]> A1).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)]> A1) with A2.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2093138 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.syscall + 0x0c) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd)
      by (rewrite /A2 upd_ne; [exact HA1sp | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID CID7 0%nat true pj true ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    (* ---- myproc(): a0 := p, callee-saved preserved ---- *)
    iApply (Myproc.wp_myproc_sconf kt A2 (av - 4)%nat 0%nat true pj true lks
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
    iPoseProof (syci_10 with "Htext") as "Hi10".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.syscall + 0x10)) Rs1 Ra0 MF (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
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
    iPoseProof (syci_12 with "Htext") as "Hi12".
    assert (Ha12 : add_vec (B0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 88 : mword 12)) = p_trapframe pj).
    { rewrite HB0a0. reflexivity. }
    iApply (wp_ld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x12)) Rs2 Ra0 (mword_of_int 88 : mword 12)
              B0 (av - 4)%nat (page_base (ud_tfp (pv_upt V))) true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [Htfc]").
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
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iPoseProof (pt_node_claim_from_static (ud_tfp (pv_upt V)) Hpv with "Hkmapb") as "#Hptc".
    iDestruct (tf_page_word_mem (ud_tfp (pv_upt V)) (pv_tf V) 21%nat RAWNUM ltac:(lia) Htf21 with "Hptc Htfp") as "[Htfw Htfwback]".
    iPoseProof (syci_16 with "Htext") as "Hi16".
    assert (Ha16 : add_vec (B1 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 168 : mword 12)) = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat 21%nat)).
    { rewrite HB1s2 (tf_pa_eq_pa_add8 (ud_tfp (pv_upt V)) 21%nat ltac:(lia)).
      unfold pa_add, add_vec_int. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x16)) Ra5 Rs2 (mword_of_int 168 : mword 12)
              B1 (av - 4)%nat RAWNUM true
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Htfw]").
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
    iPoseProof (syci_1a with "Htext") as "Hi1a".
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.syscall + 0x1a)) Ra3 Ra5 (mword_of_int 0 : mword 12)
              B2 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
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
    iPoseProof (syci_1e with "Htext") as "Hi1e".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.syscall + 0x1e)) Ra5 (mword_of_int 63 : mword 6)
              B3 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
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
    iPoseProof (syci_20 with "Htext") as "Hi20".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.syscall + 0x20)) Ra4 (mword_of_int 21 : mword 6)
              (mword_of_int 21 : mword 64) B4 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi20").
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
      iPoseProof (syci_22 with "Htext") as "Hi22".
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.syscall + 0x22)) (mword_of_int 30 : mword 13) Ra5 Ra4
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate))
                              (rget_ne B5 Ra4 ltac:(vm_compute; discriminate))
                              HB5a5 HB4a5 HB5a4;
                      exact (sysc_bltu_fall a3num Hrange))
                with "Hcg Hpc Hi22").
      iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      pose (k := Z.to_nat (bv_signed a3num)).
      assert (Hk : (1 <= k <= 22)%nat) by (unfold k; lia).
      assert (Hzk : Z.of_nat k = bv_signed a3num) by (unfold k; lia).
      assert (Ha3k : a3num = mword_of_int (Z.of_nat k)) by (rewrite Hzk; exact (sysc_a3_val a3num Hrange)).
      (* ---- +0x26: slli a4,a3,3 ---- *)
      iPoseProof (syci_26 with "Htext") as "Hi26".
      iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.syscall + 0x26)) Ra4 Ra3 (mword_of_int 3 : mword 6)
                (shift_bits_left (B5 !!! Regidx Ra3) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hi26").
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
      iPoseProof (syci_2a with "Htext") as "Hi2a".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.syscall + 0x2a)) Ra5 (mword_of_int 5 : mword 20)
                C0 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (C1 := <[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> C0).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> C0) with C1.
      assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.syscall + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.syscall + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2e) in "Hpc".
      iPoseProof (syci_2e with "Htext") as "Hi2e".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.syscall + 0x2e)) Ra5 Ra5 (mword_of_int 3818 : mword 12)
                C1 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2e").
      iIntros (CID18 Hs18) "Hcg Hpc".
      (* [rget], NOT [!!!]: [wp_addi4_s_sconf]'s continuation spells the written
         value at the hart-indexed read, so a [set] written with [!!!] folds
         NOTHING and the [change] behind it silently no-ops -- see the note at
         [C3] below for what that costs. *)
      set (C2 := <[Regidx Ra5 := regval_into_reg
          (add_vec (rget C1 Ra5) (sign_extend' 64 (mword_of_int 3818 : mword 12)))]> C1).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (rget C1 Ra5) (sign_extend' 64 (mword_of_int 3818 : mword 12)))]> C1) with C2.
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
      iPoseProof (syci_32 with "Htext") as "Hi32".
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.syscall + 0x32)) Ra5 Ra4 C2 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32").
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
      iPoseProof (syci_34 with "Htext") as "Hi34".
      iPoseProof (sysc_table_word k Hk with "Hdata") as "#Hent".
      assert (Ha34 : add_vec (C3 !!! Regidx Ra5) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                     = mword_of_int (KernelSyms.syscalls + 8 * Z.of_nat k)).
      { rewrite HC3a5. apply kv_addv_zero. }
      iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.syscall + 0x34)) Ra5 Ra5
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) C3 (av - 4)%nat
                (mword_of_int (sysc_target k) : mword 64) true
                (dqm := DfracDiscarded)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 []").
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
      iPoseProof (syci_36 with "Htext") as "Hi36".
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.syscall + 0x36)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                C4 (av - 4)%nat true ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne C4 Ra5 ltac:(vm_compute; discriminate)) HC4a5;
                      apply eq_vec_false_iff; intro Hc; exact (sysc_target_nz k Hk Hc))
                with "Hcg Hpc Hi36").
      iIntros (CID21 Hs21) "Hcg Hpc".
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.syscall + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.syscall + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".
      (* ---- +0x38: c.jalr a5 -- THE INDIRECT CALL ---- *)
      iPoseProof (syci_38 with "Htext") as "Hi38".
      iApply (wp_cjalr_s_sconf (mword_of_int (KernelSyms.syscall + 0x38)) Ra5 Rra C4 (av - 4)%nat true
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38").
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
      iDestruct (wp_next_retarget CID CID22 true pj _ Hcr22 with "Hcont") as "Hcont".
      assert (Hcr8_22 : true = false \/ pj = zero_reg -> (CID22 : CPU) = (CID8 : CPU))
        by wp_next_chain.
      iDestruct (cpu_own_transport CID8 CID22 0%nat true pj true Hcr8_22 with "Hcpu") as "Hcpu".
      iApply (sysc_arm_dispatch (CID := CID22) k γf pj γs j γl bn fn dqi ip pid V lks av m D0 us Hk
                Hj Hgamma eq_refl HD0armsp HD0s2 HD0ra HD0other HD0avb
                with "[Hpc Hcg Hcpu Htext Hprocs HR Hbs Hfc Hip Hfd Hir Hpriv] Hr24 Hr16 Hr8 Hr0 Hdata Hcont").
      { rewrite /sysc_arm_pre.
        iFrame "Hpc Hcg Hcpu Htext Hprocs HR Hbs Hfc Hip Hfd Hir Hpriv". }
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
      iPoseProof (syci_22 with "Htext") as "Hi22".
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.syscall + 0x22)) (mword_of_int 30 : mword 13) Ra5 Ra4
                B5 (av - 4)%nat true
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate))
                              (rget_ne B5 Ra4 ltac:(vm_compute; discriminate))
                              HB5a5 HB4a5 HB5a4;
                      exact (sysc_bltu_taken a3num Hrange Ha3sig))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22"). iNext.
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
      (* the landing hart again -- see the note at [sysc_arm_placeholder]. *)
      assert (Hcr15 : true = false \/ pj = zero_reg -> (CID15 : CPU) = (CID : CPU))
        by wp_next_chain.
      iDestruct (wp_next_retarget CID CID15 true pj _ Hcr15 with "Hcont") as "Hcont".
      assert (Hcr8_15 : true = false \/ pj = zero_reg -> (CID15 : CPU) = (CID8 : CPU))
        by wp_next_chain.
      iDestruct (cpu_own_transport CID8 CID15 0%nat true pj true Hcr8_15 with "Hcpu") as "Hcpu".
      iApply (sysc_fallback (CID := CID15) γf pj γs j bn fn dqi ip pid V lks av m B5 us
                Hj eq_refl HB5armsp HB5s1 HB5other HB5avb
                with "[Hpc Hcg Hcpu Htext Hprocs HR Hbs Hfc Hip Hfd Hir Hpriv] Hr24 Hr16 Hr8 Hr0 Hdata Hcont").
      { rewrite /sysc_arm_pre.
        iFrame "Hpc Hcg Hcpu Htext Hprocs HR Hbs Hfc Hip Hfd Hir Hpriv". }
  Qed.

End SyscallMain.
End SyscallProof.
