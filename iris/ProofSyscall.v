(* ProofSyscall.v -- the real proof of syscall(), replacing LinkSyscall.v's
   whole-function axiom.

   STATUS (read this before extending, and re-verify against the actual
   `Admitted`/`Qed` sites -- this note is corrected once already, see git
   blame, because the previous wording overstated progress): `wp_syscall_sconf`
   itself is STILL `Admitted` -- the prologue (frame push, `myproc()` call,
   the two trapframe reads, the fused range check, the address computation,
   the table read, the `c.jalr`) and the actual per-table-entry dispatch
   are NOT YET ASSEMBLED, and NONE of the 22 table entries are wired.  What
   IS real and Qed-sealed, as of this commit: `syscall_env` (the resource
   bundle); the table-word lemmas (`sysc_target`/`sysc_tbl_bytes`/
   `sysc_table_word`/`sysc_target_nz`); the fused-bltu range-check lemmas
   (`sysc_bltu_fall`/`sysc_bltu_taken`); the bitvector bridge from the RAW
   a7 load to the C `int num` truncation the range check needs
   (`sysc_wrap32_add_indep`/`sysc_a3_bltu_bridge`/`sysc_a3_val`); the
   table-address computation lemma (`sysc_addr_word`); the trapframe
   page-validity reader (`sysc_tfp_valid`); the stack-slot arithmetic
   helper (`sysc_stk`); the dispatch-arm VOCABULARY (`sysc_arm_pre`,
   `sysc_hcont_ty`, `sysc_arm_goal` -- the TYPE every one of the 22 arms
   will need to prove, correctly threading the budget's `av-4` convention
   and the fact that `syscall()` reuses s0/s1/s2 as LOCALS rather than
   preserving them from its own entry `m`); and, the single largest real
   piece, `sysc_epilogue_tail` -- the FULL, Qed'd proof of +0x58 through
   +0x62 (the four reloads, the frame pop, `c.ret`), reused by every
   future returning arm and by the printk fallback.  A `sysc_a3_signed_bound`
   helper (bounding a3's signed value for `sysc_bltu_taken`'s out-of-range
   arm) was attempted and pulled back out after its `bv_swrap_small`
   side-condition rewrite would not fire -- see the note at its old
   location, just above `sysc_addr_word`, for the state it was left in.
   NEXT STEP for whoever continues: inline the prologue directly into
   `wp_syscall_sconf` (mirror `ProofArgraw.wp_argraw_sconf`'s own prologue,
   register-for-register, per this file's own inline notes below), derive
   `num`/`tfp` via `ProcInv.proc_priv_tf_upd` + `ProcInv.tf_page_word_mem`
   (NOT `wp_argraw_sconf_body`'s explicit-parameter shape -- syscall's own
   contract does not parametrize over the trapframe, so it has to be
   opened from `proc_priv` inline), finish `sysc_a3_signed_bound`, then
   `destruct (decide (1<=bv_signed a3num<=22))` and land at
   `sysc_hcont_ty`/`sysc_arm_goal`-shaped ADMITTED per-arm placeholders
   (`sysc_arm_placeholder`, symbolic in `k`) for a first fully-assembled
   (if not yet arm-proven) capstone, before replacing individual arms with
   real `SysXxx.wp_sys_xxx_sconf` calls.

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
   - The precondition catalogue (which of the 22 `SpecSysXxx.v` contracts
     are satisfiable straight from `syscall_env` + the five explicit
     families + `proc_priv`, vs which need a fact tied to the SAME `bn`/
     `fn` this file's `fn`-indexing was added to reach) is, as of this
     writing: EASY (14) -- fork, wait, read, kill, fstat, dup, getpid,
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

   See claude-notes/projects/fs-sysfile.md for what's independently still
   owed upstream (sys_open/sys_unlink themselves have no real proof at all
   yet, only the axiom-backed stand-ins SpecSysOpen.v/SpecSysUnlink.v). *)
From Stdlib Require Import ZArith Lia List.
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
Require Import PanicStub.
Require Import BioInv.
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
Require Import SpecSysOpenStub SpecSysUnlink.
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

Section ProofSyscall.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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

  Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.
  Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  (* the recurring "raw sp-relative address = pa_stk sp k" bridge *)
  Ltac stkeq := unfold pa_stk, add_vec_int; f_equal; apply bv_eq; vm_compute; reflexivity.

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
  Definition sysc_arm_pre (γf : gname) (pj : mword 64) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (M : regfile)
      (tgt : mword 64) (us : gset Z) :=
    (pc_is tgt ∗
     sie_cap_gpr M av true pj ∗
     cpu_own 0%nat true pj true lks ∗
     kernel_text ∗
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
  Definition sysc_hcont_ty (γf : gname) (pj : mword 64) (bn : bio_names)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (V : pprivate) (lks : gset string) (av : nat) (m : regfile)
      (ret_tgt : mword 64) : iProp Σ :=
    wp_next true pj (fun (CID : CpuId) =>
      (∀ (mf : regfile) (V' : pprivate) (us' : gset Z),
        ⌜ callee_saved m mf ⌝ -∗
        ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
        sie_cap_gpr mf av true pj -∗
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
  Definition sysc_arm_goal (k : nat) (γf : gname) (pj : mword 64)
      (bn : bio_names) (fn : fclose_names) (dqi : dfrac) (ip : mword 64)
      (pid : mword 32) (V : pprivate) (lks : gset string) (av : nat)
      (m M : regfile) (us : gset Z) : Prop :=
    M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4 ->
    M !!! Regidx Rs2 = page_base (ud_tfp (pv_upt V)) ->
    (K_syscall <= av)%nat ->
    sysc_arm_pre γf pj bn fn dqi ip pid V lks (av - 4)%nat M (mword_of_int (sysc_target k)) us -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
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
    sie_cap_gpr E (av - 4)%nat true pj -∗
    cpu_own 0%nat true pj true lks -∗
    kernel_text -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (pa_stk (m !!! Regidx csp_rs1) 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
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
    iAssert (stack_own sp0 4) with "[Hra Hs0 Hs1 Hs2]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
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

  (* CAPSTONE -- still `Admitted` (see file header STATUS): the shared
     scaffolding above it (`sysc_arm_pre`/`sysc_hcont_ty`/`sysc_arm_goal`,
     the trapframe-extraction/bitvector-bridge lemmas, and
     `sysc_epilogue_tail`, which is fully Qed'd) is real, but the actual
     PROLOGUE assembly -- the frame push, the `myproc()` call, the two
     trapframe reads, the fused range check driving a data-dependent
     `k`, the address computation, the table read, the redundant `beqz`,
     the `c.jalr`, and specializing each of the 22 table entries against
     `sysc_arm_goal` -- was not completed this session; see the header
     for exactly what is real vs. what remains. *)
  Lemma wp_syscall_sconf (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string)
    : wp_syscall_sconf_body syscall_env γf γs j γl bn fn us ip dqi m av pid V lks.
  Proof. Admitted.

End ProofSyscall.
End SyscallProof.
