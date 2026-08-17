(* SpecSyscall.v -- the public interface of syscall() (syscall.c), stated
   ahead of its proof.  THIS CONTRACT IS ASSUMED: LinkSyscall.v supplies it
   with an [Axiom], the way LinkPrintk.v and LinkConsoleintr.v do for
   their functions.  It exists so usertrap can be proved against a stated
   interface rather than against nothing.

     void syscall(void) {
       struct proc *p = myproc();
       int num = p->trapframe->a7;
       if (num > 0 && num < NELEM(syscalls) && syscalls[num]) {
         p->trapframe->a0 = syscalls[num]();
       } else {
         printk("%d %s: unknown sys call %d\n", p->pid, p->name, num);
         p->trapframe->a0 = -1;
       }
     }

   @ KernelSyms.syscall = 0x80002872, 100 bytes / 33 instructions, a 32-byte
   ra/s0/s1/s2 frame.

   WHAT MAKES THIS ONE HARD TO STATE HONESTLY, and how the statement below
   handles it: syscall is an INDIRECT CALL through [syscalls[]], so its
   footprint is the UNION of all twenty-two sys_* functions' -- the file
   table, the buffer cache, the log, the inode cache, kalloc, the wait lock,
   the initproc cell, the fd and iref allowances.  Spelling that union out
   here would be to restate SpecSysExit.v's thirty parameters and then some,
   and every one of them would have to be threaded verbatim through
   usertrap's own contract for no gain: usertrap does not touch any of it,
   it only hands it over.

   MOST of that union is therefore still ONE ABSTRACT PARAMETER,
   [syscall_env γf pj], exactly as [SpecUsertrap.v]'s original boundary
   statement abstracted its kernel-internal resources: consumers thread it
   opaquely, and [ProofSyscall.v] defines it (as the union of whatever is
   NOT listed below, indexed by the ghost names the table's entries want)
   without churning usertrap's own proof.

   FIVE FAMILIES ARE PULLED OUT AS EXPLICIT PARAMETERS INSTEAD, and this is
   not an inconsistency with the paragraph above -- it is forced by a
   SHARING constraint [syscall_env] cannot express on its own.
   [UsertrapRes.ut_own] already threads [bslots]/[fileclose_bm]/the
   [initproc] cell/[fd_slots]/[iref_slots] to fund usertrap's OWN direct
   [kexit] calls on the killed-before/killed-after arms (both of which run
   OUTSIDE this call, never through [syscall_env]).  [SpecSysExit.v]'s own
   contract needs exactly the same five families for the SAME physical
   pool, reached only when the dispatch table selects [SYS_exit] -- so if
   [syscall_env] carried an independent copy of any of them, [ut_res]'s
   existential would be asking for TWO disjoint fundings of one pool, which
   no boot-time construction could discharge (durable-notes.md's "two
   owners of one address space" trap, in ghost-resource form: `own γ (◯ n)
   ∗ own γ (◯ n)` is not [False], but it silently doubles the authority a
   real allocation would have to supply).  So these five ride through
   [syscall()] itself on the SAME channel [ut_own] already uses for them,
   in and out, exactly like [proc_priv] -- not through [syscall_env].
   Everything else in the union genuinely has no competing outer copy
   ([UsertrapRes.v] never mentions the icache/inode-region invariants, the
   superblock cells, or [bitmap_res] at all), so it stays inside the
   still-abstract [syscall_env] -- but [syscall_env] is ALSO INDEXED BY
   [bn]/[fn], not just [γf]/[pj], for a second reason discovered writing
   [ProofSyscall.v]: eight entries (exit, pipe, close, chdir, mknod, link,
   mkdir, exec) need filesystem-fabric facts -- [bio_ctx], the kmem/itable
   locks, the icache invariants -- keyed to the SAME [bn]/[fn] the five
   explicit families above already carry.  Without the extra indices,
   [syscall_env]'s own internal existential witnesses for those facts could
   never be shown equal to the AMBIENT [bn]/[fn] a caller already fixed --
   not a competing-owner problem this time, but an unreachable-witness one,
   and the fix is the same shape: widen the index rather than smuggle the
   fact through an unrelated channel. [UsertrapRes.ut_own]'s own [Rsys]
   slot widened to match (`Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)`),
   which every one of its ~25 mentions in that file threads opaquely --
   NOTHING in [ProofUsertrapSys.v]'s call site needed to change, since it
   never applies [Rsys]/[syscall_env] itself, only names the resource
   `Rsys ...` produces.

   What the contract does say concretely is the part usertrap actually depends on:

     - the process block goes in and comes back, at a MOVED record [V'] --
       every syscall may write [p->trapframe->a0] (the return value), and
       sbrk/exec/chdir/open move [pv_sz] / [pv_upt] / [pv_cwd] / [pv_ofile]
       besides.  The one thing pinned is [ud_tfp]: the trapframe PAGE never
       changes (even exec, which builds a whole new table, maps the existing
       [p->trapframe]), and prepare_return's stores land there;
     - callee-saved registers are preserved and the pc returns to ra;
     - the crossing is REAL ([wp_next]): sys_wait / sys_pause / sys_read
       park, so syscall can return on a different hart.

   THE INDEX IS PINNED AT [true], AND UNLIKE prepare_return'S THAT IS NOT A
   GAP.  syscall has exactly one call site -- usertrap's [jal syscall] --
   and the instruction immediately before it is [csrsi sstatus,2], xv6's
   [intr_on()].  The sys_* cone below needs it: everything that sleeps
   ([SpecSleep]) or parks ([SpecKexit]) demands [eb = true], and at push_off
   level 0 the base-enable and the live index coincide
   ([CpuOwn.cpu_own_eb_agree]).  So the pinned index states a property of the
   only reachable configuration, rather than excluding one.                 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcInv.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import BioInv.        (* [bio_names], for [bslots] *)
Require Import SpecFileclose. (* [fclose_names], [fileclose_bm] -- the five
                                  shared families, see the header *)
(* The classes the widened binder list now generalizes over
   ([kallocG]/[bioG]/[diskGhostG]/[uartGhostG]/[fsLogG]/[logG]/[fsCrashG]/
   [iregG]) -- [Require Import SpecFileclose]/[SpecSysExit] does not put
   them in scope transitively, and backtick generalization then silently
   invents fresh binders with those names (durable-notes.md's typeclass-sweep
   trap: the tell is [UNDEFINED EVARS]/"unresolved implicit arguments"
   naming exactly these). *)
Require Import KallocInv.
Require Import DiskPtsto.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
Require Import SpecSysExit.
Require Import SpecSysExec.   (* [K_sys_exec]: the deepest entry in the table *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

(* syscall's own frame is 4 slots; below it the deepest table entry, which is
   sys_exit at [K_sys_exit] = 4 + kexit's 74.  Written as an expression, not
   a literal, so a change to kexit's budget cannot silently leave this one
   behind -- the drift would be invisible until a caller's [av] premise
   failed somewhere far away. *)
Notation K_syscall := ((4 + K_sys_exec)%nat) (only parsing).
Definition wp_syscall_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (R : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
    (γf : gname) (γs : list gname) (j : nat) (γl : gname)
    (bn : bio_names) (fn : fclose_names) (us : gset Z)
    (ip : mword 64) (dqi : dfrac)
    (m : regfile) (av : nat)
    (pid : mword 32) (V : pprivate) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.syscall in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_syscall <= av)%nat ->
  (* INTERRUPTS ON, at push_off level 0 -- see the header: the [csrsi] that
     precedes the only call site, and what the parking entries need. *)
  sie_cap_gpr kt m av true pj -∗
  cpu_own 0%nat true pj true lks -∗
  (* [kernel_data] is the jump table itself ([syscalls] lives in .rodata) and
     argraw's below it; [procs_inv] is the proc array and the
     panic arms every acquire/release in the cone reaches. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  procs_inv (kt := kt) γs -∗
  (* THE FIVE FAMILIES [ut_own] ALSO holds -- see the header for why they
     ride here rather than inside [R].  [sys_exit] (reached through the
     table) is the only entry that draws on them; the other twenty-one
     simply frame them across their own call. *)
  bslots bn 3 -∗
  fileclose_bm fn us -∗
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  fd_slots FDSPARE -∗
  iref_slots IREFSPARE -∗
  (* everything else the twenty-two entries consume, abstractly -- header.
     Indexed by [bn]/[fn] too, not just [γf]/[pj]: eight of the entries need
     filesystem-fabric facts (bio_ctx, the kmem/itable locks, icache
     invariants) keyed to the SAME [bn]/[fn] the five explicit families
     above already carry, and an [R] that could not reference them would
     have no way to prove its own internal witnesses equal the ambient
     ones -- the "two owners" trap in reverse: not a competing copy, but an
     UNREACHABLE one. *)
  R γf pj bn fn -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (V' : pprivate) (us' : gset Z),
      ⌜ callee_saved m mf ⌝ -∗
      (* THE TRAPFRAME PAGE IS THE ONE THING THAT CANNOT MOVE.  Everything
         else in the record may: [pv_tf] always does (the a0 slot is the
         return value), and sbrk / exec / chdir / open move the rest. *)
      ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
      sie_cap_gpr kt mf av true pj -∗
      cpu_own 0%nat true pj true lks -∗
      bslots bn 3 -∗
      (* [us] may shrink -- [SYSCLOSE]'s own postcondition re-indexes it the
         same way ([fileclose_fs_env]'s [∃ us', ...]), and this call is the
         one place that arm's [us'] has to be threaded back out to. *)
      fileclose_bm fn us' -∗
      (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      R γf pj bn fn -∗
      proc_priv γf pj pid V' -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSCALL.
  (* the kernel-side resources the syscall table's entries consume, for the
     process at [pj] whose open-file table is named by [γf].  Defined
     concretely by the (future) proof; threaded opaquely by usertrap.

     HART-FREE, AND THAT IS PART OF THE CONTRACT rather than an accident of
     the binder list.  The environment is FRAMED across steps that run at
     [b = true] -- syscall's own tail after a parking table entry returns, and
     usertrap's whole tail on this arm ([jal killed], [jal prepare_return]) --
     and at that index a step may resume on a DIFFERENT hart.  A hart-indexed
     resource cannot cross: [IntrDefs.trap_csrs_ext_transport] and its
     siblings work only because their propositions are [emp] at [true], and
     nothing of that kind is available for an abstract family.  So the union
     of the twenty-two entries' footprints has to be hart-free, which it is:
     locks, invariants, ghost fragments and memory points-to, no per-hart
     register cell and no [tick_hart].  (Compare [SpecDevintr.devintr_caps],
     which genuinely is per-hart -- [TimerCap.timer_cap] holds this hart's
     mcounteren/stimecmp -- and which usertrap therefore carries in the
     hart-generic [UsertrapRes.devintr_caps_any] form instead.) *)
  Parameter syscall_env :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId}(kt : ktier) {kt : ktier} ,
      gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ.
  Parameter wp_syscall_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_syscall_sconf_body kt syscall_env γf γs j γl bn fn us ip dqi m av pid V lks.
End SYSCALL.
