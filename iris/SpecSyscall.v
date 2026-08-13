(* SpecSyscall.v -- the public interface of syscall() (syscall.c), stated
   ahead of its proof.  THIS CONTRACT IS ASSUMED: LinkSyscall.v supplies it
   with an [Axiom], the way LinkPrintkGen.v and LinkConsoleintr.v do for
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

   So it is ONE ABSTRACT PARAMETER, [syscall_env γf pj], exactly as
   [SpecUsertrap.v]'s original boundary statement abstracted its
   kernel-internal resources.  Consumers thread it opaquely; the eventual
   proof DEFINES it (as the union above, indexed by the ghost names the
   table's entries want) without churning a single caller.  What the
   contract does say concretely is the part usertrap actually depends on:

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
Require Import PanicStub.
Require Import SpecSysExit.   (* [K_sys_exit]: the deepest entry in the table *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* syscall's own frame is 4 slots; below it the deepest table entry, which is
   sys_exit at [K_sys_exit] = 4 + kexit's 74.  Written as an expression, not
   a literal, so a change to kexit's budget cannot silently leave this one
   behind -- the drift would be invisible until a caller's [av] premise
   failed somewhere far away. *)
Definition K_syscall : nat := (4 + K_sys_exit)%nat.

Definition wp_syscall_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (R : gname -> mword 64 -> iProp Σ)
    (γf : gname) (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.syscall in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_syscall <= av)%nat ->
  (* INTERRUPTS ON, at push_off level 0 -- see the header: the [csrsi] that
     precedes the only call site, and what the parking entries need. *)
  sie_cap_gpr m av true pj -∗
  cpu_own 0%nat true pj C true -∗
  (* [kernel_data] is the jump table itself ([syscalls] lives in .rodata) and
     argraw's below it; [procs_inv]/[panic_wp_any] are the proc array and the
     panic arms every acquire/release in the cone reaches. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  (* everything the twenty-two entries consume, abstractly -- see header *)
  R γf pj -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (V' : pprivate),
      ⌜ callee_saved m mf ⌝ -∗
      (* THE TRAPFRAME PAGE IS THE ONE THING THAT CANNOT MOVE.  Everything
         else in the record may: [pv_tf] always does (the a0 slot is the
         return value), and sbrk / exec / chdir / open move the rest. *)
      ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
      sie_cap_gpr mf av true pj -∗
      cpu_own 0%nat true pj C true -∗
      R γf pj -∗
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
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
      `{GEN : GenId},
      gname -> mword 64 -> iProp Σ.
  Parameter wp_syscall_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (C : iProp Σ)
      (pid : mword 32) (V : pprivate),
      wp_syscall_sconf_body syscall_env γf γs j γl m av C pid V.
End SYSCALL.
