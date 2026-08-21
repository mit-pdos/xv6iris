(* LinkSyscall.v -- syscall()'s contract, LINKED rather than assumed.

   syscall() is an indirect call through [syscalls[]], so proving it means
   proving the dispatch AND all twenty-two sys_* entries.  Until all
   twenty-two were wired, this file supplied [SpecSyscall.SYSCALL] with an
   [Axiom] the way [LinkPrintk.v] does for printk's general path.  It no
   longer does: [ProofSyscall.SyscallProof] is instantiated below against the
   twenty-two entry links, and what is left assumed here is ONE small,
   local fact about [p->name].

   WHY THE ENVIRONMENT DOES NOT BLOCK THIS, and it is the reason the swap is
   a file rewrite rather than a project: [syscall_env] is a PRECONDITION OF
   THE WP, not a module-level dependency.  The functor needs the twenty-two
   entry PROOFS; it does not need anyone to have produced the resources those
   proofs consume.  Establishing the environment is the boot chain's job and
   is still owed -- but it is owed to whoever finally APPLIES usertrap's
   theorem, and nothing about linking waits on it.  (Before, [syscall_env]
   was [emp] here and the obligation did not exist at all; now it is the real
   bundle and the obligation is real, sitting where it belongs.)

   NOTHING IS ASSUMED HERE ANY MORE.  An earlier draft of this file kept one
   small axiom, [PROCNAME_OK.procname_ok] -- that the sixteen bytes of
   [p->name] contain a NUL, so the fallback's [printk("%s", p->name)] has a C
   string to print.  It turned out the tree already PROVED that at every
   write site and threw it away: safestrcpy NUL-terminates
   ([SpecSafestrcpy.ssc_post]), freeproc stores a zero, and the array boots
   zero.  [ProcDefs.pname_cells] now carries [ProcGeom.pname_wf] and
   [CstringInv.bytes_string_split] turns it into the C-string shape, so the
   module type is gone and so is its axiom. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import ProofSyscall.
(* the twenty-two table entries, each already linked against its own callees *)
Require Import LinkSysFork LinkSysExit LinkSysWait LinkSysPipe LinkSysRead
                LinkSysKill LinkSysExec LinkSysFstat LinkSysChdir LinkSysDup
                LinkSysGetpid LinkSysSbrk LinkSysPause LinkSysUptime
                LinkSysWrite LinkSysMknod LinkSysLink LinkSysMkdir
                LinkSysClose LinkSysSync LinkSysOpen LinkSysUnlink.
(* ...and the three the dispatch itself needs: myproc, printk's general path
   for the unknown-number fallback, and the [p->name] fact below. *)
Require Import LinkMyproc LinkPrintk.

Module Syscall :=
  SyscallProof SysFork SysExit SysWait SysPipe SysRead SysKill
               SysExec SysFstat SysChdir SysDup SysGetpid SysSbrk
               SysPause SysUptime SysWrite SysMknod SysLink SysMkdir
               SysClose SysSync SysOpen SysUnlink
               Myproc PrintkGen.
