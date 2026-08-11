(* SpecSysExit.v -- the public interface of sys_exit(), stated independently
   of its proof.

     uint64 sys_exit(void) {
       int n;
       argint(0, &n);
       kexit(n);
       return 0;  // not reached
     }

   @ KernelSyms.sys_exit = 0x800028d6, eighteen instructions / 36 bytes: a
   32-byte ra/s0 frame whose slot 3 holds [int n] at s0-20 = sp+12 -- the
   UPPER half of one slot, sys_kill's [int pid] shape -- then argint(0,&n),
   [lw a0,-20(s0)] and a call to kexit.  gcc does not know kexit is
   noreturn, so it still emits the dead [li a0,0] / epilogue / ret tail:

     +0x00  1101        c.addi     sp,sp,-32
     +0x02  ec06        c.sdsp     ra,24(sp)
     +0x04  e822        c.sdsp     s0,16(sp)
     +0x06  1000        c.addi4spn s0,sp,32
     +0x08  fec40593    addi       a1,s0,-20      a1 := &n
     +0x0c  4501        c.li       a0,0
     +0x0e  f2fff0ef    jal        ra,argint
     +0x12  fec42503    lw         a0,-20(s0)     a0 := n
     +0x16  f30ff0ef    jal        ra,kexit
     +0x1a  4501        c.li       a0,0            DEAD: kexit never returns
     +0x1c  60e2        c.ldsp     ra,24(sp)
     +0x1e  6442        c.ldsp     s0,16(sp)
     +0x20  6105        c.addi16sp sp,32
     +0x22  8082        c.ret

   IT DIVERGES.  Like SpecKexit.v, the postcondition is [WP Loop], full
   stop: nothing after the [jal kexit] is reachable, and the contract says
   so structurally (no continuation) rather than by convention.  The dead
   tail gcc emitted at +0x1a..+0x22 is decoded by nobody's proof -- kexit's
   own contract discharges the whole rest of the function by never handing
   control back.

   THE CONTRACT IS THE UNION OF ITS TWO CALLEES', and kexit dominates it.
   The [status] argument does not even need naming: kexit's own contract
   takes no [status] parameter, because nothing downstream of [p->xstate]
   is observable from inside its diverging body (see SpecKexit.v -- the
   ZOMBIE park's [proc_dormant] carries no promise about it either).  So
   the only thing sys_exit's proof needs from argint is that it MAY be
   called, i.e. that argument 0 exists in the trapframe -- and, exactly as
   in SpecSysWait.v, that is a fact about [proc_priv]'s own trapframe
   record ([pv_tf V !! tf_arg_idx 0 = Some v0]).  The trapframe fraction
   argint wants is borrowed OUT of [proc_priv] ([ProcInv.proc_priv_tf]) for
   the duration of the call and put back before kexit -- which wants the
   whole block -- is entered. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KallocInv.
Require Import IcacheRef IcacheInv IcacheEscrow IrefSlots InodeRegion.
Require Import SpecFileclose.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecPanic.
Require Import SpecProcinit.   (* [wait_lock_addr] *)
Require Import SpecKexit.      (* [K_kexit] -- the budget this one is built on *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* 4 slots for sys_exit's own frame, and below it kexit's 74 -- argint's 18
   (4 + 18 = 22) is smaller and subsumed. *)
Definition K_sys_exit : nat := (4 + K_kexit)%nat.

Definition wp_sys_exit_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !kallocG Σ,
      !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γft γf γw : gname)                               (* ftable lock, ftable, wait *)
     (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (dqi : dfrac)                     (* the initproc cell   *)
    (γkl : gname) (γka : gname * gname)               (* kmem.lock, kalloc   *)
    (γi : gname) (cn : ic_names) (γtl : gname)        (* the inode cache     *)
    (bmapstart inodestart : Z) (nib : nat) (size : Z)
    (dqb dqs : dfrac) (us : gset Z)
    (on : option nat) (fn : fclose_names)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
    (pid : mword 32) (V : pprivate) (v0 : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_exit in
  let pj := proc_addr j in
  fn = MkFCloseNames γs j γl γkl γka γu γd γk pd pav pu bn γ γfs
         cov logstart dev pid (DfracOwn (1/4))
         γi cn γtl bmapstart inodestart nib size dqb dqs ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the syscall argument, out of the trapframe page [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  (K_sys_exit <= av)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* the PARKING premise, inherited from kexit: everything that sleeps or
     parks needs it *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* entered with no lock held *)
  cpu_own 0%nat eb pj C b -∗
  (* [kernel_data] is argint/argraw's own premise (the jump table it reads
     lives there); kexit needs none of it *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the proc table, and the scheduler chain the park hands itself to *)
  procs_inv γs -∗
  panic_wp_any -∗
  (* the running-thread bundle -- consumed: this thread parks forever *)
  (* wait_lock, and what it protects *)
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  (* the open-file table: every non-null descriptor is fileclose'd *)
  is_ftable γft γf -∗
  (* ...and closing one can free a pipe's page *)
  is_lock γkl (mword_of_int KernelSyms.kmem) "kmem"%string
    (kmem_res γka (mword_of_int (KernelSyms.kmem + 24))) -∗
  kalloc_avail γka on -∗
  (* the file system, for [begin_op(); iput(p->cwd); end_op();] inside kexit *)
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 3 -∗
  (* the inode cache and the two regions iput's truncate arm frees into,
     kexit's verbatim *)
  fileclose_ic_env fn -∗
  fileclose_bm fn us -∗
  (* the initproc pointer, at any fraction *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  (* the process itself: its private block (trapframe included) and its
     fd-slot allowance *)
  fd_slots FDSPARE -∗
  (* ... and its iref allowance, which kexit rejoins with the cwd unit iput
     hands back to build the ZOMBIE block *)
  iref_slots IREFSPARE -∗
  proc_priv γf pj pid V -∗
  (* NO continuation: sys_exit does not return.  See the header. *)
  WP (Loop : expr riscv_lang).

Module Type SYSEXIT.
  Parameter wp_sys_exit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γft γf γw : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (γi : gname) (cn : ic_names) (γtl : gname)
      (bmapstart inodestart : Z) (nib : nat) (size : Z)
      (dqb dqs : dfrac) (us : gset Z)
      (on : option nat) (fn : fclose_names)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) (v0 : mword 64),
      wp_sys_exit_sconf_body γft γf γw γs j γl γu γd γk pd pav pu bn γ γfs
                             cov logstart dev ip dqi γkl γka
                             γi cn γtl bmapstart inodestart nib size dqb dqs us
                             on fn m av eb C b pid V v0.
End SYSEXIT.
