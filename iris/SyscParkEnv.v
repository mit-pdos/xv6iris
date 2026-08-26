(* SyscParkEnv.v -- THE FOUR ROWS THE FILE SYSTEM DOES NOT CARRY.

   [ProofSyscall.syscall_env] is four conjuncts: [sysc_proc_env],
   [ConsoleInv.console_ready], [sysc_fs_env], and [FirstTok.first_done].
   Almost all of it is derivable from [FirstTok.first_done] alone --
   [first_done] is [first_addr ↦₄□ 0 ∗ FsReady.fs_ready], and [fs_ready] is
   the whole file system -- which is what makes the environment payable by a
   party that has none of it yet.  That party is the one that PARKS a fresh
   process (userinit for the first, kfork for the rest), and it matters that
   the payment be in this shape: at userinit's park the file system DOES NOT
   EXIST (forkret's boot arm establishes it, after userinit has parked), so
   nothing owned outright can stand in for it.  See SpecForkret.v's last
   header section.

   WHAT [first_done] DOES NOT REACH is exactly four rows, and this file names
   them so that the [SYSCALL] Module Type can state its producer without
   naming any of the twenty-two arms' vocabulary:

     the "nextpid" lock       allocpid's counter, main's to create
     [procs_avail None]       the slot ledger, procinit's
     [is_tickslock]           the ticks lock, main's
     [console_ready]          consoleinit's

   ALL FOUR ARE PERSISTENT AND ALL FOUR EXIST BEFORE EITHER PARKER RUNS --
   main creates every one of them before it calls userinit, and kfork's
   parent holds them inside the [syscall_env] it is running on.  So this
   bundle is the honest statement of what parking a process costs beyond the
   file system, and it is nothing a parker does not have.

   THE OTHER ROWS [sysc_proc_env] AND [sysc_fs_env] WANT are not here on
   purpose: the [wait_lock], [is_ftable], [procs_inv] and [disk_geom] are
   ALREADY conjuncts of [UsertrapRes.ut_park_caps], which the same parker
   pays for [ut_caps] in the same breath.  Duplicating them here would make
   a caller hold two copies of four persistent rows and prove the same thing
   twice; the producer takes them as separate arguments instead.

   THIS FILE HAS NO PROOFS.  It is a definition and its persistence
   instance, placed below [SpecSyscall.v] so the Module Type can name it,
   and above nothing at all. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.        (* [is_lock] *)
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import SpecAllocpid.  (* [alp_pid_lock] / [nextpid_res] *)
Require Import ProcAvail.     (* [procs_avail] *)
Require Import TicksInv.      (* [is_tickslock] *)
Require Import ConsoleInv.    (* [console_ready] *)
Require Import SchedCtx.      (* [procs_inv] *)
Require Import WpUart.        (* [dev_inv] *)
Require Import SpecConsoleintr.  (* [console_caps] *)
Require Import DiskInv.  (* [disk_geom] / [disk_res] / [d_lock] *)
Require Import Xv6Cameras.
Require Import WireInv.       (* [wire_inv] *)
Require Import KptExecMap. (* [kmap_at tramp_vpn tramp_ppn KP_rx] *)
Require Import FsCfg.         (* the ambient device names *)
Require Import FileInvDefs.   (* [fileG] -- which carries [fscfg] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section SyscParkEnv.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  (* the nextpid lock's gname is EXISTENTIAL, exactly as [sysc_proc_env]
     carries it: nothing outside allocpid ever names it, and a parker that
     had to thread it would be threading a name it cannot otherwise use. *)
  Definition sysc_park_extra (γtk : gname) : iProp Σ :=
    ((∃ γp : gname, is_lock γp alp_pid_lock "nextpid"%string <{ nextpid_res }>) ∗
     procs_avail None ∗
     is_tickslock γtk ∗
     console_ready)%I.

  Global Instance sysc_park_extra_persistent γtk :
    Persistent (sysc_park_extra γtk).
  Proof. rewrite /sysc_park_extra. apply _. Qed.

End SyscParkEnv.

Section ParkWorld.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.

  (* THE PARK'S WORLD, as a process hands it to its children.  A parent that
     forks builds the child's trap-loop environment, and the rows the child
     needs beyond the file system and beyond what [sysc_park_extra] /
     [syscall_env] already carry are: the device complement at the AMBIENT
     names ([UsertrapRes.devintr_caps_any]'s six members, spelled out here
     because this file sits below that one), the console, the PLIC wire
     invariant, the trampoline claim, and a persistent share of the
     [initproc] cell.  All persistent, all existing before any process
     runs; the ticks lock's gname and the ring pages are existential
     because a child's record may name them fresh.  Stated once so that
     one premise threads usertrap -> syscall -> sys_fork -> kfork. *)
  Definition park_world (γs : list gname) : iProp Σ :=
    (∃ (γtl : gname) (pd pav pu : mword 64),
       dev_inv fsc_uart fsc_disk ∗
       console_caps fsc_uart ∗
       disk_geom fsc_disk pd pav pu ∗
       is_lock fsc_dlock d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) fsc_disk pd pav pu) ∗
       is_tickslock γtl ∗
       procs_inv γs ∗
       console_ready ∗
       (* [sysc_park_extra]'s other two rows, so that this bundle covers all
          of it: the nextpid lock and the sealed slot ledger *)
       (∃ γp : gname, is_lock γp alp_pid_lock "nextpid"%string <{ nextpid_res }>) ∗
       procs_avail None ∗
       wire_inv ∗
       kmap_at tramp_vpn tramp_ppn KP_rx ∗
       (∃ ip : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈□ ip))%I.

  Global Instance park_world_persistent γs : Persistent (park_world γs).
  Proof. rewrite /park_world. apply _. Qed.

End ParkWorld.
