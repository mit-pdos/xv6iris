(* SyscParkEnv.v -- THE FOUR ROWS THE FILE SYSTEM DOES NOT CARRY.

   [ProofSyscall.syscall_env] is four conjuncts: [sysc_proc_env],
   [SpecFileread.console_ready_app], [sysc_fs_env], and [FirstTok.first_done].
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
     [console_ready_app]      consoleinit's

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
Require Import PidLock.  (* [alp_pid_lock] / [nextpid_res] *)
Require Import ProcAvail.     (* [procs_avail] *)
Require Import TicksInv.      (* [is_tickslock] *)
Require Import ConsoleInv.    (* the console ring's invariant *)
Require Import SchedCtx.      (* [procs_inv] *)
Require Import WpUart.        (* [dev_inv] / [uart_inv] / [plic_inv] *)
Require Import SpecConsoleintr.  (* [console_caps] *)
Require Import DiskInv.  (* [disk_geom] / [disk_res] / [d_lock] *)
Require Import Xv6Cameras.
Require Import WireInv.       (* [wire_inv] *)
Require Import KptExecMap. (* [kmap_at tramp_vpn tramp_ppn KP_rx] *)
Require Import FsCfg.         (* the ambient device names *)
Require Import FileInvDefs.   (* [fileG] -- which carries [fscfg] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SpecFileread.  (* [console_ready_app] -- the PINNED console row *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section SyscParkEnv.
  (* [fileG] IS BOUND HERE since the console row became the PINNED
     [SpecFileread.console_ready_app]: the pin names [AppInv.app_sup], which
     is stated at the application record [fileG] carries. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.

  (* the nextpid lock's gname is EXISTENTIAL, exactly as [sysc_proc_env]
     carries it: nothing outside allocpid ever names it, and a parker that
     had to thread it would be threading a name it cannot otherwise use. *)
  Definition sysc_park_extra (γtk : gname) : iProp Σ :=
    ((∃ γp : gname, is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at) ∗
     procs_avail None ∗
     is_tickslock γtk ∗
     (* THE CONSOLE, PINNED (app-echo.md, lane CONS-CURSOR, the accessor
        ruling).  The console's gname-free form hid the ring's names and
        the credential; the read syscall's receipt is stated at the AMBIENT
        [fsc_cons] and at [AppInv.app_sup], so what the park carries is
        [SpecFileread.console_ready_app] -- the same bundle with only the
        cons lock's gname left existential.  Every carrier of the console
        reaches the read arm, so there is no anonymous form any more. *)
     console_ready_app)%I.

  Global Instance sysc_park_extra_persistent γtk :
    Persistent (sysc_park_extra γtk).
  Proof. rewrite /sysc_park_extra. apply _. Qed.

End SyscParkEnv.

Section ParkWorld.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.

  (* THE PARK'S WORLD, as a process hands it to its children.  A parent that
     forks builds the child's trap-loop environment, and the rows the child
     needs beyond the file system and beyond what [sysc_park_extra] /
     [syscall_env] already carry are: the device complement at the AMBIENT
     names ([UsertrapRes.devintr_caps_any]'s seven members, spelled out here
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
       is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) ∗
       is_tickslock γtl ∗
       procs_inv γs ∗
       console_ready_app ∗
       (* [sysc_park_extra]'s other two rows, so that this bundle covers all
          of it: the nextpid lock and the sealed slot ledger *)
       (∃ γp : gname, is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at) ∗
       procs_avail None ∗
       wire_inv ∗
       kmap_at tramp_vpn tramp_ppn KP_rx ∗
       (* THE USER-EXECUTION WP IS NOT HERE, and deliberately so.  This
          bundle is PERSISTENT and rides in [UsertrapRes.ut_park_caps], so
          a conjunct of it is ambiently duplicable from inside every trap
          round -- which is exactly what a per-process WP must not be.  The
          child's WP is a LINEAR resource the PARKER supplies instead, on
          the park channel ([UsertrapRes.ut_park_intro_body] /
          [ParkCap.park_chan], captured at the park the way the child's
          [fd_frags_any] is -- as the first process's EXEC BUNDLE at
          [ParkCap.park_token_park], as ONE slot at the parked record at
          [ParkCap.park_token_park_steady]).  NOR IS THE APPLICATION'S
          SUPPLY, and that is the point of ARM-c: the kernel mints no slot,
          so it needs no credential to mint one with. *)
       (∃ ip : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈□ ip) ∗
       (* THE SECOND PORT (XV6_REV 163d39b), which is [SpecDevintr.uart1_caps
          fsc_uart] spelled out -- ROW FOR ROW, so [ProofUserinit.v] can pass
          one to the other by [iExact] after unfolding both -- this file sits
          below that one, exactly as
          the six [devintr_caps_any] members above it are spelled out.  The
          ghost bundle is existential for the reason given there: devintr's
          postcondition says nothing about port 1, so nobody has to agree
          with it about which bundle it is.  LAST, so every existing
          destructuring pattern keeps working up to one added name. *)
       (∃ γu1 : uart_names,
          uart_inv Uart1 γu1 ∗ plic_inv fsc_uart γu1 ∗ uart_inited γu1 ∗
          uart_dlab_off γu1))%I.

  Global Instance park_world_persistent γs : Persistent (park_world γs).
  Proof. rewrite /park_world. apply _. Qed.

End ParkWorld.
