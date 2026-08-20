(* SpecUserinit.v -- the public interface of userinit() (kernel/proc.c).
   PROVEN: [ProofUserinit.v] discharges it, [LinkUserinit.v] links it.

     void userinit(void) {
       struct proc *p = allocproc();
       initproc = p;
       p->cwd = namei("/");
       p->state = RUNNABLE;
       release(&p->lock);
     }

   (THIS KERNEL'S userinit, read off [CodeUserinit.v]: twenty-two
   instructions, three calls and two stores.  Upstream's uvmfirst /
   trapframe / safestrcpy lines are not in this image and the decode is what
   says so.)

   ---- THIS FILE USED TO BE AN ASSUMED CONTRACT.  IT IS NOT ANY MORE. ----

   The axiom that stood here assumed userinit's WHOLE BODY, on the grounds
   that namei "drags in the whole file-system cone".  It does not:
   [namei("/")] is a path of one separator, so [skipelem] returns 0 on its
   first call, the walk's body never runs, and the only callee reached is
   [iget(ROOTDEV, ROOTINO)].  What is assumed now is exactly that one call,
   at the premises the boot client can produce
   ([SpecNameiRootBoot.NAMEI_ROOT_BOOT], whose header is the inventory) --
   four persistent inode-cache rows short of a contract the tree already
   proves.  Everything else about userinit is a theorem.

   ---- WHAT IT TAKES ------------------------------------------------------

   THE COUNTED PROC REGIME is the headline.  userinit does NOT test
   allocproc's result -- it stores through the returned pointer at +0x24 --
   so the proof has to REFUTE allocproc's empty-table arm, and
   [ProcAvail.procs_avail (Some (S k))] is the only thing that can
   (claude-notes/kernel-defects.md, "UNREACHABLE, BY THE CALLER'S
   POSITION").  It is threaded exactly as [kalloc_env] is and comes back one
   slot lighter.  The page budget is the same story for allocproc's two
   freeproc failure tails: [K_allocproc < nb] refutes both.

   THE [nextpid] LOCK is allocproc's own premise, and main builds it out of
   procinit's [lk_fresh] and the .data cell (durable-notes.md, "A WRITABLE
   GLOBAL INSIDE THE LOADED IMAGE...").

   THE ONE [iref_slot] namei's [iget] spends is NOT a premise: allocproc
   hands back [iref_slots (1 + IREFSPARE)] and the [1] is exactly it.  In
   kfork that unit pays for [idup]; here it pays for the root's [iget], and
   in both cases it is the working directory's.

   ---- WHAT COMES BACK ----------------------------------------------------

   NOTHING ABOUT THE FIRST PROCESS CROSSES BACK OUT: main does not use
   [initproc], and the process userinit made is reached by the scheduler
   through [procs_inv], which is persistent and rides in unchanged.  The
   RUNNABLE park swallows the private block, the fd allowance and the saved
   context; the [initproc] cell comes back at an unspecified value and the
   two counted regimes come back one unit down.

   THE PAGE COUNT COMES BACK EXISTENTIALLY ([nc <= K_allocproc]) rather than
   at a fixed subtraction: allocproc's own post reports what it spent, and
   inventing a round number here would be [claude-notes/durable-notes.md]'s
   "a numeral that silently encodes another constant's value".

   THE FTABLE'S GNAME DOES NOT APPEAR.  allocproc's post mentions it (in
   [ProcInv.proc_priv_nocwd]) and so does [FORKRET_PARK], but the block
   userinit hands over has every descriptor null, so nothing about the open
   file table is observable in this contract; the proof instantiates both
   callees at one arbitrary name. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import LockRank.
(* the classes the binder list generalizes over -- [fileG] (which carries
   the cache's [icfg] and [icacheG] as superclass fields) and the two device
   ghosts [panic_env] needs.  A bare [Require Import SpecPanic] does not put
   them in scope and backtick generalization then invents fresh binders. *)
Require Import FileInvDefs.
Require Import WpUart DiskPtsto.
Require Import SpecPanic.
Require Import FdSlots.
Require Import SchedCtx.
Require Import KallocInv KvmSpec.
Require Import InodeInv.
Require Import IcacheRef.
Require Import ProcAvail.
Require Import SpecAllocpid.
(* the two callee contracts whose budgets this one is the sum of.  Neither
   pulls the file-system cone: [SpecNameiRootBoot] is a leaf by design (its
   header says why) and [SpecAllocproc] is the proc/kalloc layer. *)
Require Import SpecAllocproc.
Require Import SpecNameiRootBoot.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.


(* userinit's own frame is 32 bytes (4 slots); its deepest callee is [namei]
   at its root corner (74), over allocproc's 48 and release's 10.  Written
   as the sum rather than as 78 (durable-notes.md, "A STACK-BUDGET PREMISE
   IS ARITHMETIC"). *)
Notation K_userinit := ((4 + K_namei_root_boot)%nat) (only parsing).

Definition wp_userinit_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γp : gname) (γs : list gname)
    (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
    (on : option nat) (np : nat) (v0 : mword 64)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.userinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_userinit <= K)%nat ->
  (* allocproc's four pages, at its own STRICT convention *)
  (exists nb, on = Some nb /\ (K_allocproc < nb)%nat) ->
  (* allocproc's own [acquire] is on "proc" (9); the only lock taken while
     it is held is namei's "itable" (14), which follows by
     [LockRank.locks_below_mono]. *)
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* iget's "iget: no inodes" arm is live code *)
  panic_env -∗
  (* the proc array's lock invariant: allocproc scans it, and release gives
     back the slot userinit found.  Persistent, so threading it is free. *)
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  (* ---- the two counted regimes ---- *)
  kalloc_env γa on -∗
  procs_avail (Some (S np)) -∗
  (* the one global cell userinit writes *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0 -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
      sie_cap_gpr KT1 mf K b pj -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf
        /\ mf !!! Regidx (mword_of_int 1 : mword 5)
           = (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) ⌝ -∗
      cpu_own 0%nat eb pj b lks -∗
      (∃ nc : nat, ⌜(nc <= K_allocproc)%nat⌝ ∗
                   kalloc_env γa (avail_sub on nc)) -∗
      procs_avail (Some np) -∗
      (∃ v : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type USERINIT.
  Parameter wp_userinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa γp : gname) (γs : list gname)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
      (on : option nat) (np : nat) (v0 : mword 64)
      (b : bool) (lks : gset string),
      wp_userinit_sconf_body γa γp γs m K eb pj on np v0 b lks.
End USERINIT.
