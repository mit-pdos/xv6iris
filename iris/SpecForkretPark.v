(* SpecForkretPark.v -- a NEW assumed contract: turning a freshly-allocated
   process's raw saved context (ra = forkret, sp = kstack + PGSIZE, twelve
   don't-care callee-saved slots) into a member of the scheduler's swtch
   chain, i.e. [SchedCtx.proc_ctx] -- so that [kfork] (and, eventually,
   [userinit]) can release the process at RUNNABLE.

   THIS IS NOT A DESIGN SHORTCUT; IT IS A REAL, PRE-EXISTING GAP THAT KFORK
   IS THE FIRST FUNCTION TO NEED CLOSED.  [SchedCtx.proc_ctx pa] unfolds to
   [SwtchCtx.valid_context Φ p_sched None (p_context pa) pa], a Löb/guarded
   fixpoint whose obligation is literally "prove a WP for the code that runs
   when this context is resumed" -- i.e. proving that a scheduler which picks
   this process up, swtch's into it, and lands at [forkret] actually behaves
   (forkret -> usertrapret -> userret -> user execution, re-establishing the
   very same obligation at ITS next park).  Nothing in this tree does that
   proof today: [SpecAllocproc.v]'s own header says as much --

     "turning 'ra = forkret, sp = kstack + PGSIZE' into a member of the
      scheduler's swtch chain is a Löb argument about forkret, which
      belongs to the caller that parks the process, not here"

   -- and [SpecUserinit.v], the ONE other place a process is parked at
   RUNNABLE from scratch, sidesteps the question entirely by being a
   wholesale [Axiom] (no [ProofUserinit.v] exists).  kfork cannot dodge it
   the same way -- unlike userinit, kfork's own body (allocproc, uvmcopy,
   the trapframe copy, the filedup scan, idup, safestrcpy, the two lock
   crossings) is ordinary, provable code, and boxing all of THAT into one
   Axiom just to avoid this one step would throw away everything real about
   the proof.  So this file isolates exactly the missing step, in the same
   [Module Type] + [Axiom]-in-the-Link shape [SpecIput.v] already uses,
   which is what lets [ProofKfork.v] be a functor over it: the day someone
   proves [forkret]/[usertrapret]/[userret] for real (claude-notes/projects/
   uservec.md is the tracker for that cone), this file and its [Axiom] are
   what get replaced, and nothing about [ProofKfork.v] itself changes.

   WHAT IT TAKES: precisely what [allocproc]'s own postcondition hands the
   caller for the context (raw [ctx_cells], [is_kstack]) plus everything the
   finished child OWNS by the time kfork is ready to release it at RUNNABLE
   ([proc_priv], the [fd_slots FDSPARE] allowance that travels beside it for
   a live process -- design/proc-struct.md's file-table.md cross-reference).
   Nothing about [p_sched]/[Φ]/[γs] is exposed beyond what [proc_ctx] itself
   already closes over (Section parameters of [SchedCtx.v]); the caller
   supplies them the same way it supplies [procs_inv Φ γs] anywhere else. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import SwtchCtx.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* the value [p->context.ra] holds for a fresh, never-yet-run process --
   duplicated from [SpecAllocproc.forkret_pc] rather than imported, so this
   file does not need to pull in the whole allocator/allocproc cone just to
   name one constant. *)
Definition forkret_pc : mword 64 := mword_of_int KernelSyms.forkret.

Definition forkret_park_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γs : list gname)
    (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (V : pprivate) : Prop :=
  (length rest = 12%nat) ->
  ⊢ is_kstack pa ks -∗
    ctx_cells (p_context pa) (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    proc_priv γf pa pid V -∗
    fd_slots FDSPARE -∗
    |==> ▷ proc_ctx Φ γs pa.

Module Type FORKRET_PARK.
  Parameter forkret_park :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname)
      (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate),
      forkret_park_body Φ γs γf pa ks rest pid V.
End FORKRET_PARK.
