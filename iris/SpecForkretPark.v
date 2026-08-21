(* SpecForkretPark.v -- turning a freshly-allocated process's raw saved
   context (ra = forkret, sp = kstack + PGSIZE, twelve don't-care
   callee-saved slots) into a member of the scheduler's swtch chain, i.e.
   [SchedCtx.proc_ctx] -- so that [kfork] and [userinit], the two places a
   process is parked at RUNNABLE from scratch, can release it.

   THERE ARE TWO FORMS OF THIS PARK, and the difference between them is
   the only thing still missing:

     [FORKRET_PARK] / [forkret_park_body] -- HERE, and ASSUMED
       ([LinkForkretPark.v]).  What [ProofKfork.v] and [ProofUserinit.v] are
       functors over; it takes exactly what those two have in hand.

     [SpecForkretParkPaid.FORKRET_PARK_PAID] -- the same park at the
       premises a caller must PAY ([forkret_park_pkg]: the persistent world
       the parked closure captures, the child's free kernel stack, and the
       residue closer that turns forkret's yield into the trap loop's
       kernel-side bundle).  That file's header is the inventory.

   NO PROOF OF EITHER IS IN THE TREE RIGHT NOW.  One used to be -- a functor
   over [FORKRET_NF], forkret MINUS a [first] premise, itself assumed -- and
   it was deleted (last green at 4bbc418f) when forkret's real contract
   moved out from under it.  Forkret is now PROVED outright, boot arm
   included, so a revived park is a functor over [SpecForkret.FORKRET]
   instantiated at [LinkForkret.Forkret], and carries no first-related axiom
   at all.  [SpecForkretParkPaid.v] has been rewritten against that contract
   and states what such a proof proves.

   SO PARKING A FRESH PROCESS IS NOT AN OPEN QUESTION ABOUT FORKRET ANY
   MORE.  It is a question about where a NEW process's half of the kernel
   environment comes from, which is kfork's and userinit's to answer -- and
   it is down to ONE ROW.  Of everything [forkret_park_pkg] asks: the
   persistent world is free, [pslot_used_at] is already in allocproc's
   postcondition, and the child's free kernel stack is too
   ([ProcDefs.kstack_free], a conjunct of [proc_dormant], handed back beside
   the [is_kstack] this contract takes).  What has no source is
   [bslots (un_bn N) 3], the first conjunct of [UsertrapRes.ut_own_nopt];
   see [SpecForkretParkPaid.v] for why the fix is a carve at procinit rather
   than a WP step.

   THE ASSUMED FORM IS NOT A DESIGN SHORTCUT; IT IS A REAL, PRE-EXISTING GAP
   THAT KFORK IS THE FIRST FUNCTION TO NEED CLOSED.  [SchedCtx.proc_ctx pa]
   unfolds to
   [SwtchCtx.valid_context p_sched None (p_context pa) pa], a Löb/guarded
   fixpoint whose obligation is literally "prove a WP for the code that runs
   when this context is resumed" -- i.e. proving that a scheduler which picks
   this process up, swtch's into it, and lands at [forkret] actually behaves
   (forkret -> usertrapret -> userret -> user execution, re-establishing the
   very same obligation at ITS next park).  [SpecAllocproc.v]'s own header
   says whose job that is --

     "turning 'ra = forkret, sp = kstack + PGSIZE' into a member of the
      scheduler's swtch chain is a Löb argument about forkret, which
      belongs to the caller that parks the process, not here"

   -- and [ProofUserinit.v], the ONE other place a process is parked at
   RUNNABLE from scratch, is now a REAL PROOF over this contract (2026-08-19;
   it used to sidestep the question by being a wholesale [Axiom], which is
   what an earlier revision of this paragraph described).  So both parkers
   are ordinary provable code and both take this one step assumed: kfork's
   body (allocproc, uvmcopy, the trapframe copy, the filedup scan, idup,
   safestrcpy, the two lock crossings) and userinit's (allocproc, the
   [initproc] store, namei, the state write, the release) are proved around
   it.  Boxing either of THOSE into one Axiom to avoid this step would throw
   away everything real about the proof.  So this file isolates exactly the
   missing step, in the same
   [Module Type] + [Axiom]-in-the-Link shape [SpecIput.v] already uses,
   which is what lets [ProofKfork.v] be a functor over it: when kfork can
   pay [forkret_park_pkg], its [Axiom] is replaced by an application of
   [ProofForkretPark.ForkretParkProof], and nothing about [ProofKfork.v]
   itself changes beyond that one new premise.

   WHAT IT TAKES: precisely what [allocproc]'s own postcondition hands the
   caller for the context (raw [ctx_cells], [is_kstack]) plus everything the
   finished child OWNS by the time kfork is ready to release it at RUNNABLE
   ([proc_priv], the [fd_slots FDSPARE] allowance that travels beside it for
   a live process -- design/proc-struct.md's file-table.md cross-reference).
   Nothing about [p_sched]/[Φ]/[γs] is exposed beyond what [proc_ctx] itself
   already closes over (Section parameters of [SchedCtx.v]); the caller
   supplies them the same way it supplies [procs_inv γs] anywhere else. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* the value [p->context.ra] holds for a fresh, never-yet-run process --
   duplicated from [SpecAllocproc.forkret_pc] rather than imported, so this
   file does not need to pull in the whole allocator/allocproc cone just to
   name one constant. *)
Definition forkret_pc : mword 64 := mword_of_int KernelSyms.forkret.

Definition forkret_park_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname)
    (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (V : pprivate) : Prop :=
  (length rest = 12%nat) ->
  ⊢ is_kstack pa ks -∗
    ctx_cells (p_context pa) (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    proc_priv γf pa pid V -∗
    fd_slots FDSPARE -∗
    (* the iref allowance travels beside the block for [FDSPARE]'s reason:
       a syscall borrows from it for references in flight, so it cannot live
       INSIDE [proc_priv], whose every accessor swallows the block.  The
       cwd's own unit is NOT here -- a live process has a real [cwd_ref] and
       the unit is parked in the itable against it. *)
    iref_slots IREFSPARE -∗
    |==> ▷ proc_ctx γs pa.

Module Type FORKRET_PARK.
  Parameter forkret_park :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname)
      (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate),
      forkret_park_body γs γf pa ks rest pid V.
End FORKRET_PARK.
