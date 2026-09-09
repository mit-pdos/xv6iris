(* PidLock.v -- what <pid_lock> protects (kernel/proc.c), stated at the one
   place that names it.

     static void allocpid(struct proc *p) {      // inlined into allocproc
       acquire(&pid_lock);
       for (;;) {
         pid = nextpid;
         nextpid = (pid == PIDMAX) ? 1 : pid + 1;
         for (q = proc; q < &proc[NPROC]; q++)
           if (q->pid == pid) break;
         if (q == &proc[NPROC]) break;
       }
       p->pid = pid;
       release(&pid_lock);
     }
     ... freeproc():  acquire(&pid_lock); p->pid = 0; release(&pid_lock);

   THIS FILE USED TO BE SpecAllocpid.v.  Upstream ded23f2 ("fix pid
   wraparound/reuse") made allocpid [static] and gave it the retry scan
   above, and gcc inlined it into allocproc -- so there is no <allocpid>
   symbol, no CodeAllocpid.v and no proof to state a contract for.  What
   survives is the LOCK'S RESOURCE, which every consumer of the lock names
   (allocproc, freeproc, kfork, sys_fork, userinit, the syscall environment,
   main's [newlock]), and that is what lives here.

   WHAT THE LOCK PROTECTS.  Two things, and the second is new with ded23f2:

   - the counter cell <nextpid>, value unconstrained.  Nothing in the tree
     consumes a bound on it: allocproc's post quantifies the pid
     existentially, and the pid-wrap row of the user round
     (projects/app-echo.md FORK-ROW) is what a consumer would have to
     retire to want one.  With the retry scan the kernel now DOES keep every
     live pid in [1, PIDMAX] and distinct; carrying that here would need the
     .data word's initial value pinned at boot the way [first] is, and is
     recorded as a follow-up in kernel-defects.md rather than done.

   - A QUARTER OF EVERY proc[i].pid CELL ([SchedCtx.pid_lock_share]).  The
     scan reads [q->pid] for all 64 slots under pid_lock ALONE -- no q->lock
     -- so the lock has to own a read share of each.  The cell's discipline
     (design/proc-struct.md §2) is therefore three-way: 1/4 here, 1/4 in
     the slot's own lock ([SchedCtx.proc_pub]), 1/2 travelling with the
     process ([ProcDefs.proc_priv_bare] / [ProcInv.proc_dormant]).  The two
     writers -- allocproc's [p->pid = pid] and freeproc's [p->pid = 0] --
     both hold all three (p->lock from their caller, pid_lock by their own
     acquire), which is exactly why ded23f2 added the acquire to freeproc.
     [ProcInv.p_pid_join3] / [p_pid_split3] are the reunite/redistribute.

   procinit produces the lock's raw fields; main seals them into this
   [is_lock] over the .data word and the 64 quarters
   ([BootCarveMain.boot_procs_raw] carves them, [SpecMain.main_globals_raw]
   routes them). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock CtxMorphTac.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import SchedCtx.   (* [pid_lock_share_at]: the lock's quarter of each pid cell *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.


(* the two globals: the lock and the counter it protects *)
Definition alp_pid_lock : mword 64 := mword_of_int KernelSyms.pid_lock.
Definition alp_nextpid  : mword 64 := mword_of_int KernelSyms.nextpid.

Section PidLock.
  Context `{!riscvGS Σ}.
  (* M1 flip, STAGE 2: the counter cell is [↦₄], so this payload names a
     context.  Its lock handle is therefore spelled with the λ-CONVERTED
     payload at every mention site (§0.7′ recipe rule 1) rather than under
     [<{ }>] -- which is what keeps [is_lock γp alp_pid_lock "nextpid" …] a
     CLOSED TERM, and hence carryable in tso-port.md §0.12′'s park record
     across a ∀-quantified resume context. *)
  Context `{XI : CurCtx}.

  (* everything <pid_lock> protects: the counter (value unconstrained) and
     the lock's quarter of every slot's pid cell -- see the header. *)
  (* A6.129 (the M3 λ-conversion): over an EXPLICIT context; [nextpid_res]
     is the ambient spelling *)
  Definition nextpid_res_at (ξ : TsoCtx.CtxId) : iProp Σ :=
    ((∃ v : mword 32, TsoCtx.ctx_word4_pointsto ξ alp_nextpid (DfracOwn 1) v) ∗
     ([∗ list] j ∈ seq 0 NPROC, pid_lock_share_at ξ (proc_addr j)))%I.
  Definition nextpid_res : iProp Σ := nextpid_res_at TsoCtx.cur_ctx.

  Global Instance nextpid_res_at_morph : TsoCtx.CtxMorph nextpid_res_at.
  Proof. rewrite /nextpid_res_at /pid_lock_share_at. CtxMorphTac.ctx_morph_solve. Qed.

  (* the ambient spelling, opened: what allocproc's critical section holds *)
  Lemma nextpid_res_open :
    nextpid_res ⊣⊢
      (∃ v : mword 32, alp_nextpid ↦₄ v) ∗
      ([∗ list] j ∈ seq 0 NPROC, pid_lock_share (proc_addr j)).
  Proof. rewrite /nextpid_res /nextpid_res_at /pid_lock_share. reflexivity. Qed.

End PidLock.
