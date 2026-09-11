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

   WHAT THE LOCK PROTECTS.  Three things, and the last two are the pid
   scan's:

   - the counter cell <nextpid>, IN [1, PIDMAX].  The bound is the whole
     reason the counter is under a lock at all: it is what makes every pid
     <allocpid> hands out nonzero, so the parent of a fork can always tell
     itself from its child.  It is INDUCTIVE across the store the scan makes
     -- [nextpid = (pid == PIDMAX) ? 1 : pid + 1] lands in [1, PIDMAX] from
     either branch -- and it is FOUNDED at boot, where the .data word is
     carved at the pinned value 1 ([BootShared.main_data_raw]) and sealed
     into the payload by main's [newlock].  [ProofAllocproc.wp_ap_pidsec]
     carries it through the retry loop into [SpecAllocproc.allocproc_post],
     from there into [SpecKfork.kfork_post] and the dispatcher's fork row,
     and the trap loop's round reads it as [r <> 0].

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

   - THE PID REGISTER'S AUTHORITY ([SlotGen.pid_reg_auth]), whose domain is
     tied to those 64 cells.  Uniqueness -- no two live processes share a
     pid -- is what it buys, and it is AGREEMENT rather than an invariant:
     a live process's block holds half of -- my pid is registered to my
     generation -- and <wait_lock>'s payload holds the other half, so two
     children of one parent with one pid would be two registrations at one
     key ([SlotGen.pid_reg_agree] refutes it).  allocproc inserts at its
     [p->pid = pid] -- the scan is what proves the key fresh, which is why
     the authority is under THIS lock -- and freeproc deletes at its
     [p->pid = 0].

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
Require Import RiscvPtsto.
Require Import CtxMorphTac.
Require Import ProcGeom.
Require Import SchedCtx.   (* [pid_lock_share_at]: the lock's quarter of each pid cell *)
(* [SlotGen.pid_reg_auth] / [pid_reg_dom]: the pid register this payload
   carries.  Named directly -- the Export chain through [ProcDefs] stops at
   [SchedCtx], which only Imports it. *)
Require Import Xv6Cameras.  (* [wchG]: the register's canonical name *)
Require Import SlotGen.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* the two globals: the lock and the counter it protects *)
Definition alp_pid_lock : mword 64 := mword_of_int KernelSyms.pid_lock.
Definition alp_nextpid  : mword 64 := mword_of_int KernelSyms.nextpid.

Section PidLock.
  (* [wchG]: the pid register's authority lives in this payload
     ([SlotGen.pid_reg_auth], at the canonical [Xv6Cameras.wpr_name]). *)
  Context `{!riscvGS Σ, !wchG Σ}.
  (* M1 flip, STAGE 2: the counter cell is [↦₄], so this payload names a
     context.  Its lock handle is therefore spelled with the λ-CONVERTED
     payload at every mention site (§0.7′ recipe rule 1) rather than under
     [<{ }>] -- which is what keeps [is_lock γp alp_pid_lock "nextpid" …] a
     CLOSED TERM, and hence carryable in tso-port.md §0.12′'s park record
     across a ∀-quantified resume context. *)
  Context `{XI : CurCtx}.

  (* everything <pid_lock> protects: the counter, in [1, PIDMAX], and the
     lock's quarter of every slot's pid cell -- see the header. *)
  (* A6.129 (the M3 λ-conversion): over an EXPLICIT context; [nextpid_res]
     is the ambient spelling *)
  (* THE 64 QUARTERS AT THEIR VALUES, AND THE PID REGISTER'S AUTHORITY.
     The scan reads every [q->pid] under this lock, so the payload carries
     the values as a LIST -- which is what makes -- the candidate is in
     no slot -- a statement about the payload rather than about 64 separate
     existentials -- and beside them the authority of the register
     ([SlotGen.pid_reg_auth]), whose domain is tied to that list:

       EVERY REGISTERED PID IS NONZERO AND IS HELD BY SOME SLOT.

     That direction and no other ([SlotGen.pid_reg_dom]'s note says why),
     because it is the one allocproc spends: a candidate the scan found in
     no slot is a key the authority does not have, so the registration at
     [p->pid = pid] is an INSERT.  freeproc's [p->pid = 0] deletes it.  The
     register is what makes pid uniqueness among live processes a
     RESOURCE -- two halves at one pid agree on the generation
     ([SlotGen.pid_reg_agree]) -- which is what kwait's answer stands on. *)
  Definition nextpid_res_at (ξ : TsoCtx.CtxId) : iProp Σ :=
    ((∃ v : mword 32, TsoCtx.ctx_word4_pointsto ξ alp_nextpid (DfracOwn 1) v ∗
                      ⌜1 <= bv_unsigned v <= PIDMAX⌝) ∗
     (∃ (pids : list (mword 32)) (R : gmap Z gname),
        ⌜length pids = NPROC /\ pid_reg_dom R pids⌝ ∗
        ([∗ list] j ↦ p ∈ pids, pid_lock_share_at ξ (proc_addr j) p) ∗
        pid_reg_auth R))%I.
  Definition nextpid_res : iProp Σ := nextpid_res_at TsoCtx.cur_ctx.

  Global Instance nextpid_res_at_morph : TsoCtx.CtxMorph nextpid_res_at.
  Proof. rewrite /nextpid_res_at /pid_lock_share_at. CtxMorphTac.ctx_morph_solve. Qed.

  (* THE BOOT CARVE'S SHAPE, GATHERED, exactly as the parent cells' is
     ([WaitInv.parents_cells_gather]): the carve hands the 64 quarters out
     indexed by the slot, all at the 0 the .bss pins, and the payload wants
     one LIST of values.  An OFFSET induction because [seq k (S n)] is
     [k :: seq (S k) n]. *)
  Lemma pid_shares_gather (n k : nat) (v : mword 32) :
    ([∗ list] i ∈ seq k n, pid_lock_share_at TsoCtx.cur_ctx (proc_addr i) v)
    -∗ [∗ list] j ↦ p ∈ replicate n v,
         pid_lock_share_at TsoCtx.cur_ctx (proc_addr (k + j)) p.
  Proof.
    revert k. induction n as [|n IH]; intros k.
    - iIntros "_". done.
    - cbn [seq replicate]. rewrite !big_sepL_cons.
      iIntros "[Hhd Htl]".
      iSplitL "Hhd"; [rewrite Nat.add_0_r; iExact "Hhd" |].
      iDestruct (IH (S k) with "Htl") as "Htl".
      iApply (big_sepL_mono with "Htl").
      iIntros (j w _) "Hv".
      replace (k + S j)%nat with (S k + j)%nat by lia.
      iExact "Hv".
  Qed.

  (* the ambient spelling, opened: what allocproc's critical section holds *)
  Lemma nextpid_res_open :
    nextpid_res ⊣⊢
      (∃ v : mword 32, alp_nextpid ↦₄ v ∗ ⌜1 <= bv_unsigned v <= PIDMAX⌝) ∗
      (∃ (pids : list (mword 32)) (R : gmap Z gname),
         ⌜length pids = NPROC /\ pid_reg_dom R pids⌝ ∗
         ([∗ list] j ↦ p ∈ pids, pid_lock_share (proc_addr j) p) ∗
         pid_reg_auth R).
  Proof. rewrite /nextpid_res /nextpid_res_at /pid_lock_share. reflexivity. Qed.

End PidLock.
