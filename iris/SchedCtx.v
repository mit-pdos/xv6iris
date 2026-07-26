(* SchedCtx.v -- the scheduler swtch protocol: the ONE chain payload
   predicate [p_sched] for every scheduler context switch on this CPU, and
   the per-proc lock invariant ([proc_lock_res] / [procs_inv]) built on it.

   Protocol (see claude-notes/projects/yield-sched.md):

   - A running kernel thread holds, besides its sconf-tier resources, the
     ▷-guarded valid context of THIS CPU's parked scheduler
     ([sched_vc (a_cpu_ctx cid_word)] under ▷), its own context-field cells
     ([ctx_cells (p_context p)] -- handed back by the resume wand), and the
     current-process resource ([cur_proc p], ProcGeom.v).
   - sched() swtches into the scheduler context, supplying [p_sched]'s
     FIRST disjunct (c = the cpu context, resumed by a parking proc that
     hands over its own held lock, state/chan cells and the cpu cells).
   - The (future) scheduler proof dispatches proc j by supplying the SECOND
     disjunct (c = proc j's context, state already RUNNING, c->proc = p).
   - [p_sched c cret tpv] discriminates on the RESUMED context's own address
     [c] -- a single-P chain rebuilds the suspended old context at the SAME
     P, so per-direction predicates are impossible; the resumed party knows
     its own context address statically and elims the matching disjunct
     (address disjointness: cpus[] and proc[] are adjacent, ProcGeom.v).
   - [tpv] is the resumer's tp; [⌜tpv = cid_word⌝] pins it to the ambient
     hart id, which is what restores full [callee_saved] (incl. x4) in
     sched's postcondition.

   The lock invariant's context slot is ▷-guarded: the scheduler re-stores a
   parked context from the ▷ valid_context its own swtch handed it, and
   every consumer feeds the slot straight into wp_swtch_sconf's ▷ premise. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import excl ofe.
From iris.base_logic.lib Require Import invariants own ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import SwtchCtx.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* the context-slot payload while nobody is parked in it: the raw
   14-word save area (boot; and while the scheduler itself runs).
   (Here rather than CpuOwn.v: it names [ctx_cells], and SwtchCtx now
   sits above CpuOwn so the ambient-bundle wand can mention [cpu_own].) *)
Definition cpu_ctx_free `{!riscvGS Σ} `{CID : CpuId} : iProp Σ :=
  (∃ vs : list (mword 64),
     ⌜ length vs = 14%nat ⌝ ∗ ctx_cells (a_cpu_ctx cid_word) vs)%I.

Section SchedCtx.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.
  (* the ambient S-mode world: the SIE ghost name and the whole-machine
     postcondition.  (The kernel page table rides inside [swconf]'s
     translation slot; no root parameter.) *)
  Context (γ : gname) (Φ : mval -> iProp Σ).
  (* the NPROC per-proc lock gnames. *)
  Context (γs : list gname).

  (* ------------------------------------------------------------------ *)
  (* The two payload halves shared by both swtch directions.              *)
  (* ------------------------------------------------------------------ *)

  (* NOTE: this CPU's [struct cpu] no longer rides in the payload -- the
     whole [cpu_own γ 1 eb p emp] bundle crosses at the [valid_context]
     wand interface (SwtchCtx.v), at the RESUMER's [eb]/proc; the payload
     below carries only the chain-protocol facts and the held lock. *)

  (* holding proc j's spinlock, contents out: the holder token and the state
     and chan cells.  The lock's own cpu word is inside [lock_inv] and the
     token PINS it at this hart (WpLock.v), which is exactly what holding /
     release need -- so no cell rides here. *)
  Definition proc_held (j : nat) (γl : gname) (st : mword 32) (ch : mword 64) : iProp Σ :=
    (locked γl cpu_id ∗
     p_state (proc_addr j) ↦₄ st ∗
     p_chan (proc_addr j) ↦₈ ch)%I.

  (* ------------------------------------------------------------------ *)
  (* The chain payload predicate.                                        *)
  (* ------------------------------------------------------------------ *)
  Definition p_sched : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ :=
    fun c cret tpv =>
    (⌜tpv = cid_word⌝ ∗
     ( (* c = the CPU/scheduler context, resumed by a PARKING PROC [cret]
          (sched's swtch): the proc hands over its held lock and the cpu
          cells; its state is one of the two parked states. *)
       (⌜c = a_cpu_ctx cid_word⌝ ∗
        ∃ (j : nat) (γl : gname) (st : mword 32) (ch : mword 64),
          ⌜cret = p_context (proc_addr j) /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ needs_ctx st = true⌝ ∗
          proc_held j γl st ch)
     ∨ (* c = proc j's context, resumed by THE SCHEDULER [cret] (the
          scheduler's swtch): state already set RUNNING, c->proc = p. *)
       (∃ (j : nat) (γl : gname) (ch : mword 64),
          ⌜c = p_context (proc_addr j) /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ cret = a_cpu_ctx cid_word⌝ ∗
          proc_held j γl RUNNING ch)))%I.

  (* the scheduler-chain valid context (fixed γ / Phi / P instantiation);
     [p] = the context's c->proc index (see SwtchCtx). *)
  Definition sched_vc (c p : mword 64) : iProp Σ :=
    valid_context γ Φ p_sched c p.

  (* ------------------------------------------------------------------ *)
  (* Payload intro/elim.  Discrimination is by the resumed context's own  *)
  (* address; the other disjunct is refuted by cpus[]/proc[] adjacency.   *)
  (* ------------------------------------------------------------------ *)

  (* build the parking-proc payload (what sched supplies at its swtch). *)
  Lemma p_sched_to_cpu (j : nat) (γl : gname) (st : mword 32) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl -> needs_ctx st = true ->
    proc_held j γl st ch -∗
    p_sched (a_cpu_ctx cid_word) (p_context (proc_addr j)) cid_word.
  Proof.
    iIntros (Hj Hγl Hst) "Hheld".
    iSplit; [done|]. iLeft. iSplit; [done|].
    iExists j, γl, st, ch. iFrame. done.
  Qed.

  (* build the dispatch payload (what the scheduler supplies at its swtch). *)
  Lemma p_sched_to_proc (j : nat) (γl : gname) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl ->
    proc_held j γl RUNNING ch -∗
    p_sched (p_context (proc_addr j)) (a_cpu_ctx cid_word) cid_word.
  Proof.
    iIntros (Hj Hγl) "Hheld".
    iSplit; [done|]. iRight.
    iExists j, γl, ch. iFrame. done.
  Qed.

  (* a resumed PROC context's payload: the resumer was this CPU's scheduler,
     the proc's own lock is held with state RUNNING. *)
  Lemma p_sched_at_proc (j : nat) (cret tpv : mword 64) :
    (j < NPROC)%nat ->
    p_sched (p_context (proc_addr j)) cret tpv -∗
    ⌜tpv = cid_word⌝ ∗ ⌜cret = a_cpu_ctx cid_word⌝ ∗
    ∃ (γl : gname) (ch : mword 64),
      ⌜γs !! j = Some γl⌝ ∗ proc_held j γl RUNNING ch.
  Proof.
    iIntros (Hj) "[%Htp Hpay]". iSplit; [done|].
    iDestruct "Hpay" as "[[%Hc _] | Hpay]".
    { exfalso.
      exact (a_cpu_ctx_ne_p_context cid_word j tp_ok_cid Hj (eq_sym Hc)). }
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts Hpay]".
    destruct Hfacts as (Hc & Hj' & Hγl & Hcret).
    assert (j' = j) as -> by (apply (p_context_proc_addr_inj j' j Hj' Hj); congruence).
    iSplit; [done|]. iExists γl, ch. iFrame. done.
  Qed.

  (* the resumed CPU/scheduler context's payload: the resumer was a parking
     proc holding its own lock in a parked state. *)
  Lemma p_sched_at_cpu (cret tpv : mword 64) :
    p_sched (a_cpu_ctx cid_word) cret tpv -∗
    ⌜tpv = cid_word⌝ ∗
    ∃ (j : nat) (γl : gname) (st : mword 32) (ch : mword 64),
      ⌜cret = p_context (proc_addr j) /\ (j < NPROC)%nat /\
       γs !! j = Some γl /\ needs_ctx st = true⌝ ∗
      proc_held j γl st ch.
  Proof.
    iIntros "[%Htp Hpay]". iSplit; [done|].
    iDestruct "Hpay" as "[[_ Hpay] | Hpay]".
    { iDestruct "Hpay" as (j γl st ch) "[%Hfacts Hpay]".
      iExists j, γl, st, ch. iFrame. done. }
    iDestruct "Hpay" as (j γl ch) "[%Hfacts _]".
    destruct Hfacts as (Hc & Hj & _).
    exfalso. exact (a_cpu_ctx_ne_p_context cid_word j tp_ok_cid Hj Hc).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The per-proc lock invariant.                                        *)
  (* ------------------------------------------------------------------ *)

  (* the valid-context obligation of a parked proc: its saved context is a
     member of the scheduler chain. *)
  (* a parked proc's context is indexed by its OWN proc address (it parked
     right after the dispatcher set c->proc to it, and never wrote it). *)
  Definition proc_ctx (pa : mword 64) : iProp Σ := sched_vc (p_context pa) pa.

  (* the resource protected by [p->lock].  The context slot is ▷-guarded:
     its producer (the scheduler, releasing a freshly parked proc) only ever
     holds the context under ▷ (from its own swtch), and its consumers feed
     it straight into wp_swtch_sconf's ▷ premise. *)
  Definition proc_lock_res (γl : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       p_state pa ↦₄ st ∗
       p_chan pa ↦₈ ch ∗
       (if needs_ctx st then ▷ proc_ctx pa else emp))%I.

  (* the global proc-array invariant: an [is_lock] over every proc's
     [proc_lock_res]. *)
  Definition procs_inv : iProp Σ :=
    (⌜length γs = NPROC⌝ ∗
     [∗ list] i ↦ γl ∈ γs,
       is_lock γl (proc_addr i) "proc"%string (proc_lock_res γl (proc_addr i)))%I.

  Global Instance procs_inv_persistent : Persistent procs_inv.
  Proof. apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ is_lock γl (proc_addr i) "proc"%string (proc_lock_res γl (proc_addr i)).
  Proof.
    iIntros (Hi) "[_ Hbig]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* reassemble [proc_lock_res] from its parts -- what every release does:
     whatever the (possibly updated) state, if it now demands a context we
     supply the (▷-guarded) [proc_ctx]. *)
  Lemma proc_lock_res_intro (γl : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    p_state pa ↦₄ st -∗
    p_chan pa ↦₈ ch -∗
    (if needs_ctx st then ▷ proc_ctx pa else emp) -∗
    proc_lock_res γl pa.
  Proof. iIntros "Hs Hc Hctx". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γl : gname) (pa : mword 64) :
    proc_lock_res γl pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ p_chan pa ↦₈ ch ∗
      (if needs_ctx st then ▷ proc_ctx pa else emp).
  Proof. iIntros "H". iExact "H". Qed.

  (* the wakeup transition: a proc found SLEEPING (hence carrying the
     ▷-guarded context), with its state cell flipped to RUNNABLE, still
     satisfies [proc_lock_res].  The saved context survives untouched. *)
  Lemma proc_lock_res_wakeup (γl : gname) (pa : mword 64) (ch : mword 64) :
    p_state pa ↦₄ RUNNABLE -∗
    p_chan pa ↦₈ ch -∗
    ▷ proc_ctx pa -∗
    proc_lock_res γl pa.
  Proof.
    iIntros "Hs Hc Hctx". iExists RUNNABLE, ch. iFrame "Hs Hc".
    rewrite needs_ctx_RUNNABLE. iExact "Hctx".
  Qed.

End SchedCtx.
