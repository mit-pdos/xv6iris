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
   - [tpv] is the resumer's tp; [⌜tpv = cid_word_of h⌝] pins it to the
     payload's own hart [h], which is what restores full [callee_saved]
     (incl. x4) in sched's postcondition.  [h] is a PARAMETER of [p_sched];
     [sched_vc] applies it at [cpu_id], so today's chain still runs entirely
     on the ambient hart.

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
Require Import ProcGeom.
Require Import FdSlots.
Require Import ProcInv.
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
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

  (* NOTE: this CPU's [struct cpu] does NOT ride in the payload -- the whole
     [cpu_own γ 1 eb p emp] bundle crosses at the [valid_context] wand
     interface (SwtchCtx.v), at the RESUMER's [eb]/proc; the payload below
     carries only the chain-protocol facts and the held lock. *)

  (* holding proc j's spinlock, contents out: the holder token and the state
     and chan cells.  The lock's own cpu word is inside [lock_inv] and the
     token PINS it at this hart (WpLock.v), which is exactly what holding /
     release need -- so no cell rides here. *)
  (* The lock-protected cells whose VALUES no protocol step needs to name:
     killed and xstate (mutable under p->lock, read by kill / wait), and the
     invariant's permanent HALF of the pid cell -- the other half rides with
     the running process in [ProcInv.proc_priv], and the two agree for free by
     [word4_pointsto_agree].  Bundled EXISTENTIALLY so that growing the
     invariant by these three cells costs every existing caller one opaque
     conjunct instead of three new spec parameters. *)
  Definition proc_pub (pa : mword 64) : iProp Σ :=
    (∃ (kl xs pid : mword 32),
       p_killed pa ↦₄ kl ∗ p_xstate pa ↦₄ xs ∗ p_pid pa ↦₄{DfracOwn (1/2)} pid)%I.

  (* [i] is the hart the lock is held ON -- the hart whose scheduler chain
     this payload half belongs to.  Every current user instantiates it at
     [cpu_id]; the parameter is the seam the hart-generic protocol
     (claude-notes/projects/sched-hart-generic.md) moves into the payload's
     own binder. *)
  Definition proc_held (i : CPU) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64) : iProp Σ :=
    (locked γl i ∗
     p_state (proc_addr j) ↦₄ st ∗
     p_chan (proc_addr j) ↦₈ ch ∗
     proc_pub (proc_addr j))%I.

  (* ------------------------------------------------------------------ *)
  (* The chain payload predicate.  The FOURTH argument is the crossing's  *)
  (* c->proc index [p] (the valid_context record's own index, passed      *)
  (* through by the payload slot): both directions of a crossing happen   *)
  (* at the same index -- the dispatcher pre-sets c->proc and nobody else *)
  (* writes it -- and pinning [p = proc_addr j] here is what lets the     *)
  (* RESUMED scheduler identify the parking proc's existential [j] with   *)
  (* its own scan cursor (p_sched_at_cpu below).                          *)
  (* ------------------------------------------------------------------ *)
  (* [h] is the RESUMING hart: every per-hart address and the tp pin are
     spelled through [cid_word_of h] rather than the ambient instance, so
     the predicate itself is hart-parametric.  [sched_vc] below applies it
     at [cpu_id] -- today's whole chain runs on one hart -- and that single
     application is the seam the hart-generic protocol moves inside the
     stored continuation's own ∀h binder. *)
  Definition p_sched : CPU -d> gname -d> ctx_adm -d> mword 64 -d> mword 64 -d>
                       mword 64 -d> mword 64 -d> iPropO Σ :=
    fun h g A' c cret tpv p =>
    (⌜tpv = cid_word_of h⌝ ∗
     ( (* c = the CPU/scheduler context, resumed by a PARKING PROC [cret]
          (sched's swtch): the proc hands over its held lock and the cpu
          cells; its state is one of the two parked states.  [A'] -- the
          resumer's own record index -- is the PARKING PROC's context: still
          pinned here, [None] (migratable) once the sweep flips proc
          contexts. *)
       (⌜c = a_cpu_ctx (cid_word_of h)⌝ ∗ ⌜A' = Some (h, g)⌝ ∗
        ∃ (j : nat) (γl : gname) (st : mword 32) (ch : mword 64),
          ⌜cret = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ needs_ctx st = true⌝ ∗
          proc_held h j γl st ch)
     ∨ (* c = proc j's context, resumed by THE SCHEDULER [cret] (the
          scheduler's swtch): state already set RUNNING, c->proc = p.  [A']
          is the scheduler's own record, PINNED at (h, g) -- cpus[h].context
          can only ever be resumed from hart h's own tp, and the parked
          scheduler's closure holds hart-h register resources. *)
       (∃ (j : nat) (γl : gname) (ch : mword 64),
          ⌜c = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ cret = a_cpu_ctx (cid_word_of h) /\
           A' = Some (h, g)⌝ ∗
          proc_held h j γl RUNNING ch)))%I.

  (* the scheduler-chain valid context (fixed Phi / P instantiation);
     [p] = the context's c->proc index (see SwtchCtx).  Every record in
     today's chain is PINNED at the ambient hart and its SIE ghost; the
     hart-generic sweep flips the PROC records (proc_ctx below) to [None]. *)
  Definition sched_vc (c p : mword 64) : iProp Σ :=
    valid_context Φ p_sched (Some (cpu_id, γ)) c p.

  (* ------------------------------------------------------------------ *)
  (* Payload intro/elim.  Discrimination is by the resumed context's own  *)
  (* address; the other disjunct is refuted by cpus[]/proc[] adjacency.   *)
  (* ------------------------------------------------------------------ *)

  (* build the parking-proc payload (what sched supplies at its swtch;
     [p = proc_addr j] is sched's own cpu_own/premise tie). *)
  Lemma p_sched_to_cpu (i : CPU) (g : gname) (j : nat) (γl : gname)
      (st : mword 32) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl -> needs_ctx st = true ->
    proc_held i j γl st ch -∗
    p_sched i g (Some (i, g)) (a_cpu_ctx (cid_word_of i))
      (p_context (proc_addr j)) (cid_word_of i) (proc_addr j).
  Proof.
    iIntros (Hj Hgl Hst) "Hheld".
    iSplit; [done|]. iLeft. iSplit; [done|]. iSplit; [done|].
    iExists j, γl, st, ch. iFrame. done.
  Qed.

  (* build the dispatch payload (what the scheduler supplies at its swtch;
     it has just written c->proc = proc_addr j, so its crossing index IS
     proc_addr j). *)
  Lemma p_sched_to_proc (i : CPU) (g : gname) (j : nat) (γl : gname) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl ->
    proc_held i j γl RUNNING ch -∗
    p_sched i g (Some (i, g)) (p_context (proc_addr j))
      (a_cpu_ctx (cid_word_of i)) (cid_word_of i) (proc_addr j).
  Proof.
    iIntros (Hj Hgl) "Hheld".
    iSplit; [done|]. iRight.
    iExists j, γl, ch. iFrame. done.
  Qed.

  (* a resumed PROC context's payload: the resumer was this CPU's scheduler,
     the proc's own lock is held with state RUNNING, and the scheduler's
     record comes back pinned at this hart. *)
  Lemma p_sched_at_proc (i : CPU) (g : gname) (A' : ctx_adm) (j : nat)
      (cret tpv p : mword 64) :
    (j < NPROC)%nat ->
    p_sched i g A' (p_context (proc_addr j)) cret tpv p -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = a_cpu_ctx (cid_word_of i)⌝ ∗
    ⌜p = proc_addr j⌝ ∗ ⌜A' = Some (i, g)⌝ ∗
    ∃ (γl : gname) (ch : mword 64),
      ⌜γs !! j = Some γl⌝ ∗ proc_held i j γl RUNNING ch.
  Proof.
    iIntros (Hj) "[%Htp Hpay]". iSplit; [done|].
    iDestruct "Hpay" as "[(%Hc & _ & _) | Hpay]".
    { exfalso.
      exact (a_cpu_ctx_ne_p_context (cid_word_of i) j (tp_ok_cid_of i) Hj (eq_sym Hc)). }
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts Hpay]".
    destruct Hfacts as (Hc & Hp & Hj' & Hgl & Hcret & HA).
    assert (j' = j) as -> by (apply (p_context_proc_addr_inj j' j Hj' Hj); congruence).
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iExists γl, ch. iFrame. done.
  Qed.

  (* the resumed CPU/scheduler context's payload: the resumer was a parking
     proc holding its own lock in a parked state.  The scheduler KNOWS its
     record's crossing index (it wrote c->proc = proc_addr j before parking),
     so the payload's existential is pinned to its scan cursor by
     [proc_addr] injectivity -- this is what identifies the lock the
     payload delivers with the lock its release is about to give back.  The
     parking proc's own record comes back at the index the payload pins,
     which is what the scheduler re-deposits into that proc's lock. *)
  Lemma p_sched_at_cpu (i : CPU) (g : gname) (A' : ctx_adm) (j : nat)
      (cret tpv : mword 64) :
    (j < NPROC)%nat ->
    p_sched i g A' (a_cpu_ctx (cid_word_of i)) cret tpv (proc_addr j) -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = p_context (proc_addr j)⌝ ∗
    ⌜A' = Some (i, g)⌝ ∗
    ∃ (γl : gname) (st : mword 32) (ch : mword 64),
      ⌜γs !! j = Some γl /\ needs_ctx st = true⌝ ∗
      proc_held i j γl st ch.
  Proof.
    iIntros (Hj) "[%Htp Hpay]". iSplit; [done|].
    iDestruct "Hpay" as "[(_ & %HA & Hpay) | Hpay]".
    { iDestruct "Hpay" as (j' γl st ch) "[%Hfacts Hpay]".
      destruct Hfacts as (Hcret & Hp & Hj' & Hgl & Hst).
      assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
      iSplit; [done|]. iSplit; [done|]. iExists γl, st, ch. iFrame. done. }
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts _]".
    destruct Hfacts as (Hc & _ & Hj' & _).
    exfalso. exact (a_cpu_ctx_ne_p_context (cid_word_of i) j' (tp_ok_cid_of i) Hj' Hc).
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
  (* ------------------------------------------------------------------ *)
  (* The two DETACHABLE slots -- and there are exactly two.               *)
  (*                                                                      *)
  (* Everything else the lock protects sits unconditionally at the top     *)
  (* level of [proc_lock_res], so kill() and wakeup() -- the two functions *)
  (* that walk procs they do not own -- reach every cell they touch        *)
  (* without ever learning the state.  These two genuinely move:           *)
  (*   - the saved context, resident as a live [▷ proc_ctx] exactly on     *)
  (*     RUNNABLE/SLEEPING ([needs_ctx]);                                  *)
  (*   - the private field block ([ProcInv.proc_dormant]), resident        *)
  (*     exactly on UNUSED/ZOMBIE ([inv_dormant]) -- sys_sbrk writes       *)
  (*     [myproc()->sz] with NO lock held, so the invariant can retain no  *)
  (*     fraction of that block while the process is live.                 *)
  (* FLAT and INDEPENDENT: two single-boolean guards side by side, never a *)
  (* nested chain, so no caller destructs more than one.  See              *)
  (* claude-notes/design/proc-struct.md.                                   *)
  (* ------------------------------------------------------------------ *)
  Definition proc_slots (pa : mword 64) (st : mword 32) : iProp Σ :=
    ((if needs_ctx st   then ▷ proc_ctx pa   else emp) ∗
     (if inv_dormant st then proc_dormant pa st else emp))%I.

  Definition proc_lock_res (γl : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       p_state pa ↦₄ st ∗
       p_chan pa ↦₈ ch ∗
       proc_pub pa ∗
       proc_slots pa st)%I.

  (* A state change that moves NO resource -- every transition except the
     allocation/parking ones.  Both side conditions are [vm_compute], and
     because neither [proc_ctx] nor [proc_dormant] is indexed by [st], this
     holds in BOTH directions within a guard class. *)
  (* A state change that moves NO resource.  Restricted to the LIVE class:
     the dormant slot is keyed on [st] (a ZOMBIE owns a user table the
     UNUSED slot has had freed), so ZOMBIE -> UNUSED genuinely moves
     resources and is freeproc's job, not a recast. *)
  Lemma proc_slots_recast (pa : mword 64) (st st' : mword 32) :
    needs_ctx st' = needs_ctx st ->
    inv_dormant st = false -> inv_dormant st' = false ->
    proc_slots pa st -∗ proc_slots pa st'.
  Proof. intros Hn Hd Hd'. rewrite /proc_slots Hn Hd Hd'. iIntros "$". Qed.

  (* allocproc's move: a slot found UNUSED yields the dormant block and
     nothing else -- [needs_ctx UNUSED] is false, so the context guard is
     [emp].  (The converse direction is [proc_lock_res_intro] at USED, where
     BOTH guards are false and the release owes nothing.) *)
  Lemma proc_slots_unused (pa : mword 64) :
    proc_slots pa UNUSED -∗ proc_dormant pa UNUSED.
  Proof.
    rewrite /proc_slots inv_dormant_UNUSED.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    iIntros "[_ $]".
  Qed.

  (* the global proc-array invariant: an [is_lock] over every proc's
     [proc_lock_res], plus every proc's kernel-stack address.
     [p->kstack] is written once by procinit and never again, so
     [ProcInv.is_kstack] is PERSISTENT and belongs here rather than in any
     caller's precondition: allocproc reads [p->kstack] of the slot it
     found, which it cannot name before the scan runs.  The value is
     existential -- the tie to [KvmMap.kstack_va i] is the page-table
     world's business, not the lock protocol's. *)
  Definition procs_inv : iProp Σ :=
    (⌜length γs = NPROC⌝ ∗
     ([∗ list] i ↦ γl ∈ γs,
        is_lock γl (proc_addr i) "proc"%string (proc_lock_res γl (proc_addr i))) ∗
     [∗ list] i ↦ _ ∈ γs, ∃ ks : mword 64, is_kstack (proc_addr i) ks)%I.

  Global Instance procs_inv_persistent : Persistent procs_inv.
  Proof. apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ is_lock γl (proc_addr i) "proc"%string (proc_lock_res γl (proc_addr i)).
  Proof.
    iIntros (Hi) "[_ [Hbig _]]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* the array's length -- what a scan's fuel bound is stated over. *)
  Lemma procs_inv_len : procs_inv -∗ ⌜length γs = NPROC⌝.
  Proof. iIntros "[$ _]". Qed.

  (* ... and the per-proc kstack address. *)
  Lemma procs_inv_kstack (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ ∃ ks : mword 64, is_kstack (proc_addr i) ks.
  Proof.
    iIntros (Hi) "[_ [_ Hbig]]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* reassemble [proc_lock_res] from its parts -- what every release does:
     whatever the (possibly updated) state, if it now demands a context we
     supply the (▷-guarded) [proc_ctx]. *)
  Lemma proc_lock_res_intro (γl : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    p_state pa ↦₄ st -∗
    p_chan pa ↦₈ ch -∗
    proc_pub pa -∗
    proc_slots pa st -∗
    proc_lock_res γl pa.
  Proof. iIntros "Hs Hc Hpub Hsl". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γl : gname) (pa : mword 64) :
    proc_lock_res γl pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ p_chan pa ↦₈ ch ∗ proc_pub pa ∗ proc_slots pa st.
  Proof. iIntros "H". iExact "H". Qed.

  (* the wakeup transition: a proc found SLEEPING (hence carrying the
     ▷-guarded context), with its state cell flipped to RUNNABLE, still
     satisfies [proc_lock_res].  The saved context survives untouched. *)
  Lemma proc_lock_res_wakeup (γl : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    st = SLEEPING ->
    p_state pa ↦₄ RUNNABLE -∗
    p_chan pa ↦₈ ch -∗
    proc_pub pa -∗
    proc_slots pa st -∗
    proc_lock_res γl pa.
  Proof.
    intros ->. iIntros "Hs Hc Hpub Hsl". iExists RUNNABLE, ch. iFrame "Hs Hc Hpub".
    iApply (proc_slots_recast pa SLEEPING RUNNABLE
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hsl").
  Qed.

End SchedCtx.
