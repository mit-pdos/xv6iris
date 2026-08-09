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
     payload's own hart [h].  That is no longer a statement about the
     AMBIENT hart: proc contexts are MIGRATABLE ([ctx_adm = None]), so a
     parked thread resumes on whichever hart's scheduler picked it up and
     learns which one only from the payload.  It is what re-ties the
     received per-cpu cells to the fresh register file's tp, and what makes
     [callee_saved_notp m mf ∧ mf !!! x4 = cid_word_of h] (CalleeSaved.v)
     the honest postcondition of every parking function.
   - The payload also carries the PER-HART trap CSRs [trap_csrs (CID := h)]
     -- yield/sleep hold them across the park (they take acquire's
     [arm_pay] and spend it at their own release), and the scheduler
     holds exactly one set at every dispatch -- and, on the DISPATCH
     direction, the resuming hart's [intr_handler_avail g]: the resumed
     thread's intena retune needs it under the FRESH ghost [g], and its own
     entry stash (taken under its old hart's ghost) is worthless.

   The lock invariant's context slot is ▷-guarded: the scheduler re-stores a
   parked context from the ▷ valid_context its own swtch handed it, and
   every consumer feeds the slot straight into wp_swtch_sconf's ▷ premise. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import excl ofe.
From iris.base_logic.lib Require Import invariants own ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import HartTp.
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
Definition cpu_ctx_free `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} : iProp Σ :=
  (∃ vs : list (mword 64),
     ⌜ length vs = 14%nat ⌝ ∗ ctx_cells (a_cpu_ctx cid_word) vs)%I.

(* the namespace of the global parked-scheduler invariant [scheds_inv]. *)
Definition schedsN : namespace := nroot .@ "scheds".

(* ---------------------------------------------------------------------- *)
(* Pure plumbing for the [∗ list] over [enum CPU] that [scheds_inv]'s body  *)
(* is: a hart's own index into the enumeration.                            *)
(* ---------------------------------------------------------------------- *)
Lemma fin_enum_lookup (n : nat) (h : fin n) :
  fin_enum n !! (fin_to_nat h) = Some h.
Proof.
  induction h as [|n h IH]; simpl; [done|].
  by rewrite list_lookup_fmap IH.
Qed.

Lemma cpu_enum_lookup (h : CPU) : enum CPU !! (fin_to_nat h) = Some h.
Proof. apply fin_enum_lookup. Qed.

(* [cpus[h].proc = 0] and [cpus[h].proc = &proc[j]] are the invariant's two
   live states, and they are DISJOINT: proc[] does not start at address 0. *)
Lemma proc_addr_nonzero (j : nat) :
  (j < NPROC)%nat -> proc_addr j <> (zero_reg : mword 64).
Proof.
  intros Hj Heq.
  apply (f_equal (@bv_unsigned 64)) in Heq.
  rewrite (proc_addr_unsigned j Hj) in Heq.
  assert (bv_unsigned (zero_reg : mword 64) = 0) as Hz
    by (vm_compute; reflexivity).
  rewrite Hz in Heq.
  unfold KernelSyms.proc, proc_size in Heq. lia.
Qed.

Section SchedCtx.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
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
     (claude-notes/completed/sched-hart-generic.md) moves into the payload's
     own binder. *)
  Definition proc_held (i : CPU) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64) : iProp Σ :=
    (locked γl i ∗
     p_state (proc_addr j) ↦₄ st ∗
     (* THE WHOLE STATE MIRROR.  A lock holder has both halves at every
        state: half #1 is the invariant's, out on loan while the lock is
        held, and half #2 is either the invariant's too (unclaimed) or the
        holder's own, since a claimed proc is claimed BY the holder.  The
        split back into [pstate_lock] happens at release
        ([ProcGeom.pstate_whole_split]). *)
     pstate_whole (proc_addr j) st ∗
     p_chan (proc_addr j) ↦₈ ch ∗
     proc_pub (proc_addr j))%I.

  (* ------------------------------------------------------------------ *)
  (* WHAT A PARKING THREAD OWES ITS SLOT BESIDES ITS SAVED CONTEXT.       *)
  (*                                                                      *)
  (* At the two resumable parks (RUNNABLE / SLEEPING) the lock's dormant   *)
  (* guard is [emp] and the answer is nothing: the private block stays     *)
  (* captured in the parked closure, to be handed back when the process    *)
  (* is dispatched again.  At the ZOMBIE park there IS no resumption --    *)
  (* kexit never comes back and the scheduler never dispatches a zombie -- *)
  (* so the block cannot ride a closure: wait()/freeproc, running on       *)
  (* ANOTHER process, must find the user page table and the trapframe      *)
  (* page in the lock.  Hence it crosses here, minus the context cells,    *)
  (* which are what the swtch is about to write ([ProcInv.proc_dormant_    *)
  (* noctx]).                                                             *)
  (* ------------------------------------------------------------------ *)
  Definition park_pay (pa : mword 64) (st : mword 32) : iProp Σ :=
    (if inv_dormant st then proc_dormant_noctx pa st else emp)%I.

  Lemma park_pay_live (pa : mword 64) (st : mword 32) :
    inv_dormant st = false -> ⊢ park_pay pa st.
  Proof. intros Hd. rewrite /park_pay Hd. auto. Qed.

  Lemma park_pay_needs_ctx (pa : mword 64) (st : mword 32) :
    needs_ctx st = true -> ⊢ park_pay pa st.
  Proof. intros Hn. exact (park_pay_live pa st (inv_dormant_of_needs_ctx st Hn)). Qed.

  (* ------------------------------------------------------------------ *)
  (* The chain payload predicate.  The FOURTH argument is the crossing's  *)
  (* c->proc index [p] (the valid_context record's own index, passed      *)
  (* through by the payload slot): both directions of a crossing happen   *)
  (* at the same index -- the dispatcher pre-sets c->proc and nobody else *)
  (* writes it -- and pinning [p = proc_addr j] here is what lets the     *)
  (* RESUMED scheduler identify the parking proc's existential [j] with   *)
  (* its own scan cursor (p_sched_at_cpu below).                          *)
  (* ------------------------------------------------------------------ *)
  (* [h] is the RESUMING hart: every per-hart address, the tp pin and the
     trap CSRs are spelled through [h] rather than the ambient instance, so
     the predicate itself is hart-parametric -- and, since proc records are
     migratable, the payload is the resumed thread's ONLY channel for
     learning [h].
     [trap_csrs (CID := h)] rides on BOTH directions (factored out here):
     the parking side is yield/sleep, which took the CSRs from acquire's
     [arm_pay] and owes them to their own release, entirely inside the
     function -- so the crossing must carry them; the dispatch side is the
     scheduler, which provably holds exactly one set at every dispatch in
     both [eb] arms.
     [intr_handler_avail (CID := h)] rides on the DISPATCH direction only: it
     is the persistent half the resumed thread's intena restore needs, and it
     must be named at the RESUMING hart's ghost (the SIE ghost is per-hart --
     [sie_name h] -- so the thread's own pre-park stash is about the wrong
     name).  That is also why the payload needs no ghost-name argument: [h]
     determines the name. *)
  Definition p_sched : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
                       mword 64 -d> mword 64 -d> iPropO Σ :=
    fun h A' c cret tpv p =>
    (⌜tpv = cid_word_of h⌝ ∗
     trap_csrs (CID := h) ∗
     ( (* c = the CPU/scheduler context, resumed by a PARKING PROC [cret]
          (sched's swtch): the proc hands over its held lock and the cpu
          cells; its state is one of the two parked states.  [A'] -- the
          resumer's own record index -- is the PARKING PROC's context, and
          it is MIGRATABLE: [None]. *)
       (⌜c = a_cpu_ctx (cid_word_of h)⌝ ∗ ⌜A' = None⌝ ∗
        ∃ (j : nat) (γl : gname) (st : mword 32) (ch : mword 64),
          ⌜cret = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ park_ok st = true⌝ ∗
          proc_held h j γl st ch ∗ park_pay (proc_addr j) st)
     ∨ (* c = proc j's context, resumed by THE SCHEDULER [cret] (the
          scheduler's swtch): state already set RUNNING, c->proc = p.  [A']
          is the scheduler's own record, PINNED at [h] -- cpus[h].context
          can only ever be resumed from hart h's own tp, and the parked
          scheduler's closure holds hart-h register resources. *)
       (intr_handler_avail (CID := h) ∗
        ∃ (j : nat) (γl : gname) (ch : mword 64),
          ⌜c = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ cret = a_cpu_ctx (cid_word_of h) /\
           A' = Some h⌝ ∗
          proc_held h j γl RUNNING ch)))%I.

  (* the scheduler-chain valid context, PINNED at hart [h]
     (fixed Phi / P instantiation); [p] = the context's c->proc
     index (see SwtchCtx).  This is the CPU/scheduler record: [cpus[h].context]
     is only ever resumed from hart h's own tp, and the parked scheduler's
     closure holds hart-h register resources.  [sched_vc] is the ambient
     restatement -- the shape a thread running on THIS hart holds of ITS
     scheduler -- and every crossing hands its partner's record back at the
     partner's own hart, so a parking function's continuation states the
     slot with [sched_vc_at h]. *)
  Definition sched_vc_at (h : CPU) (c p : mword 64) : iProp Σ :=
    valid_context p_sched (Some h) c p.

  Definition sched_vc (c p : mword 64) : iProp Σ := sched_vc_at cpu_id c p.

  (* ------------------------------------------------------------------ *)
  (* Payload intro/elim.  Discrimination is by the resumed context's own  *)
  (* address; the other disjunct is refuted by cpus[]/proc[] adjacency.   *)
  (* ------------------------------------------------------------------ *)

  (* build the parking-proc payload (what sched supplies at its swtch;
     [p = proc_addr j] is sched's own cpu_own/premise tie).  The parking
     proc's own record is MIGRATABLE, and it hands over the trap CSRs it
     took from its acquire. *)
  Lemma p_sched_to_cpu (i : CPU) (j : nat) (γl : gname)
      (st : mword 32) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl -> park_ok st = true ->
    trap_csrs (CID := i) -∗
    proc_held i j γl st ch -∗
    park_pay (proc_addr j) st -∗
    p_sched i None (a_cpu_ctx (cid_word_of i))
      (p_context (proc_addr j)) (cid_word_of i) (proc_addr j).
  Proof.
    iIntros (Hj Hgl Hst) "Htc Hheld Hpay".
    iSplit; [done|]. iFrame "Htc". iLeft. iSplit; [done|]. iSplit; [done|].
    iExists j, γl, st, ch. iFrame. done.
  Qed.

  (* build the dispatch payload (what the scheduler supplies at its swtch;
     it has just written c->proc = proc_addr j, so its crossing index IS
     proc_addr j).  It hands over its own trap CSRs and the persistent
     handler-avail at ITS ghost -- the dispatched thread's intena restore
     runs under [g]. *)
  Lemma p_sched_to_proc (i : CPU) (j : nat) (γl : gname) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl ->
    trap_csrs (CID := i) -∗
    intr_handler_avail (CID := i) -∗
    proc_held i j γl RUNNING ch -∗
    p_sched i (Some i) (p_context (proc_addr j))
      (a_cpu_ctx (cid_word_of i)) (cid_word_of i) (proc_addr j).
  Proof.
    iIntros (Hj Hgl) "Htc Havail Hheld".
    iSplit; [done|]. iFrame "Htc". iRight. iSplitL "Havail"; [iExact "Havail"|].
    iExists j, γl, ch. iFrame. done.
  Qed.

  (* a resumed PROC context's payload: the resumer was hart [i]'s scheduler,
     the proc's own lock is held with state RUNNING, and the scheduler's
     record comes back pinned at that hart. *)
  Lemma p_sched_at_proc (i : CPU) (A' : ctx_adm) (j : nat)
      (cret tpv p : mword 64) :
    (j < NPROC)%nat ->
    p_sched i A' (p_context (proc_addr j)) cret tpv p -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = a_cpu_ctx (cid_word_of i)⌝ ∗
    ⌜p = proc_addr j⌝ ∗ ⌜A' = Some i⌝ ∗
    trap_csrs (CID := i) ∗ intr_handler_avail (CID := i) ∗
    ∃ (γl : gname) (ch : mword 64),
      ⌜γs !! j = Some γl⌝ ∗ proc_held i j γl RUNNING ch.
  Proof.
    iIntros (Hj) "(%Htp & Htc & Hpay)". iSplit; [done|].
    iDestruct "Hpay" as "[(%Hc & _ & _) | Hpay]".
    { exfalso.
      exact (a_cpu_ctx_ne_p_context (cid_word_of i) j (tp_ok_cid_of i) Hj (eq_sym Hc)). }
    iDestruct "Hpay" as "(#Havail & Hpay)".
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts Hpay]".
    destruct Hfacts as (Hc & Hp & Hj' & Hgl & Hcret & HA).
    assert (j' = j) as -> by (apply (p_context_proc_addr_inj j' j Hj' Hj); congruence).
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Htc". iSplitR; [iApply "Havail"|].
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
  Lemma p_sched_at_cpu (i : CPU) (A' : ctx_adm) (j : nat)
      (cret tpv : mword 64) :
    (j < NPROC)%nat ->
    p_sched i A' (a_cpu_ctx (cid_word_of i)) cret tpv (proc_addr j) -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = p_context (proc_addr j)⌝ ∗
    ⌜A' = None⌝ ∗ trap_csrs (CID := i) ∗
    ∃ (γl : gname) (st : mword 32) (ch : mword 64),
      ⌜γs !! j = Some γl /\ park_ok st = true⌝ ∗
      proc_held i j γl st ch ∗ park_pay (proc_addr j) st.
  Proof.
    iIntros (Hj) "(%Htp & Htc & Hpay)". iSplit; [done|].
    iDestruct "Hpay" as "[(_ & %HA & Hpay) | Hpay]".
    { iDestruct "Hpay" as (j' γl st ch) "[%Hfacts Hpay]".
      destruct Hfacts as (Hcret & Hp & Hj' & Hgl & Hst).
      assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
      iSplit; [done|]. iSplit; [done|]. iFrame "Htc".
      iExists γl, st, ch. iFrame. done. }
    iDestruct "Hpay" as "(_ & Hpay)".
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
     right after the dispatcher set c->proc to it, and never wrote it), and
     it is MIGRATABLE -- [ctx_adm = None].  This is the whole point of the
     hart-generic protocol: real xv6 lets ANY hart's scheduler dispatch any
     RUNNABLE proc, so the record stored in a proc's lock can name neither a
     hart nor a per-hart SIE ghost.  Consequently [proc_lock_res] and
     [procs_inv] below mention neither -- which is what lets ONE [procs_inv]
     ride the [started] payload to every secondary hart. *)
  Definition proc_ctx (pa : mword 64) : iProp Σ :=
    valid_context p_sched None (p_context pa) pa.

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
  (*   - the HART TAG ([ProcGeom.hart_at_any]), whole here exactly while the *)
  (*     proc is not RUNNING and its value then meaningless; while it IS     *)
  (*     running the tag is split, half in the running arm below and half in *)
  (*     [IntrDefs.cpu_claim].  It moves on exactly the two transitions that *)
  (*     change running-ness, so wakeup and kill are unaffected.            *)
  (* ------------------------------------------------------------------ *)

  (* THE RUNNING ARM.  Three things, and the last two are the whole
     parked-scheduler protocol -- there is no global box and no receipt:
       - the proc's own context cells, raw, with no resume obligation.  That
         is what lets a TRAP preempt the thread: kerneltrap -> yield ->
         acquire finds the cells here rather than needing them handed down
         from the interrupted frame.
       - the OTHER half of [c->proc] for the hart running it, which is what
         lets the scheduler store that field -- it needs the whole cell, and
         gets it by holding this lock.
       - THAT HART'S PARKED SCHEDULER RECORD, reached by holding p->lock,
         which every parking path does already.
     The hart is existential (the lock is hart-free, the record is not); the
     tag half collapses it to the ambient hart, timelessly.  See
     claude-notes/design/proc-struct.md. *)
  Definition run_slot (pa : mword 64) : iProp Σ :=
    (own_ctx (p_context pa) ∗
     ∃ h : CPU,
       hart_at pa (1/2) h ∗
       cpu_proc_half h pa ∗
       ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) pa)%I.

  Definition proc_slots (pa : mword 64) (st : mword 32) : iProp Σ :=
    ((if needs_ctx st   then ▷ proc_ctx pa   else emp) ∗
     (if is_running st  then run_slot pa else emp) ∗
     (if inv_dormant st then proc_dormant pa st else emp) ∗
     (if not_running st then hart_at_any pa else emp))%I.

  Definition proc_lock_res (γl : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       p_state pa ↦₄ st ∗
       (* THE STATE MIRROR'S LOCK-SIDE SHARE, at the same [st] the cell holds.
          Half #1 is the tie: nothing moves the cell without moving the ghost,
          and a ghost_var does not move on half alone.  Half #2 is here too
          exactly on [unclaimed] -- so on an unclaimed state the lock can move
          the state by itself, and on a claimed one the claimant must bring
          the other half.  THE RIGHT TO WRITE [p->state] IS OWNERSHIP OF
          HALF #2.

          It lives HERE rather than in [proc_slots] because it is keyed on
          [st] itself: putting it in a slot arm would make [proc_slots_recast]
          -- the resource-free state change -- have to move a ghost. *)
       pstate_lock pa st ∗
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
    not_running st' = not_running st ->
    inv_dormant st = false -> inv_dormant st' = false ->
    proc_slots pa st -∗ proc_slots pa st'.
  Proof.
    intros Hn Hr Hd Hd'.
    (* [is_running] is [negb not_running], so [Hr] fixes the new arm too --
       recast needs no extra premise. *)
    rewrite /proc_slots (is_running_negb st) (is_running_negb st').
    rewrite Hn Hr Hd Hd'. iIntros "$".
  Qed.

  (* allocproc's move: a slot found UNUSED yields the dormant block and the
     park receipt -- [needs_ctx UNUSED] is false, so the context guard is
     [emp], but UNUSED is not RUNNING, so the receipt IS here and allocproc
     has to carry it to the USED state it re-establishes. *)
  Lemma proc_slots_unused (pa : mword 64) :
    proc_slots pa UNUSED -∗ proc_dormant pa UNUSED ∗ hart_at_any pa.
  Proof.
    rewrite /proc_slots inv_dormant_UNUSED not_running_UNUSED is_running_UNUSED.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    iIntros "[_ [_ [$ $]]]".
  Qed.

  (* the converse: putting a slot BACK at UNUSED.  freeproc's post is exactly
     [proc_dormant _ UNUSED], so allocproc's failure tails rebuild the lock
     resource through this before they release. *)
  Lemma proc_slots_unused_intro (pa : mword 64) :
    proc_dormant pa UNUSED -∗ hart_at_any pa -∗ proc_slots pa UNUSED.
  Proof.
    rewrite /proc_slots inv_dormant_UNUSED not_running_UNUSED is_running_UNUSED.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    iIntros "Hd Hp". iSplitR; [done|]. iSplitR; [done|]. iFrame "Hd Hp".
  Qed.

  (* ... and its USED counterpart.  [needs_ctx USED] is TRUE
     ([ProcGeom.needs_ctx]): a USED proc is one kfork has finished setting up
     and released the lock on, so its slot owns a real parked record exactly
     as RUNNABLE does.  Only the dormant and running guards are false. *)
  Lemma proc_slots_used (pa : mword 64) :
    ▷ proc_ctx pa -∗ hart_at_any pa -∗ proc_slots pa USED.
  Proof.
    rewrite /proc_slots inv_dormant_USED not_running_USED is_running_USED
            needs_ctx_USED.
    iIntros "$ $".
  Qed.

  (* THE SCHEDULER'S TWO SLOT MOVES, spelled at the proc-lock end.
     Dispatch takes the receipt out of a parked slot (which also yields the
     saved context the scheduler is about to resume); reclaim puts it back
     into the state the parking proc left behind. *)
  Lemma proc_slots_dispatch (pa : mword 64) (st : mword 32) :
    needs_ctx st = true ->
    proc_slots pa st -∗ ▷ proc_ctx pa ∗ hart_at_any pa.
  Proof.
    intros Hn. rewrite /proc_slots Hn.
    rewrite (not_running_of_needs_ctx st Hn).
    rewrite (is_running_of_needs_ctx st Hn).
    rewrite (inv_dormant_of_needs_ctx st Hn).
    iIntros "[$ [_ [_ $]]]".
  Qed.

  Lemma proc_slots_park (pa : mword 64) (st : mword 32) :
    needs_ctx st = true ->
    ▷ proc_ctx pa -∗ hart_at_any pa -∗ proc_slots pa st.
  Proof.
    intros Hn. rewrite /proc_slots Hn.
    rewrite (not_running_of_needs_ctx st Hn).
    rewrite (is_running_of_needs_ctx st Hn).
    rewrite (inv_dormant_of_needs_ctx st Hn).
    iIntros "$ $".
  Qed.

  (* FORGETTING A PARKED RECORD DOWN TO ITS CELLS.  A [valid_context] owns
     its fourteen cells outright ([SwtchCtx.valid_context_pre]); dropping the
     resume wand and the parked stack leaves exactly [own_ctx].  Only the
     ZOMBIE park does this, and it is the honest move: nothing ever resumes a
     zombie, so claiming its saved context is resumable would be a promise
     with no consumer -- and one whose price (a [needs_ctx ZOMBIE] slot) the
     dormant block would have to pay for by giving up its own cells. *)
  Lemma proc_ctx_cells (pa : mword 64) : proc_ctx pa -∗ own_ctx (p_context pa).
  Proof.
    rewrite /proc_ctx valid_context_unfold /valid_context_pre.
    iIntros "(%vs & %av & %Hlen & _ & Hcells & _)".
    iExists vs. by iFrame "Hcells".
  Qed.

  (* ... under the ▷ the record always arrives beneath.  [own_ctx] is
     timeless (its cells are), so the step is a bare update. *)
  (* A FANCY update, not a basic one: stripping a ▷ off a timeless
     proposition needs an except-0 goal, and [|==>] is not one. *)
  Lemma proc_ctx_own_ctx (E : coPset) (pa : mword 64) :
    ▷ proc_ctx pa ={E}=∗ own_ctx (p_context pa).
  Proof.
    iIntros "H".
    iAssert (▷ own_ctx (p_context pa))%I with "[H]" as "H".
    { iNext. by iApply proc_ctx_cells. }
    by iMod "H".
  Qed.

  (* THE RECLAIMING SCHEDULER'S ONE MOVE, at either kind of park: it holds
     the record its swtch handed back, the rejoined receipt, and whatever the
     crossing's [park_pay] carried, and that is [proc_slots] at the state the
     parking thread stored.  Stated once, so the scheduler never cases on the
     state -- the case analysis lives here. *)
  Lemma proc_slots_park_gen (E : coPset) (pa : mword 64) (st : mword 32) :
    park_ok st = true ->
    ▷ proc_ctx pa -∗ hart_at_any pa -∗ park_pay pa st ={E}=∗ proc_slots pa st.
  Proof.
    intros Hst. iIntros "Hctx Hpark Hpay".
    apply park_ok_cases in Hst as [Hn | ->].
    - iModIntro. rewrite /proc_slots Hn.
      rewrite (inv_dormant_of_needs_ctx st Hn) (not_running_of_needs_ctx st Hn).
      rewrite (is_running_of_needs_ctx st Hn).
      iFrame "Hctx". by iFrame "Hpark".
    - rewrite /park_pay inv_dormant_ZOMBIE.
      iMod (proc_ctx_own_ctx E pa with "Hctx") as "Hown".
      iModIntro. rewrite /proc_slots not_running_ZOMBIE inv_dormant_ZOMBIE.
      rewrite (_ : needs_ctx ZOMBIE = false); [| vm_compute; reflexivity].
      rewrite is_running_ZOMBIE.
      iSplitR; [done|]. iSplitR; [done|]. iSplitR "Hpark"; [| iExact "Hpark"].
      iEval (rewrite proc_dormant_split). iFrame "Hpay Hown".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE RUNNING ARM, at its two users.                                   *)
  (*                                                                      *)
  (* Presenting the thread's tag half at an acquired proc lock does two    *)
  (* things at once.  It proves the state under the lock is RUNNING -- at  *)
  (* any other state the lock holds the WHOLE tag, and 1 + 1/2 does not    *)
  (* validate -- and it collapses the arm's existential hart to the        *)
  (* caller's own.  That is what lets yield read the raw context cells AND *)
  (* its hart's parked scheduler out of the lock it just took, rather than *)
  (* being handed them by its caller, which may be kerneltrap and so holds *)
  (* no frame of the thread it preempted.                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_slots_running (j : nat) (h : CPU) (st : mword 32) :
    (j < NPROC)%nat ->
    hart_hlf j h -∗ proc_slots (proc_addr j) st -∗
    ⌜ st = RUNNING ⌝ ∗ hart_full j h ∗
    own_ctx (p_context (proc_addr j)) ∗
    cpu_proc_half h (proc_addr j) ∗
    ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) (proc_addr j).
  Proof.
    iIntros (Hj) "Hhlf Hslot".
    rewrite /proc_slots.
    (* first: refute [not_running], which is the whole argument. *)
    destruct (not_running st) eqn:Hnr.
    { iDestruct "Hslot" as "(_ & _ & _ & Hany)".
      iDestruct (hart_at_any_elim j Hj with "Hany") as (h') "Hfull".
      rewrite /hart_full /hart_hlf /hart_own.
      by iDestruct (ghost_var_valid_2 with "Hhlf Hfull") as %[Hq _]. }
    (* [not_running st = false] settles the state outright, and with it the
       other three guards. *)
    assert (Hrun : st = RUNNING).
    { rewrite /not_running in Hnr.
      apply negb_false_iff, bool_decide_eq_true_1 in Hnr. exact Hnr. }
    subst st.
    rewrite needs_ctx_RUNNING inv_dormant_RUNNING is_running_RUNNING.
    iDestruct "Hslot" as "(_ & Harm & _ & _)".
    rewrite /run_slot.
    iDestruct "Harm" as "(Hown & (%h' & Hhlf' & Hph & Hrec))".
    iDestruct (hart_at_elim j (1/2) h' Hj with "Hhlf'") as "Hhlf'".
    iDestruct (hart_own_agree j (1/2) (1/2) h h' with "Hhlf Hhlf'") as %Hhh.
    subst h'.
    iSplitR; [done|].
    rewrite hart_split. iFrame "Hhlf Hhlf' Hown Hph Hrec".
  Qed.

  (* the converse, for the release side: what a resumed thread deposits when
     it re-establishes a RUNNING slot.  Both the record and the spare
     [c->proc] half came across the dispatching swtch. *)
  Lemma proc_slots_running_intro (j : nat) (h : CPU) :
    (j < NPROC)%nat ->
    hart_hlf j h -∗
    own_ctx (p_context (proc_addr j)) -∗
    cpu_proc_half h (proc_addr j) -∗
    ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) (proc_addr j) -∗
    proc_slots (proc_addr j) RUNNING.
  Proof.
    iIntros (Hj) "Hhlf Hown Hph Hrec". rewrite /proc_slots /run_slot.
    rewrite needs_ctx_RUNNING inv_dormant_RUNNING not_running_RUNNING is_running_RUNNING.
    iSplitR; [done|]. iSplitL; [| done].
    iFrame "Hown". iExists h. iFrame "Hph Hrec".
    by iApply (hart_at_intro j (1/2) h Hj).
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
    pstate_lock pa st -∗
    p_chan pa ↦₈ ch -∗
    proc_pub pa -∗
    proc_slots pa st -∗
    proc_lock_res γl pa.
  Proof. iIntros "Hs Hg Hc Hpub Hsl". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γl : gname) (pa : mword 64) :
    proc_lock_res γl pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ pstate_lock pa st ∗
      p_chan pa ↦₈ ch ∗ proc_pub pa ∗ proc_slots pa st.
  Proof. iIntros "H". iExact "H". Qed.

  (* the wakeup transition: a proc found SLEEPING (hence carrying the
     ▷-guarded context), with its state cell flipped to RUNNABLE, still
     satisfies [proc_lock_res].  The saved context survives untouched. *)
  (* SLEEPING and RUNNABLE are both [unclaimed], so the lock holds the WHOLE
     mirror at either and moves it alone -- which is exactly why wakeup and
     kill may write [p->state] without being the claimant. *)
  Lemma proc_lock_res_wakeup (γl : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    st = SLEEPING ->
    p_state pa ↦₄ RUNNABLE -∗
    pstate_lock pa st -∗
    p_chan pa ↦₈ ch -∗
    proc_pub pa -∗
    proc_slots pa st -∗
    |==> proc_lock_res γl pa.
  Proof.
    intros ->. iIntros "Hs Hg Hc Hpub Hsl".
    iMod (pstate_lock_write pa SLEEPING RUNNABLE
            unclaimed_SLEEPING unclaimed_RUNNABLE with "Hg") as "Hg".
    iModIntro. iExists RUNNABLE, ch. iFrame "Hs Hg Hc Hpub".
    iApply (proc_slots_recast pa SLEEPING RUNNABLE
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              with "Hsl").
  Qed.

End SchedCtx.
