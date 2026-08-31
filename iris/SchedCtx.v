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
     holds exactly one set at every dispatch.  [IntrDefs.intr_res] -- the
     installed vector and its contract -- is a CONJUNCT of that bundle, so
     the resuming hart's copy crosses with it in both directions; it used to
     be a separate persistent [intr_handler_avail] on the dispatch direction
     only.

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
Require Import IntrDefs.
Require Import HartTp.
Require Import WpLock CtxMorphTac.
Require Import ProcGeom.
(* the proc table's two regimes: [pslot_used_at] is the marker
   [proc_slots] carries on every arm but UNUSED.  EXPORTed because every
   file that states [proc_slots] / [proc_lock_res] / [procs_inv] must bind
   [pavG] (durable-notes.md, "Typeclass sweeps", trap one). *)
Require Export ProcAvail.
Require Import FdSlots.
Require Export IrefSlots.
(* A6.128: [proc_pt]'s pieces are named by the payload's move instances.
   [PtTreeMove] is NOT taken: main's page-table tree is over [↦ₚ₈], which is
   not context-indexed here, so those pieces are ξ-free and the solver's
   constant row closes them. *)
Require Import ProcPtOwn.
Require Import ProcDefs.
Require Import SwtchCtx.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Require Import TsoCtxPark.
Require Import TsoCtxMove.
Local Open Scope Z_scope.

(* the context-slot payload while nobody is parked in it: the raw
   14-word save area (boot; and while the scheduler itself runs).
   (Here rather than CpuOwn.v: it names [ctx_cells], and SwtchCtx now
   sits above CpuOwn so the ambient-bundle wand can mention [cpu_own].) *)
(* NO [CurCtx] BINDER, deliberately.  The slot is the raw 14 words at this
   hart's [a_cpu_ctx] -- pure per-cpu memory geometry, with no thread of
   control in it (that is the whole meaning of "free": nobody is parked
   here).  An inline binder that the body never mentions is a PHANTOM: it
   cannot be inferred, so every consumer inherits an evar.  It broke
   adequacy concretely -- [BootChain.boot_hart_res] picked the context up
   through this conjunct alone, and [BootShared.boot_shared_alloc] mints
   all eight harts' bundles under ONE ambient context, which the primary /
   secondary boot lemmas then try to pin to eight DIFFERENT contexts. *)
Definition cpu_ctx_free `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} : iProp Σ :=
  (* the save-area cells belong to NO thread while free, so their context is
     ∃-quantified (an ambient binder here is the eight-hart adequacy trap
     this file's header records; the scheduler's park/resume proofs trade
     the ∃ for their own ambient through the shim -- the M2 seam). *)
  (* A6.68: IT IS A PARKED RECORD NOW, not a bare ∃.  The scheduler that
     finds the area free has to move its 14 cells into ITS OWN context, and
     at the real machine nothing dominates a bare ∃ξ -- the SC-era trade
     was the shim's [ctx_dom_sc] and it is gone.  What makes the move
     honest is the lock kit's own idiom one tier up (tso-port.md §0.18′):
     the slot carries the record's TOKEN and, beside it, THIS HART's
     receipt that its view has passed the record's stamp.  The absorb is
     then [TsoCtxAbsorbLb.ctx_dom_of_parked_lb] at [T ≤ T], reflexivity.
     At boot the stamp is 0 and [TsoGhost.view_lb_0] gives the receipt for
     nothing; every later publication (a park into this slot) stamps at a
     position its own hart has already passed. *)
  (* main-tso-readiness (M2): the M-leg's SC shape -- the bare ∃-context
     cell run; the claim is the shim's [ctx_dom_sc] (ProofScheduler).  The
     T-leg's parked record + receipt is the cutover shape. *)
  (∃ (vs : list (mword 64)) (ξ : CtxId),
     ⌜ length vs = 14%nat ⌝ ∗
     ctx_cells (XI := ξ) (a_cpu_ctx cid_word) vs)%I.

(* [cpus[h].proc = 0] and [cpus[h].proc = &proc[j]] are the two live values
   of the field, and they are DISJOINT: proc[] does not start at address 0. *)
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
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
     [ctx_word4_pointsto_agree].  Bundled EXISTENTIALLY so that growing the
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
     [intr_handler_avail (CID := h)] USED TO RIDE ON THE DISPATCH DIRECTION
     ONLY -- the persistent half the resumed thread's intena restore needs,
     named at the RESUMING hart's ghost.  It is gone, and nothing replaced it
     here: the installed-handler resource is now [IntrDefs.intr_res], a
     conjunct OF [trap_csrs], so it rides the line above, on BOTH directions.
     That is not a convenience -- being owned, it must come BACK from a
     parking thread, or the resumed scheduler would have no handler to
     dispatch the next one with, and the persistent version simply never had
     to.  ([h] still determines the ghost name, so the payload needs no
     ghost-name argument.) *)
  (* THE SEVENTH SLOT is [SwtchCtx]'s [back]: did the resumer leave a
     resumable record, or only its raw context cells?  [SwtchCtx] does not
     know why the answer is what it is; THIS is where it is decided, and the
     answer is [ProcGeom.needs_ctx st] -- THE PROC LOCK'S OWN PREDICATE.
     [proc_slots] says a slot owns a [▷ proc_ctx] exactly when [needs_ctx st],
     so pinning the crossing to the same predicate makes it deliver precisely
     what the invariant it feeds asks for, with no second, weaker spelling
     (a "not ZOMBIE" test) to keep in step with it.  The dispatch direction
     is [true] unconditionally: the scheduler always comes back. *)
End SchedCtx.

(* A6.128: the payload is stated over the pieces above at an EXPLICIT context,
   so those pieces' section is closed first (their [XI] becomes a parameter). *)
Section SchedCtxPay.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (γs : list gname).

  (* A6.128: THE PAYLOAD IS A FUNCTION OF THE CONTEXT [ξ] -- the identity of
     the thread that holds it, moved across the swtch crossing by
     [TsoCtxMove.ctx_move] ([p_sched_move] below).  The ambient forms the
     consumers wrote stay as they were: at [cur_ctx]. *)
  Definition p_sched : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
                       mword 64 -d> mword 64 -d> bool -d> CtxId -d> iPropO Σ :=
    fun h A' c cret tpv p back ξ =>
    (⌜tpv = cid_word_of h⌝ ∗
     trap_csrs (XI := ξ) KT1 (CID := h) ∗
     ( (* c = the CPU/scheduler context, resumed by a PARKING PROC [cret]
          (sched's swtch): the proc hands over its held lock and the cpu
          cells; its state is one of the two parked states.  [A'] -- the
          resumer's own record index -- is the PARKING PROC's context, and
          it is MIGRATABLE: [None]. *)
       (⌜c = a_cpu_ctx (cid_word_of h)⌝ ∗ ⌜A' = None⌝ ∗
        ∃ (j : nat) (γl : gname) (st : mword 32) (ch : mword 64),
          ⌜cret = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ park_ok st = true /\ back = needs_ctx st⌝ ∗
          proc_held (XI := ξ) h j γl st ch ∗ hart_full j h ∗ park_pay (XI := ξ) (proc_addr j) st)
     ∨ (* c = proc j's context, resumed by THE SCHEDULER [cret] (the
          scheduler's swtch): state already set RUNNING, c->proc = p.  [A']
          is the scheduler's own record, PINNED at [h] -- cpus[h].context
          can only ever be resumed from hart h's own tp, and the parked
          scheduler's closure holds hart-h register resources. *)
       (∃ (j : nat) (γl : gname) (ch : mword 64),
          ⌜c = p_context (proc_addr j) /\ p = proc_addr j /\ (j < NPROC)%nat /\
           γs !! j = Some γl /\ cret = a_cpu_ctx (cid_word_of h) /\
           A' = Some h /\ back = true⌝ ∗
          proc_held (XI := ξ) h j γl RUNNING ch ∗ hart_full j h)))%I.

  (* THE PAYLOAD MOVES BETWEEN CONTEXTS, one [CtxMove] instance per named
     piece: TsoCtxMove's leaf dispatch is syntactic, so a named piece is
     resolved by instance search rather than unfolded by [apply]. *)
  (* EIGHT OF THE TWENTY ARE ξ-FREE ON MAIN and so carry no [(XI := ξ)]
     annotation: [tf_words]/[tf_tail]/[tf_page] are over [↦ₚ₈]/[↦ₚ] and the
     five page-table pieces ([phys_byte_any] … [proc_pt]) over main's
     non-context-indexed physical tier -- which is also why the T-leg's
     [PtTreeMove.v] has no counterpart here. *)
  Global Instance pname_cells_move pa dq bs :
    CtxMove (λ ξ, pname_cells (XI := ξ) pa dq bs).
  Proof. rewrite /pname_cells. ctx_move_solve. Qed.
  Global Instance proc_fields_move pa dq V :
    CtxMove (λ ξ, proc_fields (XI := ξ) pa dq V).
  Proof. rewrite /proc_fields. ctx_move_solve. Qed.
  Global Instance ofile_cells_move pa fs :
    CtxMove (λ ξ, ofile_cells (XI := ξ) pa fs).
  Proof. rewrite /ofile_cells. ctx_move_solve. Qed.
  Global Instance tf_words_move tfp ws :
    CtxMove (λ ξ, tf_words (XI := ξ) tfp ws).
  Proof. rewrite /tf_words. ctx_move_solve. Qed.
  Global Instance tf_tail_move tfp :
    CtxMove (λ ξ, tf_tail (XI := ξ) tfp).
  Proof. rewrite /tf_tail. ctx_move_solve. Qed.
  Global Instance tf_page_move tfp ws :
    CtxMove (λ ξ, tf_page (XI := ξ) tfp ws).
  Proof. rewrite /tf_page. ctx_move_solve. Qed.
  Global Instance is_kstack_move pa ks :
    CtxMove (λ ξ, is_kstack (XI := ξ) pa ks).
  Proof. rewrite /is_kstack. ctx_move_solve. Qed.
  Global Instance kstack_free_move pa :
    CtxMove (λ ξ, kstack_free (XI := ξ) pa).
  Proof. rewrite /kstack_free. ctx_move_solve. Qed.
  Global Instance phys_byte_any_move a :
    CtxMove (λ ξ, phys_byte_any (XI := ξ) a).
  Proof. rewrite /phys_byte_any. ctx_move_solve. Qed.
  Global Instance phys_page_own_move ppn :
    CtxMove (λ ξ, phys_page_own (XI := ξ) ppn).
  Proof. rewrite /phys_page_own. ctx_move_solve. Qed.
  Global Instance upt_pages_own_move um :
    CtxMove (λ ξ, upt_pages_own (XI := ξ) um).
  Proof. rewrite /upt_pages_own. ctx_move_solve. Qed.
  Global Instance proc_pt_own_move P :
    CtxMove (λ ξ, proc_pt_own (XI := ξ) P).
  Proof. rewrite /proc_pt_own. ctx_move_solve. Qed.
  Global Instance proc_pt_move P M :
    CtxMove (λ ξ, proc_pt (XI := ξ) P M).
  Proof. rewrite /proc_pt. ctx_move_solve. Qed.
  Global Instance proc_pt_at_move pa P M :
    CtxMove (λ ξ, proc_pt_at (XI := ξ) pa P M).
  Proof. rewrite /proc_pt_at. ctx_move_solve. Qed.
  Global Instance proc_dormant_noctx_move pa st :
    CtxMove (λ ξ, proc_dormant_noctx (XI := ξ) pa st).
  Proof. rewrite /proc_dormant_noctx. ctx_move_solve. Qed.
  Global Instance locked_move γ i :
    CtxMove (λ ξ, WpLock.locked (XI := ξ) γ i).
  Proof. rewrite /WpLock.locked. ctx_move_solve. Qed.
  Global Instance proc_pub_move pa :
    CtxMove (λ ξ, proc_pub (XI := ξ) pa).
  Proof. rewrite /proc_pub. ctx_move_solve. Qed.
  Global Instance proc_held_move i j γl st ch :
    CtxMove (λ ξ, proc_held (XI := ξ) i j γl st ch).
  Proof. rewrite /proc_held. ctx_move_solve. Qed.
  Global Instance park_pay_move pa st :
    CtxMove (λ ξ, park_pay (XI := ξ) pa st).
  Proof. rewrite /park_pay. ctx_move_solve. Qed.
  (* A6.139: the handler ENVIRONMENT re-homes across the crossing by the
     witness packed beside it in [intr_res]; everything else in the bundle
     is context-free.  These two instances are what lets the payload rows
     stay pinned at the box's own ξ. *)
  Global Instance intr_res_move (kt : ktier) (CIDh : CpuId) :
    CtxMove (CID := CID) (λ ξ, intr_res (XI := ξ) (CID := CIDh) kt).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 Hres".
    iEval (rewrite /intr_res) in "Hres".
    iDestruct "Hres" as (E) "(Hat & #HE & #Hmv)".
    iMod ("Hmv" $! _ ξ0 ξ1 with "H0 H1 HE") as "(H0 & H1 & #HE')".
    iModIntro. iFrame "H0 H1".
    iEval (rewrite /intr_res). iExists E. iFrame "Hat HE' Hmv".
  Qed.

  Global Instance trap_csrs_move (kt : ktier) (CIDh : CpuId) :
    CtxMove (CID := CID) (λ ξ, trap_csrs (XI := ξ) (CID := CIDh) kt).
  Proof. rewrite /trap_csrs. ctx_move_solve. Qed.

  Global Instance p_sched_move h A' c cret tpv p back :
    CtxMove (λ ξ, p_sched h A' c cret tpv p back ξ).
  Proof.
    rewrite /p_sched. ctx_move_solve.
    all: apply (trap_csrs_move KT1 h).
  Qed.


  (* the scheduler-chain valid context, PINNED at hart [h]
     (fixed Phi / P instantiation); [p] = the context's c->proc
     index (see SwtchCtx).  This is the CPU/scheduler record: [cpus[h].context]
     is only ever resumed from hart h's own tp, and the parked scheduler's
     closure holds hart-h register resources.  [sched_vc] is the ambient
     restatement -- the shape a thread running on THIS hart holds of ITS
     scheduler -- and every crossing hands its partner's record back at the
     partner's own hart, so a parking function's continuation states the
     slot with [sched_vc_at h]. *)
  (* A6.127 §6: THE PINNED RECORD KEEPS ITS RUNNING TOKEN.  The scheduler
     never parks; its record carries [own_context (CID := h)] beside the
     record at that identity ([SwtchCtx.park_tok (Some h)]). *)
  Definition sched_vc_at (h : CPU) (c p : mword 64) : iProp Σ :=
    (∃ XIs : CtxId,
       own_context (CID := h) XIs ∗ valid_context p_sched (Some h) c p XIs)%I.

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
    trap_csrs KT1 (CID := i) -∗
    proc_held i j γl st ch -∗
    hart_full j i -∗
    park_pay (proc_addr j) st -∗
    p_sched i None (a_cpu_ctx (cid_word_of i))
      (p_context (proc_addr j)) (cid_word_of i) (proc_addr j) (needs_ctx st) cur_ctx.
  Proof.
    iIntros (Hj Hgl Hst) "Htc Hheld Htag Hpay".
    iSplit; [done|]. iFrame "Htc". iLeft. iSplit; [done|]. iSplit; [done|].
    iExists j, γl, st, ch. iFrame. done.
  Qed.

  (* build the dispatch payload (what the scheduler supplies at its swtch;
     it has just written c->proc = proc_addr j, so its crossing index IS
     proc_addr j).  It hands over its own trap CSRs -- the dispatched
     thread's intena restore reads the handler contract out of them, at ITS
     hart's ghost. *)
  Lemma p_sched_to_proc (i : CPU) (j : nat) (γl : gname) (ch : mword 64) :
    (j < NPROC)%nat -> γs !! j = Some γl ->
    trap_csrs KT1 (CID := i) -∗
    proc_held i j γl RUNNING ch -∗
    hart_full j i -∗
    p_sched i (Some i) (p_context (proc_addr j))
      (a_cpu_ctx (cid_word_of i)) (cid_word_of i) (proc_addr j) true cur_ctx.
  Proof.
    iIntros (Hj Hgl) "Htc Hheld Htag".
    iSplit; [done|]. iFrame "Htc". iRight.
    iExists j, γl, ch. iFrame. done.
  Qed.

  (* a resumed PROC context's payload: the resumer was hart [i]'s scheduler,
     the proc's own lock is held with state RUNNING, and the scheduler's
     record comes back pinned at that hart. *)
  Lemma p_sched_at_proc (i : CPU) (A' : ctx_adm) (j : nat)
      (cret tpv p : mword 64) (back : bool) :
    (j < NPROC)%nat ->
    p_sched i A' (p_context (proc_addr j)) cret tpv p back cur_ctx -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = a_cpu_ctx (cid_word_of i)⌝ ∗
    ⌜p = proc_addr j⌝ ∗ ⌜A' = Some i⌝ ∗ ⌜back = true⌝ ∗
    trap_csrs KT1 (CID := i) ∗
    ∃ (γl : gname) (ch : mword 64),
      ⌜γs !! j = Some γl⌝ ∗ proc_held i j γl RUNNING ch ∗ hart_full j i.
  Proof.
    iIntros (Hj) "(%Htp & Htc & Hpay)". iSplit; [done|].
    iDestruct "Hpay" as "[(%Hc & _ & _) | Hpay]".
    { exfalso.
      exact (a_cpu_ctx_ne_p_context (cid_word_of i) j (tp_ok_cid_of i) Hj (eq_sym Hc)). }
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts Hpay]".
    destruct Hfacts as (Hc & Hp & Hj' & Hgl & Hcret & HA & Hback).
    assert (j' = j) as -> by (apply (p_context_proc_addr_inj j' j Hj' Hj); congruence).
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Htc".
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
  (* THE FLAG IS READ BACK HERE, and it is the parked state's own
     [needs_ctx]: the scheduler learns "there is a record to re-deposit"
     from exactly the predicate the slot it is about to release demands one
     at.  So no case analysis crosses the seam -- the two are the same
     boolean, not two facts to be kept consistent. *)
  Lemma p_sched_at_cpu (i : CPU) (A' : ctx_adm) (j : nat)
      (cret tpv : mword 64) (back : bool) :
    (j < NPROC)%nat ->
    p_sched i A' (a_cpu_ctx (cid_word_of i)) cret tpv (proc_addr j) back cur_ctx -∗
    ⌜tpv = cid_word_of i⌝ ∗ ⌜cret = p_context (proc_addr j)⌝ ∗
    ⌜A' = None⌝ ∗ trap_csrs KT1 (CID := i) ∗
    ∃ (γl : gname) (st : mword 32) (ch : mword 64),
      ⌜γs !! j = Some γl /\ park_ok st = true /\ back = needs_ctx st⌝ ∗
      proc_held i j γl st ch ∗ hart_full j i ∗ park_pay (proc_addr j) st.
  Proof.
    iIntros (Hj) "(%Htp & Htc & Hpay)". iSplit; [done|].
    iDestruct "Hpay" as "[(_ & %HA & Hpay) | Hpay]".
    { iDestruct "Hpay" as (j' γl st ch) "[%Hfacts Hpay]".
      destruct Hfacts as (Hcret & Hp & Hj' & Hgl & Hst & Hback).
      assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
      iSplit; [done|]. iSplit; [done|]. iFrame "Htc".
      iExists γl, st, ch. iFrame. done. }
    iDestruct "Hpay" as (j' γl ch) "[%Hfacts _]".
    destruct Hfacts as (Hc & _ & Hj' & _).
    exfalso. exact (a_cpu_ctx_ne_p_context (cid_word_of i) j' (tp_ok_cid_of i) Hj' Hc).
  Qed.

  (* the ZOMBIE park's reading of the same flag, as a rewrite: [needs_ctx] is
     false there, so the crossing carries [own_ctx] and not a record. *)


  Lemma needs_ctx_ZOMBIE_false : needs_ctx ZOMBIE = false.
  Proof. vm_compute. reflexivity. Qed.

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
  (* A6.127 §6: THE MIGRATABLE RECORD'S TOKEN IS BESIDE IT, LINKED.  The
     record at its own identity [XIp] under the later it always arrives
     beneath; its parked token OUTSIDE the later, with the link
     [ctx_floor ξl Tp] on the slot's context [ξl] -- the ONLY context
     dependence of the slot, which is what makes [proc_lock_pay] a genuine
     λ-payload ([ctx_floor_dom] transports the link; nothing else moves).
     The ambient form [proc_ctx] is the slot at the holder's own context. *)
  Definition proc_ctx_at (ξl : CtxId) (pa : mword 64) : iProp Σ :=
    (∃ (XIp : CtxId) (Tp : nat),
       ctx_parked XIp Tp ∗ ctx_floor ξl Tp ∗
       ▷ valid_context p_sched None (p_context pa) pa XIp)%I.
  Definition proc_ctx (pa : mword 64) : iProp Σ := proc_ctx_at cur_ctx pa.

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

  (* THE RUNNING ARM.  Two things, and the second is the whole
     parked-scheduler protocol -- there is no global box and no receipt:
       - the proc's own context cells, raw, with no resume obligation.  That
         is what lets a TRAP preempt the thread: kerneltrap -> yield ->
         acquire finds the cells here rather than needing them handed down
         from the interrupted frame.
       - THAT HART'S PARKED SCHEDULER RECORD, reached by holding p->lock,
         which every parking path does already.
     The hart is existential (the lock is hart-free, the record is not); the
     tag half collapses it to the ambient hart, timelessly.  [cpus[h].proc]
     is NOT here: it is private to hart [h] and stays whole in that hart's
     [IntrDefs.cpu_cells].  See claude-notes/design/proc-struct.md. *)
  (* A6.129: AT THE LOCK'S CONTEXT [ξl], like every other row of the
     payload -- the cells a lock holder receives are at ITS context, and
     the payload has to transport ([CtxMorph]) for real.  [run_slot] is the
     ambient spelling the consumers keep. *)
  Definition run_slot_at (ξl : CtxId) (pa : mword 64) : iProp Σ :=
    (own_ctx (XI := ξl) (p_context pa) ∗
     ∃ h : CPU,
       hart_at pa (1/2) h ∗
       ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) pa)%I.
  Definition run_slot (pa : mword 64) : iProp Σ := run_slot_at cur_ctx pa.
  (* A6.129: the transports the forked child's record needs -- the context
     field's cells, the running slot, and the lock HANDLES (a handle is the
     name, the invariant and a floor; a floor's dirty arm moves by
     [TsoCtxMove.ctx_move_wrote]). *)
  Global Instance ctx_cells_morph c vs : CtxMorph (λ ξ, ctx_cells (XI := ξ) c vs).
  Proof. rewrite /ctx_cells. apply ctx_cells_at_morph. Qed.
  Global Instance own_ctx_morph pa : CtxMorph (λ ξ, own_ctx (XI := ξ) pa).
  Proof. rewrite /own_ctx. ctx_morph_solve. Qed.
  Global Instance run_slot_at_morph pa : CtxMorph (λ ξ, run_slot_at ξ pa).
  Proof. rewrite /run_slot_at. ctx_morph_solve. Qed.
  Global Instance lk_floor_move (lo : nat) : CtxMove (λ ξ, WpLock.lk_floor ξ lo).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [Hfl | (%a & Hw)]".
    - iMod (ctx_move_floor ξ0 ξ1 lo with "H0 H1 Hfl") as "(H0 & H1 & Hfl)".
      iModIntro. iFrame "H0 H1". by iLeft.
    - iMod (ctx_move_wrote ξ0 ξ1 lo a with "H0 H1 Hw") as "(H0 & H1 & [Hfl | Hw])".
      + iModIntro. iFrame "H0 H1". by iLeft.
      + iModIntro. iFrame "H0 H1". iRight. iExists a. iExact "Hw".
  Qed.
  (* [tso-flip SchedCtx.v:344] has these by [ctx_move_solve]: flip's lock
     word lives in the ξ-CLOSED phys ledger, so [lock_inv] is a ξ-closed
     term there.  On main the word is the ambient ctx cell, so the handle
     transports by the SC shim instead: [TsoCtxShim.ctx_word_shim] /
     [ctx_word4_shim] are [⊣⊢] against the raw cell, hence [lock_inv] is
     ξ-INDEPENDENT under SC and the [inv] re-homes by properness.  The
     STATEMENTS are flip's verbatim; at the cutover (the M4 lock-kit
     reshape, lock_body with the exposed bound) only these proof bodies
     change back to [ctx_move_solve] and the two helpers die. *)
  Local Lemma lock_inv_reindex_sc (ξ0 ξ1 : CtxId) γ lk s R lo :
    WpLock.lock_inv (XI := ξ0) γ lk s R lo ⊣⊢
    WpLock.lock_inv (XI := ξ1) γ lk s R lo.
  Proof.
    rewrite /WpLock.lock_inv /WpLock.lock_word /WpLock.lk_cpu_res.
    setoid_rewrite TsoCtxShim.ctx_word_shim.
    setoid_rewrite TsoCtxShim.ctx_word4_shim.
    reflexivity.
  Qed.

  Local Lemma is_lock_reindex_sc (ξ0 ξ1 : CtxId) γ lk s R :
    is_lock (XI := ξ0) γ lk s R -∗ is_lock (XI := ξ1) γ lk s R.
  Proof.
    rewrite /is_lock. setoid_rewrite (lock_inv_reindex_sc ξ0 ξ1).
    iIntros "(%lo & Hname & Hinv & _)". iExists lo. iFrame "Hname Hinv".
    iApply WpLock.lk_floor_of_ctx. iApply TsoCtxShim.ctx_floor_any.
  Qed.

  Global Instance is_lock_move γ lk s R : CtxMove (λ ξ, is_lock (XI := ξ) γ lk s R).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 Hlk". iModIntro. iFrame "H0 H1".
    by iApply is_lock_reindex_sc.
  Qed.
  Global Instance is_lock_morph γ lk s R : CtxMorph (λ ξ, is_lock (XI := ξ) γ lk s R).
  Proof.
    iIntros (ξ ξ') "Hdom Hlk". iFrame "Hdom". by iApply is_lock_reindex_sc.
  Qed.

  (* ---- THE ALLOCATION MARKER ([ProcAvail.v]).  PERSISTENT, and present on
     every arm but UNUSED: it is what lets allocproc's scan accumulate a
     record of every slot it passed while handing each slot's own copy back
     with its lock, and so what lets a COUNTED caller refute the
     empty-table exit.  ZOMBIE carries it -- a zombie slot is dormant but
     ALLOCATED -- which is why the guard is [is_unused] and not
     [negb (inv_dormant _)].

     It costs the ordinary state changes nothing: [proc_slots_recast] is
     restricted to [inv_dormant _ = false] on both sides, so its two states
     are both allocated and the conjunct is literally the same proposition
     on each. *)
  Definition proc_slots_at (ξl : CtxId) (pa : mword 64) (st : mword 32) : iProp Σ :=
    ((if needs_ctx st   then proc_ctx_at ξl pa   else emp) ∗
     (if is_running st  then run_slot_at ξl pa else emp) ∗
     (if inv_dormant st then proc_dormant (XI := ξl) pa st else emp) ∗
     (if not_running st then hart_at_any pa else emp) ∗
     (if is_unused st   then emp else pslot_used_at pa))%I.
  Definition proc_slots (pa : mword 64) (st : mword 32) : iProp Σ :=
    proc_slots_at cur_ctx pa st.

  Definition proc_lock_res_at (ξl : CtxId) (γl : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       (* A6.129: the cells at [ξl] -- [p_state pa ↦₄ st] when [ξl] is the
          ambient, and transportable otherwise *)
       ctx_word4_pointsto ξl (p_state pa) (DfracOwn 1) st ∗
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
       ctx_word_pointsto ξl (p_chan pa) (DfracOwn 1) ch ∗
       proc_pub (XI := ξl) pa ∗
       proc_slots_at ξl pa st)%I.
  Definition proc_lock_res (γl : gname) (pa : mword 64) : iProp Σ :=
    proc_lock_res_at cur_ctx γl pa.

  (* THE λ-PAYLOAD (A6.121's recipe, A6.127 §6): the lock's payload as a
     function of the holder's context.  Its only context dependence is the
     parked record's link, so the transport obligation is discharged by
     instance search: the floor along [ctx_floor_dom], everything else
     constant. *)
  Definition proc_lock_pay (γl : gname) (pa : mword 64) : CtxId → iProp Σ :=
    λ ξ, proc_lock_res_at ξ γl pa.

  Global Instance proc_ctx_at_morph pa : CtxMorph (λ ξ, proc_ctx_at ξ pa).
  Proof. rewrite /proc_ctx_at. apply _. Qed.
  Global Instance proc_slots_at_morph pa st : CtxMorph (λ ξ, proc_slots_at ξ pa st).
  Proof. rewrite /proc_slots_at. apply _. Qed.
  Global Instance proc_pub_morph pa : CtxMorph (λ ξ, proc_pub (XI := ξ) pa).
  Proof. rewrite /proc_pub. ctx_morph_solve. Qed.
  Global Instance proc_lock_res_at_morph γl pa : CtxMorph (λ ξ, proc_lock_res_at ξ γl pa).
  Proof. rewrite /proc_lock_res_at. ctx_morph_solve. Qed.
  Global Instance proc_lock_pay_morph γl pa : CtxMorph (proc_lock_pay γl pa).
  Proof. rewrite /proc_lock_pay. apply _. Qed.

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
       recast needs no extra premise.  Nor does the allocation marker: both
       states are non-dormant, hence both allocated, so the last conjunct is
       the SAME proposition on each side. *)
    rewrite /proc_slots /proc_slots_at (is_running_negb st) (is_running_negb st').
    rewrite (is_unused_of_inv_dormant st Hd) (is_unused_of_inv_dormant st' Hd').
    rewrite Hn Hr Hd Hd'. iIntros "$".
  Qed.

  (* THE MARKER, READ OFF A SLOT THE SCAN IS PASSING.  Persistent, so the
     slot keeps its own copy and goes straight back into its lock -- which
     is what lets allocproc's scan end holding one for EVERY slot it
     passed, and so lets a counted caller refute the empty-table exit
     ([ProcAvail.v]). *)
  Lemma proc_slots_marker (pa : mword 64) (st : mword 32) :
    is_unused st = false ->
    proc_slots pa st -∗ pslot_used_at pa ∗ proc_slots pa st.
  Proof.
    intros Hu. rewrite {1}/proc_slots {1}/proc_slots_at Hu.
    iIntros "(H1 & H2 & H3 & H4 & #Hm)". iFrame "Hm".
    rewrite /proc_slots /proc_slots_at Hu. iFrame "H1 H2 H3 H4 Hm".
  Qed.

  (* allocproc's move: a slot found UNUSED yields the dormant block and the
     park receipt -- [needs_ctx UNUSED] is false, so the context guard is
     [emp], but UNUSED is not RUNNING, so the receipt IS here and allocproc
     has to carry it to the USED state it re-establishes. *)
  Lemma proc_slots_unused (pa : mword 64) :
    proc_slots pa UNUSED -∗ proc_dormant pa UNUSED ∗ hart_at_any pa.
  Proof.
    rewrite /proc_slots /proc_slots_at inv_dormant_UNUSED not_running_UNUSED is_running_UNUSED
            is_unused_UNUSED.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    iIntros "(_ & _ & $ & $ & _)".
  Qed.

  (* the converse: putting a slot BACK at UNUSED.  freeproc's post is exactly
     [proc_dormant _ UNUSED], so allocproc's failure tails rebuild the lock
     resource through this before they release. *)
  (* Note what this does NOT take: the allocation marker.  Going back to
     UNUSED is where the marker is DROPPED, which is exactly right --
     freeproc gives a slot up, and [ProcAvail]'s authority never shrinks, so
     a freed slot is simply never re-counted as available. *)
  Lemma proc_slots_unused_intro (pa : mword 64) :
    proc_dormant pa UNUSED -∗ hart_at_any pa -∗ proc_slots pa UNUSED.
  Proof.
    rewrite /proc_slots /proc_slots_at inv_dormant_UNUSED not_running_UNUSED is_running_UNUSED
            is_unused_UNUSED.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    iIntros "Hd Hp". iSplitR; [done|]. iSplitR; [done|]. iFrame "Hd Hp".
  Qed.

  (* ... and its USED counterpart.  [needs_ctx USED] is TRUE
     ([ProcGeom.needs_ctx]): a USED proc is one kfork has finished setting up
     and released the lock on, so its slot owns a real parked record exactly
     as RUNNABLE does.  Only the dormant and running guards are false. *)
  Lemma proc_slots_used (pa : mword 64) :
    proc_ctx pa -∗ hart_at_any pa -∗ pslot_used_at pa -∗ proc_slots pa USED.
  Proof.
    rewrite /proc_slots /proc_slots_at inv_dormant_USED not_running_USED is_running_USED
            needs_ctx_USED is_unused_USED.
    iIntros "$ $ $".
  Qed.

  (* THE SCHEDULER'S TWO SLOT MOVES, spelled at the proc-lock end.
     Dispatch takes the receipt out of a parked slot (which also yields the
     saved context the scheduler is about to resume); reclaim puts it back
     into the state the parking proc left behind. *)
  (* the marker comes back OUT here, and every caller that re-parks the slot
     hands it straight to [proc_slots_park].  It is persistent, so nothing
     has to thread it as a resource. *)
  Lemma proc_slots_dispatch (pa : mword 64) (st : mword 32) :
    needs_ctx st = true ->
    proc_slots pa st -∗ proc_ctx pa ∗ hart_at_any pa ∗ pslot_used_at pa.
  Proof.
    intros Hn. rewrite /proc_slots /proc_slots_at Hn.
    rewrite (not_running_of_needs_ctx st Hn).
    rewrite (is_running_of_needs_ctx st Hn).
    rewrite (inv_dormant_of_needs_ctx st Hn).
    rewrite (is_unused_of_needs_ctx st Hn).
    iIntros "[$ [_ [_ [$ $]]]]".
  Qed.

  Lemma proc_slots_park (pa : mword 64) (st : mword 32) :
    needs_ctx st = true ->
    proc_ctx pa -∗ hart_at_any pa -∗ pslot_used_at pa -∗ proc_slots pa st.
  Proof.
    intros Hn. rewrite /proc_slots /proc_slots_at Hn.
    rewrite (not_running_of_needs_ctx st Hn).
    rewrite (is_running_of_needs_ctx st Hn).
    rewrite (inv_dormant_of_needs_ctx st Hn).
    rewrite (is_unused_of_needs_ctx st Hn).
    iIntros "$ $ $".
  Qed.

  (* A6.128: the old [proc_ctx_cells] / [proc_ctx_own_ctx] (a parked record
     forgotten down to [own_ctx] AT THE AMBIENT context) are gone: a record's
     cells live at ITS identity (SwtchCtx.valid_context_pre), and only a
     running context can move them ([TsoCtxMove.ctx_move]).  Neither had a
     consumer. *)

  (* THE RECLAIMING SCHEDULER'S ONE MOVE, at either kind of park: it holds
     the record its swtch handed back, the rejoined receipt, and whatever the
     crossing's [park_pay] carried, and that is [proc_slots] at the state the
     parking thread stored.  Stated once, so the scheduler never cases on the
     state -- the case analysis lives here. *)
  (* THE CONTEXT SLOT ARRIVES IN THE SHAPE THE CROSSING DELIVERED, and that
     is the same [needs_ctx st] guard the slot itself uses
     ([SchedCtx.p_sched]'s [back], [SwtchCtx.valid_context_pre]'s [if]).  A
     resumable park hands over a record; a ZOMBIE park hands over the raw
     cells, because its swtch is not coming back and there is no
     continuation to park.  Nothing is forgotten here any more -- the old
     [proc_ctx_own_ctx] step, which threw a record's parked stack away, is
     gone from this path, and with it the hole it used to leave in the
     dying thread's kernel stack. *)
  Lemma proc_slots_park_gen (E : coPset) (pa : mword 64) (st : mword 32) :
    park_ok st = true ->
    (if needs_ctx st then proc_ctx pa else own_ctx (p_context pa)) -∗
    hart_at_any pa -∗ pslot_used_at pa -∗ park_pay pa st
    ={E}=∗ proc_slots pa st.
  Proof.
    intros Hst. iIntros "Hctx Hpark #Hused Hpay".
    pose proof (is_unused_of_park_ok st Hst) as Hu.
    apply park_ok_cases in Hst as [Hn | Hz].
    - rewrite Hn. iModIntro. rewrite /proc_slots /proc_slots_at Hn Hu.
      rewrite (inv_dormant_of_needs_ctx st Hn) (not_running_of_needs_ctx st Hn).
      rewrite (is_running_of_needs_ctx st Hn).
      iFrame "Hctx Hpark". by iFrame "Hused".
    - subst st. rewrite /park_pay inv_dormant_ZOMBIE needs_ctx_ZOMBIE_false.
      iModIntro. rewrite /proc_slots /proc_slots_at not_running_ZOMBIE inv_dormant_ZOMBIE
                        is_unused_ZOMBIE needs_ctx_ZOMBIE_false is_running_ZOMBIE.
      iSplitR; [done|]. iSplitR; [done|].
      iSplitR "Hpark Hused"; [| iFrame "Hpark Hused"].
      iEval (rewrite proc_dormant_split). iFrame "Hpay Hctx".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* A6.127 §6: THE RECORD/TOKEN SHAPES THE SWTCH CONTRACT SPEAKS.         *)
  (* ------------------------------------------------------------------ *)

  (* the pinned record's running token, into and out of the later the
     record always arrives beneath ([own_context] is timeless) *)
  Lemma sched_vc_at_intro (h : CPU) (c p : mword 64) (XIs : CtxId) :
    own_context (CID := h) XIs -∗ ▷ valid_context p_sched (Some h) c p XIs -∗
    ▷ sched_vc_at h c p.
  Proof.
    iIntros "Hown Hrec". rewrite /sched_vc_at bi.later_exist. iExists XIs.
    rewrite bi.later_sep. iFrame "Hrec". iNext. iExact "Hown".
  Qed.

  Lemma sched_vc_at_tok (E : coPset) (h : CPU) (c p : mword 64) :
    ▷ sched_vc_at h c p ={E}=∗
    ∃ XIs : CtxId, own_context (CID := h) XIs ∗ ▷ valid_context p_sched (Some h) c p XIs.
  Proof.
    rewrite /sched_vc_at bi.later_exist. iIntros "(%XIs & H)".
    rewrite bi.later_sep. iDestruct "H" as "[Hown Hrec]".
    iPoseProof (@timeless _ (own_context (CID := h) XIs) (own_context_timeless XIs)
                  with "Hown") as "Hown".
    iMod "Hown". iModIntro. iExists XIs. iFrame.
  Qed.

  (* a migratable record at the holder's own context IS what swtch wants of
     its target: the link at [cur_ctx] ([SwtchCtx.resume_tok None]) *)
  Lemma proc_ctx_resume_tok (pa : mword 64) :
    proc_ctx pa -∗
    ∃ XIt : CtxId, resume_tok None XIt ∗
                   ▷ valid_context p_sched None (p_context pa) pa XIt.
  Proof.
    rewrite /proc_ctx /proc_ctx_at /resume_tok.
    iIntros "(%XIp & %Tp & Hpk & #Hfl & Hrec)".
    iExists XIp. iFrame "Hrec". iExists Tp. iFrame "Hpk Hfl".
  Qed.

  (* ...and what a park hands back -- the record with its BOX
     ([SwtchCtx.park_tok None]) -- is the slot at the box's context *)
  Lemma proc_ctx_at_of_tok (pa : mword 64) (XIo : CtxId) :
    park_tok None XIo -∗ ▷ valid_context p_sched None (p_context pa) pa XIo -∗
    ∃ (ξb : CtxId) (Tb : nat), ctx_parked ξb Tb ∗ proc_ctx_at ξb pa.
  Proof.
    rewrite /park_tok. iIntros "(%ξb & %Tb & %Tp & Hbox & Hpk & #Hfl) Hrec".
    iExists ξb, Tb. iFrame "Hbox". rewrite /proc_ctx_at.
    iExists XIo, Tp. iFrame "Hpk Hfl Hrec".
  Qed.

  (* a fresh migratable record WITH ITS BOX -- what the child-record producers
     (fork, userinit) mint and their release makes the lock's context *)
  Definition proc_ctx_boxed (pa : mword 64) : iProp Σ :=
    (∃ (ξb : CtxId) (Tb : nat), ctx_parked ξb Tb ∗ proc_ctx_at ξb pa)%I.

  Lemma proc_slots_park_at (ξl : CtxId) (pa : mword 64) (st : mword 32) :
    needs_ctx st = true ->
    proc_ctx_at ξl pa -∗ hart_at_any pa -∗ pslot_used_at pa -∗ proc_slots_at ξl pa st.
  Proof.
    intros Hn. rewrite /proc_slots_at Hn.
    rewrite (not_running_of_needs_ctx st Hn).
    rewrite (is_running_of_needs_ctx st Hn).
    rewrite (inv_dormant_of_needs_ctx st Hn).
    rewrite (is_unused_of_needs_ctx st Hn).
    iIntros "$ $ $".
  Qed.

  (* THE RECLAIMING SCHEDULER'S SLOT, AT THE BOX: [proc_slots_park_gen] with
     the record's box as the slot's context.  A ZOMBIE park brings no box,
     so one is minted -- and (A6.129) the dormant block is DEPOSITED into
     it from the reclaimer's context, which is why the running token comes
     through: the slot's rows are at the box, not at the ambient. *)
  Lemma proc_slots_park_box (pa : mword 64) (st : mword 32) :
    park_ok st = true ->
    own_context cur_ctx -∗
    (if needs_ctx st
     then ∃ (ξb : CtxId) (Tb : nat), ctx_parked ξb Tb ∗ proc_ctx_at ξb pa
     else own_ctx (p_context pa)) -∗
    hart_at_any pa -∗ pslot_used_at pa -∗ park_pay pa st
    ==∗ own_context cur_ctx ∗
        ∃ (ξb : CtxId) (Tb : nat), ctx_parked ξb Tb ∗ proc_slots_at ξb pa st.
  Proof.
    intros Hst. iIntros "Hrun Hctx Hpark #Hused Hpay".
    pose proof (is_unused_of_park_ok st Hst) as Hu.
    apply park_ok_cases in Hst as [Hn | Hz].
    - rewrite Hn. iDestruct "Hctx" as (ξb Tb) "[Hbox Hctx]".
      iModIntro. iFrame "Hrun". iExists ξb, Tb. iFrame "Hbox".
      rewrite /proc_slots_at Hn Hu.
      rewrite (inv_dormant_of_needs_ctx st Hn) (not_running_of_needs_ctx st Hn).
      rewrite (is_running_of_needs_ctx st Hn).
      iFrame "Hctx Hpark". by iFrame "Hused".
    - subst st. rewrite /park_pay inv_dormant_ZOMBIE needs_ctx_ZOMBIE_false.
      iMod ctx_parked_alloc as (ξb) "Hbox".
      iAssert (proc_dormant pa ZOMBIE) with "[Hpay Hctx]" as "Hdorm".
      { iEval (rewrite proc_dormant_split). iFrame "Hpay Hctx". }
      iMod (ctx_deposit (λ ξ, proc_dormant (XI := ξ) pa ZOMBIE) cur_ctx ξb 0
              with "Hrun Hbox Hdorm") as "(Hrun & %Tb & _ & Hbox & Hdorm)".
      iModIntro. iFrame "Hrun". iExists ξb, Tb. iFrame "Hbox".
      rewrite /proc_slots_at not_running_ZOMBIE inv_dormant_ZOMBIE
              is_unused_ZOMBIE needs_ctx_ZOMBIE_false is_running_ZOMBIE.
      iSplitR; [done|]. iSplitR; [done|]. iFrame "Hdorm Hpark Hused".
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
    ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) (proc_addr j) ∗
    pslot_used_at (proc_addr j).
  Proof.
    iIntros (Hj) "Hhlf Hslot".
    rewrite /proc_slots /proc_slots_at.
    (* first: refute [not_running], which is the whole argument. *)
    destruct (not_running st) eqn:Hnr.
    { iDestruct "Hslot" as "(_ & _ & _ & Hany & _)".
      iDestruct (hart_at_any_elim j Hj with "Hany") as (h') "Hfull".
      rewrite /hart_full /hart_hlf /hart_own.
      by iDestruct (ghost_var_valid_2 with "Hhlf Hfull") as %[Hq _]. }
    (* [not_running st = false] settles the state outright, and with it the
       other three guards. *)
    assert (Hrun : st = RUNNING).
    { rewrite /not_running in Hnr.
      apply negb_false_iff, bool_decide_eq_true_1 in Hnr. exact Hnr. }
    subst st.
    rewrite needs_ctx_RUNNING inv_dormant_RUNNING is_running_RUNNING
            is_unused_RUNNING.
    iDestruct "Hslot" as "(_ & Harm & _ & _ & #Hused)".
    rewrite /run_slot /run_slot_at.
    iDestruct "Harm" as "(Hown & (%h' & Hhlf' & Hrec))".
    iDestruct (hart_at_elim j (1/2) h' Hj with "Hhlf'") as "Hhlf'".
    iDestruct (hart_own_agree j (1/2) (1/2) h h' with "Hhlf Hhlf'") as %Hhh.
    subst h'.
    iSplitR; [done|].
    rewrite hart_split. iFrame "Hhlf Hhlf' Hown Hrec". iFrame "Hused".
  Qed.

  (* the converse, for the release side: what a resumed thread deposits when
     it re-establishes a RUNNING slot.  The record came across the
     dispatching swtch. *)
  Lemma proc_slots_running_intro (j : nat) (h : CPU) :
    (j < NPROC)%nat ->
    hart_hlf j h -∗
    own_ctx (p_context (proc_addr j)) -∗
    ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) (proc_addr j) -∗
    pslot_used_at (proc_addr j) -∗
    proc_slots (proc_addr j) RUNNING.
  Proof.
    iIntros (Hj) "Hhlf Hown Hrec #Hused". rewrite /proc_slots /proc_slots_at /run_slot_at.
    rewrite needs_ctx_RUNNING inv_dormant_RUNNING not_running_RUNNING
            is_running_RUNNING is_unused_RUNNING.
    iSplitR; [done|]. iSplitR "Hused"; [| iSplitR; [done | iFrame "Hused"]].
    iFrame "Hown". iExists h. iFrame "Hrec".
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
        is_lock γl (proc_addr i) "proc"%string (proc_lock_pay γl (proc_addr i))) ∗
     [∗ list] i ↦ _ ∈ γs, ∃ ks : mword 64, is_kstack (proc_addr i) ks)%I.

  Global Instance procs_inv_persistent : Persistent procs_inv.
  Proof. apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ is_lock γl (proc_addr i) "proc"%string (proc_lock_pay γl (proc_addr i)).
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
  Proof.
    iIntros "Hs Hg Hc Hpub Hsl". iExists st, ch. iFrame "Hs Hg Hc Hsl". iExact "Hpub".
  Qed.

  (* A6.129: the cells at [ξl] -- the honest statement *)
  Lemma proc_lock_res_at_intro (ξl : CtxId) (γl : gname) (pa : mword 64)
      (st : mword 32) (ch : mword 64) :
    ctx_word4_pointsto ξl (p_state pa) (DfracOwn 1) st -∗
    pstate_lock pa st -∗
    ctx_word_pointsto ξl (p_chan pa) (DfracOwn 1) ch -∗
    proc_pub (XI := ξl) pa -∗
    proc_slots_at ξl pa st -∗
    proc_lock_res_at ξl γl pa.
  Proof. iIntros "Hs Hg Hc Hpub Hsl". iExists st, ch. iFrame. Qed.

  (* A6.129: THE PRODUCER'S FORM -- the cells at the ambient, the slot at a
     PARKED box (a child record's, or the reclaimer's fresh one): the cells
     are deposited into the box from the running context, which raises the
     box's stamp.  What the release then hands the lock is
     [proc_lock_pay_of_box]'s [lock_pay]. *)
  Lemma proc_lock_res_deposit (γl : gname) (pa : mword 64) (st : mword 32) (ch : mword 64)
      (ξb : CtxId) (Tb : nat) :
    own_context cur_ctx -∗ ctx_parked ξb Tb -∗
    p_state pa ↦₄ st -∗
    pstate_lock pa st -∗
    p_chan pa ↦₈ ch -∗
    proc_pub pa -∗
    proc_slots_at ξb pa st ==∗
    own_context cur_ctx ∗
    ∃ Tb' : nat, ⌜(Tb ≤ Tb')%nat⌝ ∗ ctx_parked ξb Tb' ∗ proc_lock_res_at ξb γl pa.
  Proof.
    iIntros "Hrun Hbox Hs Hg Hc Hpub Hsl".
    pose (R := (λ ξ, ctx_word4_pointsto ξ (p_state pa) (DfracOwn 1) st ∗
                     ctx_word_pointsto ξ (p_chan pa) (DfracOwn 1) ch ∗
                     proc_pub (XI := ξ) pa)%I).
    assert (HR : CtxMorph R) by (subst R; ctx_morph_solve).
    iMod (ctx_deposit R cur_ctx ξb Tb with "Hrun Hbox [Hs Hc Hpub]")
      as "(Hrun & %Tb' & %HT & Hbox & (Hs & Hc & Hpub))".
    { subst R. iFrame "Hs Hc". iExact "Hpub". }
    subst R.
    iModIntro. iFrame "Hrun". iExists Tb'. iFrame "Hbox". iSplitR; [done|].
    iApply (proc_lock_res_at_intro with "Hs Hg Hc Hpub Hsl").
  Qed.

  (* the free arm's record, off a slot at its box: what a release that just
     reclaimed a park hands the input-side finisher ([WpLockIn]) *)
  Lemma proc_lock_pay_of_box (γl : gname) (pa : mword 64) :
    (∃ (ξb : CtxId) (Tb : nat), ctx_parked ξb Tb ∗ proc_lock_res_at ξb γl pa) -∗
    lock_pay (proc_lock_pay γl pa).
  Proof. iIntros "(%ξb & %Tb & Hbox & HR)". iExists ξb, Tb. iFrame. Qed.

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

End SchedCtxPay.

(* A6.129: the lock table moves into a forked child's record whole -- stated
   after the section so the table's context is explicit. *)
Section SchedCtxMove.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (γs : list gname).
  Global Instance procs_inv_move : CtxMove (λ ξ, procs_inv (XI := ξ) γs).
  Proof. rewrite /procs_inv. ctx_move_solve. Qed.
  Global Instance procs_inv_morph : CtxMorph (λ ξ, procs_inv (XI := ξ) γs).
  Proof. rewrite /procs_inv. ctx_morph_solve. Qed.
End SchedCtxMove.



(* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md):
   [procs_inv] is two [∗ list]s over NPROC, and it is named in 166 files.
   AT THE END OF THE FILE, so the accessors above -- [procs_inv_len],
   [procs_inv_lookup] and the kstack one -- can still take it apart.  Those
   accessors are what a consumer should use; four files had been hand-rolling
   [iDestruct "Hpinv" as "[%Hl _]"] instead, and now call [procs_inv_len]. *)
Global Typeclasses Opaque procs_inv.
