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
From iris.algebra Require Import excl agree ofe.
From iris.base_logic.lib Require Import invariants own ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import IntrDefs.
Require Import HartTp.
Require Import WpLock.
Require Import ProcGeom.
(* the proc table's two regimes: [pslot_used_at] is the marker
   [proc_slots] carries on every arm but UNUSED.  EXPORTed because every
   file that states [proc_slots] / [proc_lock_res] / [procs_inv] must bind
   [pavG] (durable-notes.md, "Typeclass sweeps", trap one). *)
Require Export ProcAvail.
Require Import FdSlots.
Require Export IrefSlots.
(* A6.128: [proc_pt]'s pieces are named by the payload's transport
   instances.  [PtTreeMorph] carries the tree; main's [proc_pt] keys the
   image bytes by [M] beside it. *)
Require Import ProcPtOwn CtxMorphTac.
Require Import ProcDefs.
(* [SlotGen.pid_reg] / [qeighth] -- the killed row's tie (lane SELF-KILL, §1)
   names the incarnation by an eighth of its pid registration. *)
Require Import SlotGen.
(* [ChildTok.kill_owed] / [taken_at] -- the killed row is at the target's own
   exit payload now (owner, 2026-09-13), so it is per-INCARNATION. *)
Require Import ChildTok.
Require Import SwtchCtx.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
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
     then [TsoCtxAbsorbLb.ctx_dom_of_stamped_lb] at [T ≤ T], reflexivity.
     At boot the stamp is 0 and [TsoGhost.view_lb_0] gives the receipt for
     nothing; every later publication (a park into this slot) stamps at a
     position its own hart has already passed. *)
  (∃ (vs : list (mword 64)) (ξ : CtxId) (T : nat),
     ⌜ length vs = 14%nat ⌝ ∗
     TsoCtx.ctx_stamped ξ T ∗ TsoCtx.hart_view_lb T ∗
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
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
  (* THE pid_lock's SHARE OF ONE SLOT'S pid CELL.  allocproc's pid scan
     (upstream ded23f2: allocpid retries until it finds a pid no slot holds)
     reads [q->pid] for every q under <pid_lock> ALONE, so that lock owns a
     read share of all 64 cells ([PidLock.nextpid_res_at]).  A quarter: the
     slot's own lock keeps a quarter ([proc_pub] below) and the travelling
     half stays where it was ([ProcDefs.proc_priv_bare], [ProcInv.proc_dormant]),
     so nothing above the two writers -- allocproc and freeproc, which hold all
     three -- had to move.  Over an EXPLICIT context, because the lock payload
     it lives in is λ-converted (PidLock.v). *)
  (* AT AN EXPLICIT VALUE, because the payload has to say what the scan
     read: <pid_lock> carries the 64 quarters as a LIST of values
     ([PidLock.nextpid_res_at]), and what allocproc's scan proves -- the
     candidate is in no slot -- is a fact about that list.  The pid
     REGISTER's domain fact is stated against it. *)
  Definition pid_lock_share_at (ξ : CtxIdDefs.CtxId) (pa : mword 64)
      (v : mword 32) : iProp Σ :=
    TsoCtx.ctx_word4_pointsto ξ (p_pid pa) (DfracOwn (1/4)) v.
  Definition pid_lock_share (pa : mword 64) (v : mword 32) : iProp Σ :=
    pid_lock_share_at CtxIdDefs.cur_ctx pa v.

  (* The lock-protected cells whose VALUES no protocol step needs to name:
     killed and xstate (mutable under p->lock, read by kill / wait), and the
     invariant's permanent QUARTER of the pid cell -- the travelling half
     rides with the running process in [ProcInv.proc_priv], the other quarter
     is <pid_lock>'s ([pid_lock_share] above), and all three agree for free by
     [ctx_word4_pointsto_agree].  Bundled EXISTENTIALLY so that growing the
     invariant by these three cells costs every existing caller one opaque
     conjunct instead of three new spec parameters. *)
  (* [p_xstate] IS HALF A CELL HERE.  The other half rides the process --
     [ProcInv.proc_priv_core] while it runs, [ProcDefs.proc_dormant] while
     the slot is parked -- because the ZOMBIE park's escrow is keyed at the
     status the cell holds ([ChildTok.exit_tok]) and a reaper that copies
     the status out must know that what it reads is what the escrow was
     built at.  Holding p->lock gives both halves, so the two agree by
     [ctx_word4_pointsto_agree]; the writers (kexit's [p->xstate = status],
     freeproc's [p->xstate = 0]) hold p->lock and therefore write the whole
     cell and re-split it. *)
  (* ...AND THE KILLED WORD IS PAID FOR (app-echo.md, lane KILL-PAY, K2).
     [p->killed] used to be a bare existential, so the invariant said
     NOTHING about a kill: any slot could be found killed at any moment and
     every consequence -- usertrap's [kexit(-1)], consoleread's -1, wait()'s
     -1 status, init reprinting its banner -- was unexplained.  The row
     below is the explanation: the flag is zero, OR the application's KILL
     CREDENTIAL has been paid ([RiscvPtsto.app_taint]).

     PERSISTENT, both arms, and that is what keeps the cost at one conjunct:
     every party that opens the lock may keep a copy and every re-bundle
     puts it straight back, so only the two WRITERS -- kkill's [p->killed =
     1] and setkilled's -- have anything to pay, and each takes the
     credential in its contract ([SpecKkill], [SpecSetkilled]).  The
     FOUNDERS ([BootCarveMain]'s carve, [ProofFreeproc]'s clear) found it at
     zero, which costs nothing.

     THE ZERO IS SPELLED AT THE CELL'S WIDTH: [p->killed] is an [int], so the
     word is [mword 32] and [RiscvLang.zero_reg] -- a 64-bit constant -- is
     not it. *)
  (* WHICH INCARNATION THIS PAYLOAD BELONGS TO (lane SELF-KILL, §1).
     Nothing here answered that until now, and the header above says why
     the generation is not in the block's reach: the private block is
     resident only on UNUSED/ZOMBIE ([proc_slots_at]), because sys_sbrk
     writes [myproc()->sz] with no lock held.  So a LIVE slot's lock
     payload knew the pid and nothing else -- and the killed row is about
     to be per-incarnation, which needs a name.

     THE TIE IS AN EIGHTH OF THE PID'S REGISTRATION ([SlotGen.pid_reg],
     carved out of the block's quarter by [SlotGen.pid_reg_eighths]).  It
     is the one resource in the tree that says "the CURRENT generation of
     this pid is [gn]" -- persistent readings cannot, since a pid is
     reused.  A party that holds a share of its own registration (every
     live process does, in its block) agrees with this one and learns that
     the row it just read is its own.

     GUARDED BY THE PID CELL, and that is what keeps the boot and the
     dormant arms out of it: an UNUSED slot's pid cell is 0 and 0 is
     registered to nothing ([SlotGen.pid_reg_dom]), so the carve costs the
     .bss nothing.  freeproc restores this arm at [p->pid = 0]. *)
  (* ...AND THE ROW IS PER-INCARNATION NOW, SO IT FOLDS INTO THE TIE (lane
     SELF-KILL, §4b'; owner's ruling of 2026-09-13).  The credential a kill
     costs is no longer a fact about the application but THE TARGET'S OWN
     EXIT PAYLOAD AT -1 ([ChildTok.kill_owed]), and a payload belongs to a
     generation -- so the row cannot be stated without the name the tie
     carries, and the two are one conjunct.

     THREE ARMS, AND THE THIRD IS WHY THE ROW IS LINEAR.  "The flag is
     zero" is the founders' arm.  [kill_owed gn] is what a killer deposits
     and what usertrap's exit path takes OUT, to pay [kexit(-1)] with.
     What it leaves in the row's place is [taken_at gn] -- "killed and
     spent" -- and that is what makes the take ONE-SHOT: the credential is
     gone, the marker is exclusive, and the process cannot forge either. *)
  (* ...AND THE FLAG IS MONOTONE, WHICH THE CELL CANNOT SAY (lane
     SELF-KILL, P6).  [p->killed] is set and never cleared while a process
     lives -- only freeproc zeroes it, and only on a slot whose process is
     already a ZOMBIE -- but this payload quantifies the cell
     EXISTENTIALLY, so "the flag was nonzero when I last looked" survives
     no release of the lock.  The party that READS the flag ([killed]) and
     the party that needs to know it ([kexit], whose C never reads it and
     which is two critical sections later) are therefore separated by a
     fact the cell cannot carry, and the take of the payment would be
     unprovable without one.
       So the ZERO ARM CARRIES [ChildTok.kill_pend gn] -- the incarnation's
     one-shot, minted PENDING with the generation -- and the other arms
     carry [ChildTok.kill_shot gn], which is PERSISTENT.  A writer of the
     flag fires the one-shot as it writes; from then on every opening of
     this row hands out a copy of the shot, [killed] relays it, and [kexit]
     spends it to refute the zero arm.  It is the ghost image of the C's
     own monotonicity, and it costs the writers nothing they do not already
     hold. *)
  (* ...AND THE PAID ARM IS AT A NONZERO FLAG (lane TRAP-ROWS, T2/T3).
     The one-shot fires exactly when a writer stores 1 ([kkill],
     [setkilled]); the only store of 0 is [freeproc]'s, on a DEAD slot,
     where [kill_paid]'s free arm applies and this row is gone.  So within
     a live incarnation the flag is MONOTONE, and saying so here is what
     lets a party holding the shot read the flag as nonzero
     ([kill_paid_shot_nz]) -- which is how usertrap's second killed check
     refutes its resume branch after a [setkilled], and how a console read
     that answered -1 by kill refutes it after the syscall. *)
  (* ...AND THE PAID ARM CARRIES THE KILLER'S CREDENTIAL (design/pipe.md,
     "The exit path", 2026-09-16).  A kill closes every descriptor of the
     victim, and a pipe descriptor's last close steps the pipe's exact
     ghost state -- a price the KILLER pays, and the only thing a killer can
     pay it with is the taint ([RiscvPtsto.app_taint]), since it
     cannot name the victim's table.  So the payment arm is the death
     payload AND the credential.  A process that kills ITSELF pays
     differently: its own trap deposit carries the closes of the table it
     holds, so the fault arm founds the row on the SPENT arm directly,
     with the incarnation's marker -- which is what a live process at a
     later killed check refutes with the marker still in its block
     ([kill_paid_shot_tear]). *)
  Definition kill_row (gn : gname) (kl : mword 32) : iProp Σ :=
    ((⌜kl = (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_pend gn)
     ∨ (⌜kl <> (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_shot gn ∗
        ((ChildTok.kill_owed gn ∗ app_taint) ∨ ChildTok.taken_at gn)))%I.

  (* WHOSE ROW IT IS, and the tie that says so: an eighth of the pid's
     registration ([SlotGen.pid_reg]), which is the one resource in the
     tree that answers "the CURRENT generation of this pid is [gn]".
     GUARDED BY THE PID CELL, and that is what keeps the boot and the
     dormant arms out of it: an UNUSED slot's pid cell is 0 and 0 is
     registered to nothing ([SlotGen.pid_reg_dom]), so the carve costs the
     .bss nothing.  freeproc restores this arm at [p->pid = 0]. *)
  (* THE FREE ARM CARRIES THE FLAG TOO, and it has to: allocproc re-keys
     this payload at a NEW pid, and to found the row there it must know the
     flag it is founding it at.  An UNUSED slot's is zero -- freeproc's
     [p->killed = 0] and the .bss both leave it so -- and saying so here is
     what lets allocproc hand the fresh incarnation a row. *)
  (* THE TWO ARMS ARE PURELY EXCLUSIVE, and that is what allocproc needs.
     It re-keys this payload at a NEW pid and must found the row there at
     the flag the slot already has -- so it has to READ that flag, and it
     can only do that if the arm it is not on is refutable.  The slot it
     is re-keying is UNUSED, whose pid cell is 0
     ([ProcInv.proc_dormant_nofd]); the second arm says the pid is not 0,
     so the first is the only one left and it is what allocproc reads. *)
  (* ...AND AN UNUSED SLOT'S FLAG IS ZERO, which is an invariant only
     because the KERNEL keeps it.  Upstream xv6's [kkill] compared
     [p->pid == pid] with no test at all, so [kill(0)] set [p->killed = 1]
     on the first UNUSED slot it walked -- whose pid cell is 0 -- and this
     arm would have been false.  The owner fixed it: [kkill] refuses pid 0
     (XV6_REV 64c58ba), so no writer can reach a free slot and allocproc
     may read the flag off the slot it is about to re-key. *)
  Definition kill_free (kl : mword 32) : iProp Σ :=
    (⌜kl = (mword_of_int 0 : mword 32)⌝)%I.

  Global Instance kill_free_persistent kl : Persistent (kill_free kl).
  Proof using . rewrite /kill_free. apply _. Qed.

  Lemma kill_free_zero : ⊢ kill_free (mword_of_int 0 : mword 32).
  Proof using . rewrite /kill_free. by iPureIntro. Qed.
  (* ...AND THE LIVE ARM PUBLISHES HOW A KILLER PAYS (lane SELF-KILL, 4b';
     the owner's ruling of 2026-09-13).  A [kill(2)] costs the TARGET's
     exit payload at -1, and the party that calls kill holds none of the
     target's resources -- it scans the proc table and lands on whatever
     slot the pid names.  So the row itself carries the price: the
     persistent reading of the incarnation's payload, and a persistent WAND
     from [RiscvPtsto.app_taint] to that payload at -1.

     AND [app_taint] IS NO LONGER A KILL CREDENTIAL.  It is the
     APPLICATION'S TAINT on the fixed record (echo instantiates it as
     [AppEcho.echo_taint]; [App.al_kill] is where the supply buys it),
     and after this lane it survives ONLY as the antecedent of this wand.
     Nothing else asks for it: no verified program produces it, no payload
     row carries a -1 wand ([UexecSlot.upay_neg] is gone), and the deposit
     at a killing cause is the process's OWN [ChildTok.kill_owed].  So a
     killer is necessarily a TAINTED process -- it runs on
     [UexecExecInst.xv6_ssupply], which buys the taint from the
     application's supply -- and what it buys with it is exactly the
     target's [Q (-1)].

     WHY THE ANTECEDENT IS THE AMBIENT AND NOT [AppInv.app_sup].  The row is
     FOUNDED at allocproc out of the CREATOR's promise, and for a forked
     child the creator is the forking PROCESS -- so the promise travels down
     the fork deposit, through [UexecRet.uexec_fork_child_F], whose section
     is [{!riscvGS} {!ufdG} {!ctokG}] and nothing else.  Naming [app_sup]
     there would force [fileG] on 76 more files -- the whole U tier, every
     verified program -- which is exactly what lane SUPPLY-SPLIT exists to
     prevent.  [app_taint] lives at [RiscvPtsto]'s altitude and both
     ends can name it; [UexecSlot.upay_neg] was stated against it for the
     same reason.

     FOUNDED ONCE, AT ALLOCPROC, out of [SpecAllocproc]'s
     [□ (app_taint -∗ Q (-1))] premise: <init>'s payload is trivial
     and kfork's comes from the forking process, whose payload admits the
     taint on its taint arm.  Both conjuncts are PERSISTENT, so re-bundling
     the lock's payload costs nothing and the row stays linear only in
     [kill_row]. *)
  Definition kill_paid (pid : mword 32) (kl : mword 32) : iProp Σ :=
    ((⌜bv_unsigned pid = 0⌝ ∗ kill_free kl)
     ∨ (⌜bv_unsigned pid <> 0⌝ ∗
        ∃ (gn : gname) (Q : Z -> iProp Σ),
          pid_reg pid (DfracOwn qeighth) gn ∗
          ChildTok.my_pay gn Q ∗ □ (app_taint -∗ Q (-1)) ∗
          kill_row gn kl))%I.

  Definition proc_pub (pa : mword 64) : iProp Σ :=
    (∃ (kl xs pid : mword 32),
       p_killed pa ↦₄ kl ∗ p_xstate pa ↦₄{DfracOwn (1/2)} xs ∗
       p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
       kill_paid pid kl)%I.

  (* the row's three arms *)
  Lemma kill_row_zero (gn : gname) :
    ChildTok.kill_pend gn -∗ kill_row gn (mword_of_int 0 : mword 32).
  Proof using .
    rewrite /kill_row. iIntros "H". iLeft. iFrame "H". done.
  Qed.

  Lemma kill_row_of_owed (gn : gname) (kl : mword 32) :
    kl <> (mword_of_int 0 : mword 32) ->
    ChildTok.kill_shot gn -∗ app_taint -∗ ChildTok.kill_owed gn -∗
    kill_row gn kl.
  Proof using .
    intro Hnz. rewrite /kill_row. iIntros "#Hs #Hc H". iRight.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ iExact "Hs" | ]. iLeft.
    iFrame "H". iExact "Hc".
  Qed.

  Lemma kill_row_of_taken (gn : gname) (kl : mword 32) :
    kl <> (mword_of_int 0 : mword 32) ->
    ChildTok.kill_shot gn -∗ ChildTok.taken_at gn -∗ kill_row gn kl.
  Proof using .
    intro Hnz. rewrite /kill_row. iIntros "#Hs H". iRight.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ iExact "Hs" | ]. iRight. iExact "H".
  Qed.

  (* ...AND THE READING THE MONOTONE FLAG BUYS: the shot says the flag is
     nonzero, which is the converse of [kill_row_shot]. *)
  Lemma kill_row_shot_nz (gn : gname) (kl : mword 32) :
    kill_row gn kl -∗ ChildTok.kill_shot gn -∗
    kill_row gn kl ∗ ⌜kl <> (mword_of_int 0 : mword 32)⌝.
  Proof using .
    rewrite /kill_row. iIntros "[[_ Hp] | Hr] #Hs".
    - iDestruct (ChildTok.kill_pend_shot with "Hp Hs") as %[].
    - iDestruct "Hr" as "[%Hnz Hr]". iSplitR ""; [ | by iPureIntro ].
      iRight. iSplitR; [ by iPureIntro | ]. iExact "Hr".
  Qed.

  (* ...AND WHAT A NONZERO FLAG SAYS, relayed: the one-shot has been fired.
     This is what [killed()] hands its caller beside the value, and it is
     PERSISTENT, which is the whole reason the one-shot exists -- the row
     goes back untouched and the fact outlives the critical section. *)
  Lemma kill_row_shot (gn : gname) (kl : mword 32) :
    kl <> (mword_of_int 0 : mword 32) ->
    kill_row gn kl -∗ ChildTok.kill_shot gn ∗ kill_row gn kl.
  Proof using .
    intro Hnz. rewrite /kill_row.
    iIntros "[[%Hz _] | [_ [#Hs H]]]"; [ exfalso; exact (Hnz Hz) | ].
    iSplitR; [ iExact "Hs" | ]. iRight. iFrame "Hs H". by iPureIntro.
  Qed.

  (* ...AND WHAT A WRITER DOES BEFORE IT STORES: fire the one-shot.  At the
     zero arm the token is right there; at either other arm the shot half
     is already in the row and persistent, so this is a duplication.  The
     row's OLD content is dropped -- a second kill of an already-killed
     process says nothing new and costs the same. *)
  Lemma kill_row_fire (gn : gname) (kl : mword 32) :
    kill_row gn kl ==∗ ChildTok.kill_shot gn.
  Proof using .
    rewrite /kill_row. iIntros "[[_ Hp] | [_ [#Hs _]]]".
    - iApply (ChildTok.kill_pend_fire with "Hp").
    - iModIntro. iExact "Hs".
  Qed.

  (* THE TAKE, and it is [kexit]'s (lane SELF-KILL, P6).  Three things go
     in: the SHOT (which refutes the zero arm -- the fact the C's own
     monotonicity gives and the cell does not), the caller's OWN marker
     (which refutes the spent arm, because the marker is exclusive and
     lives in the dying process's block), and the row.  What comes out is
     the death payment and a row closed on the spent arm.  ONE-SHOT by
     construction: the marker is gone from the block and into the row, and
     no second one exists. *)
  Lemma kill_row_take (gn : gname) (kl : mword 32) :
    ChildTok.kill_shot gn -∗ ChildTok.taken_at gn -∗ kill_row gn kl -∗
    ChildTok.kill_owed gn ∗ kill_row gn kl.
  Proof using .
    iIntros "#Hs Ht Hrow". rewrite /kill_row.
    iDestruct "Hrow" as "[[_ Hp] | [%Hnz [_ [[Ho _] | Ht2]]]]".
    - iDestruct (ChildTok.kill_pend_shot with "Hp Hs") as %[].
    - iSplitL "Ho"; [ iExact "Ho" | ].
      iRight. iSplitR; [ by iPureIntro | ].
      iSplitR; [ iExact "Hs" | ]. iRight. iExact "Ht".
    - iDestruct (ChildTok.taken_at_excl with "Ht Ht2") as %[].
  Qed.

  (* ...and the tie's two.  An unused slot's cell is 0 and costs nothing; a
     live slot's is the eighth allocproc carved when it registered the
     pid. *)
  Lemma kill_paid_zero (pid : mword 32) (kl : mword 32) :
    bv_unsigned pid = 0 -> kl = (mword_of_int 0 : mword 32) ->
    ⊢ kill_paid pid kl.
  Proof using .
    intros H Hk. rewrite /kill_paid. iLeft.
    iSplitR; [ iPureIntro; exact H | ]. rewrite Hk. iApply kill_free_zero.
  Qed.

  Lemma kill_paid_of_reg (pid : mword 32) (kl : mword 32) (gn : gname)
      (Q : Z -> iProp Σ) :
    bv_unsigned pid <> 0 ->
    pid_reg pid (DfracOwn qeighth) gn -∗ ChildTok.my_pay gn Q -∗
    □ (app_taint -∗ Q (-1)) -∗ kill_row gn kl -∗ kill_paid pid kl.
  Proof using .
    intro Hnz. rewrite /kill_paid. iIntros "Hr #Hmy #Hw Hk". iRight.
    iSplitR; [ iPureIntro; exact Hnz | ]. iExists gn, Q.
    iSplitL "Hr"; [ iExact "Hr" | ].
    iSplitR; [ iExact "Hmy" | ].
    iSplitR; [ iModIntro; iExact "Hw" | ].
    iExact "Hk".
  Qed.

  (* ...AND WHAT THE PUBLICATION IS FOR: a party that holds the
     application's supply may re-close this payload at ANY flag, because
     the wand buys the target's payload at -1 and [kill_row]'s paid arm is
     exactly that payload.  This is [kkill]'s / [setkilled]'s / [sys_kill]'s
     whole payment: they hold p->lock, write the flag, and rebuild the row
     through this.  Whatever the row held before is DROPPED -- a second
     kill of an already-killed process costs the same and says nothing
     new. *)
  (* THE SIDE CONDITION IS THE C's OWN GUARD: [kkill] refuses pid 0 (XV6_REV
     64c58ba) and [setkilled] runs on a RUNNING process, so no writer ever
     lands on a slot whose pid cell is 0 -- which is what keeps the free
     arm's [⌜kl = 0⌝] an invariant and lets allocproc read the flag off the
     slot it re-keys. *)
  (* ...AND IT IS A BASIC UPDATE NOW, because the writer also FIRES the
     incarnation's one-shot ([kill_row_fire]) -- the ghost half of the
     store it is about to make. *)
  Lemma kill_paid_kill (pid : mword 32) (kl kl' : mword 32) :
    bv_unsigned pid <> 0 ->
    ⌜kl' <> (mword_of_int 0 : mword 32)⌝ -∗
    app_taint -∗ kill_paid pid kl ==∗ kill_paid pid kl'.
  Proof using .
    intro Hpnz. rewrite /kill_paid.
    iIntros "%Hknz #Hsup [[%Hz _] | [%Hnz Hr]]".
    - exfalso. exact (Hpnz Hz).
    - iDestruct "Hr" as (gn Q) "(Hr & #Hmy & #Hw & Hrow)".
      iMod (kill_row_fire with "Hrow") as "#Hs". iModIntro.
      iRight. iSplitR; [ iPureIntro; exact Hnz | ].
      iExists gn, Q.
      iSplitL "Hr"; [ iExact "Hr" | ].
      iSplitR; [ iExact "Hmy" | ].
      iSplitR; [ iModIntro; iExact "Hw" | ].
      iApply (kill_row_of_owed _ _ Hknz with "Hs Hsup").
      iApply (ChildTok.kill_owed_of with "Hmy"). iApply "Hw". iExact "Hsup".
  Qed.

  (* ...AND THE SAME STEP FOR A WRITER THAT PAYS OUT OF ITS OWN POCKET
     (lane SELF-KILL, P6).  [setkilled]'s only caller is usertrap's fault
     arm on [myproc()], and a process that faults ON PURPOSE deposits its
     OWN [Q (-1)] rather than buying the target's with the application's
     taint -- which is the whole point of the lane, and why the deposit the
     trap route carries is two-sided ([UexecRet.ukill_cred_at]).  The
     caller's registration eighth is what says the row it is closing is the
     row of the generation whose payment it holds. *)
  Lemma kill_paid_kill_owed (pid : mword 32) (kl kl' : mword 32) (dq : dfrac)
      (gn : gname) :
    bv_unsigned pid <> 0 ->
    ⌜kl' <> (mword_of_int 0 : mword 32)⌝ -∗
    pid_reg pid dq gn -∗ app_taint -∗ ChildTok.kill_owed gn -∗
    kill_paid pid kl ==∗
    pid_reg pid dq gn ∗ kill_paid pid kl'.
  Proof using .
    intro Hpnz. rewrite /kill_paid.
    iIntros "%Hknz Hmine #Hsup Howed [[%Hz _] | [%Hnz Hr]]".
    - exfalso. exact (Hpnz Hz).
    - iDestruct "Hr" as (gn' Q) "(Hr & #Hmy & #Hw & Hrow)".
      iDestruct (pid_reg_agree pid pid dq (DfracOwn qeighth) gn gn' eq_refl
                   with "Hmine Hr") as %->.
      iMod (kill_row_fire with "Hrow") as "#Hs". iModIntro.
      iFrame "Hmine". iRight. iSplitR; [ iPureIntro; exact Hnz | ].
      iExists gn', Q.
      iSplitL "Hr"; [ iExact "Hr" | ].
      iSplitR; [ iExact "Hmy" | ].
      iSplitR; [ iModIntro; iExact "Hw" | ].
      iApply (kill_row_of_owed _ _ Hknz with "Hs Hsup Howed").
  Qed.

  (* ...AND THE TWO SIDES AS ONE STEP, which is what a writer that may be
     EITHER party takes (lane SELF-KILL, P6b; [SpecSetkilled]).  setkilled
     runs only on [myproc()], so the process it kills may be paying for its
     own death ([ChildTok.kill_owed], the right side) or being killed by an
     application that holds the taint (the left) -- and the row is closed
     the same way either way.  The registration eighth is what names the
     generation the right side's payment is keyed at, and it is what lets
     the step hand the ONE-SHOT back: after this write the flag is monotone
     for this incarnation, and [ChildTok.kill_shot] is that fact. *)
  Lemma kill_paid_kill_two (pid : mword 32) (kl kl' : mword 32) (dq : dfrac)
      (gn : gname) (self : bool) :
    bv_unsigned pid <> 0 ->
    ⌜kl' <> (mword_of_int 0 : mword 32)⌝ -∗
    pid_reg pid dq gn -∗
    (* the taint, or the process's OWN death payload beside the
       incarnation's marker (design/pipe.md, "The exit path"): a self-kill
       founds the row on the SPENT arm, keeps its payload in hand for the
       kexit two critical sections later, and gets it back below.  KEYED
       on the party, so the caller knows which side comes back. *)
    (if self then ChildTok.kill_owed gn ∗ ChildTok.taken_at gn
     else app_taint) -∗
    kill_paid pid kl ==∗
    pid_reg pid dq gn ∗ ChildTok.kill_shot gn ∗ kill_paid pid kl' ∗
    (if self then ChildTok.kill_owed gn else app_taint).
  Proof using .
    intro Hpnz. rewrite /kill_paid.
    iIntros "%Hknz Hmine Hpay [[%Hz _] | [%Hnz Hr]]".
    - exfalso. exact (Hpnz Hz).
    - iDestruct "Hr" as (gn' Q) "(Hr & #Hmy & #Hw & Hrow)".
      iDestruct (pid_reg_agree pid pid dq (DfracOwn qeighth) gn gn' eq_refl
                   with "Hmine Hr") as %->.
      iMod (kill_row_fire with "Hrow") as "#Hs".
      iModIntro. iFrame "Hmine". iSplitL ""; [ iExact "Hs" | ].
      destruct self.
      + (* the process's own: the marker goes in, the payload comes back *)
        iDestruct "Hpay" as "[Howed Ht]".
        iSplitR "Howed"; [ | iExact "Howed" ].
        iRight. iSplitR; [ iPureIntro; exact Hnz | ].
        iExists gn', Q.
        iSplitL "Hr"; [ iExact "Hr" | ].
        iSplitR; [ iExact "Hmy" | ].
        iSplitR; [ iModIntro; iExact "Hw" | ].
        iApply (kill_row_of_taken _ _ Hknz with "Hs Ht").
      + (* the killer's credential buys the payload through the row's wand *)
        iDestruct "Hpay" as "#Hc".
        iSplitL "Hr"; [ | iExact "Hc" ].
        iRight. iSplitR; [ iPureIntro; exact Hnz | ].
        iExists gn', Q.
        iSplitL "Hr"; [ iExact "Hr" | ].
        iSplitR; [ iExact "Hmy" | ].
        iSplitR; [ iModIntro; iExact "Hw" | ].
        iApply (kill_row_of_owed _ _ Hknz with "Hs Hc").
        iApply (ChildTok.kill_owed_of with "Hmy"). iApply "Hw". iExact "Hc".
  Qed.

  (* ...AND WHAT AN UNUSED SLOT'S PAYLOAD SAYS ABOUT THE FLAG: either it
     is zero, or a killer with the application's supply set it while the
     slot was free.  allocproc reads this off the slot it is about to
     re-key and founds the new incarnation's row on whichever side it
     lands. *)
  Lemma kill_paid_flag (pid : mword 32) (kl : mword 32) :
    bv_unsigned pid = 0 -> kill_paid pid kl -∗ kill_free kl.
  Proof using .
    intro Hz. rewrite /kill_paid.
    iIntros "[[_ Hf] | [%Hnz _]]"; [ iExact "Hf" | exfalso; exact (Hnz Hz) ].
  Qed.

  (* ...AND WHAT A PARTY HOLDING A SHARE OF ITS OWN REGISTRATION READS OFF
     IT: the row is at ITS generation.  Its share comes back -- the
     agreement is pure -- and the nonzero side condition is what the
     caller's own registration already gives ([SlotGen.pid_reg_dom]). *)
  Lemma kill_paid_agree (pid : mword 32) (kl : mword 32) (dq : dfrac)
      (gn : gname) :
    kill_paid pid kl -∗ pid_reg pid dq gn -∗
    ((⌜bv_unsigned pid = 0⌝ ∗ kill_free kl)
     ∨ (⌜bv_unsigned pid <> 0⌝ ∗
        ∃ Q : Z -> iProp Σ,
          pid_reg pid (DfracOwn qeighth) gn ∗ ChildTok.my_pay gn Q ∗
          □ (app_taint -∗ Q (-1)) ∗ kill_row gn kl)) ∗
    pid_reg pid dq gn.
  Proof using .
    rewrite /kill_paid. iIntros "[[%Hz #Hf] | [%Hnz Hr]] Hmine".
    - iFrame "Hmine". iLeft. iSplitR; [ iPureIntro; exact Hz | ].
      iExact "Hf".
    - iDestruct "Hr" as (gn' Q) "(Hr & #Hmy & #Hw & Hk)".
      iDestruct (pid_reg_agree pid pid dq (DfracOwn qeighth) gn gn' eq_refl
                   with "Hmine Hr") as %Heq.
      iFrame "Hmine". iRight. iSplitR; [ iPureIntro; exact Hnz | ].
      rewrite Heq. iExists Q.
      iSplitL "Hr"; [ iExact "Hr" | ].
      iSplitR; [ iExact "Hmy" | ].
      iSplitR; [ iModIntro; iExact "Hw" | ].
      iExact "Hk".
  Qed.

  (* WHAT [killed()] READS OUT BESIDE THE VALUE (lane SELF-KILL, P6; the
     owner's ruling that killed() reports the FLAG and nothing else).  The
     row is LINEAR and per-incarnation, so a reader can neither copy it out
     nor relay it -- but the incarnation's ONE-SHOT is persistent, and at a
     nonzero flag the row is carrying it.  So the answer is the number and,
     when the number is nonzero, the fact that the number will stay
     nonzero: exactly what [kexit] needs two critical sections later, and
     nothing else.
       THE CALLER'S REGISTRATION IS WHAT TIES IT to a generation the caller
     can name: [killed()] is called on a proc pointer and the row's
     generation is existential, so the eighth the caller's own block
     carries ([SlotGen.gen_halves_at]) is what makes the answer usable.  It
     is pure agreement, so the share comes straight back.
       THE FREE ARM IS AN ANSWER TOO: nothing in killed()'s contract says
     the slot is live, and an UNUSED slot's flag is zero. *)
  Lemma kill_paid_shot (pid kl : mword 32) (dq : dfrac) (gn : gname) :
    kill_paid pid kl -∗ pid_reg pid dq gn -∗
    kill_paid pid kl ∗ pid_reg pid dq gn ∗
    (⌜kl = (mword_of_int 0 : mword 32)⌝ ∨ ChildTok.kill_shot gn).
  Proof using .
    iIntros "Hkp Hmine".
    iDestruct (kill_paid_agree pid kl dq gn with "Hkp Hmine")
      as "[Harm Hmine]".
    iDestruct "Harm" as "[[%Hz #Hf] | [%Hnz Hlive]]".
    - rewrite /kill_free. iDestruct "Hf" as %Hkz.
      iFrame "Hmine". iSplitL.
      + iApply (kill_paid_zero pid kl Hz Hkz).
      + iLeft. iPureIntro; exact Hkz.
    - iDestruct "Hlive" as (Q) "(Hr & #Hmy & #Hw & Hrow)".
      destruct (decide (kl = (mword_of_int 0 : mword 32))) as [-> | Hne].
      + iFrame "Hmine". iSplitL "Hr Hrow"; [ | iLeft; done ].
        iApply (kill_paid_of_reg pid _ gn Q Hnz with "Hr Hmy Hw Hrow").
      + iDestruct (kill_row_shot gn kl Hne with "Hrow") as "[#Hs Hrow]".
        iFrame "Hmine". iSplitL "Hr Hrow".
        * iApply (kill_paid_of_reg pid kl gn Q Hnz with "Hr Hmy Hw Hrow").
        * iRight. iExact "Hs".
  Qed.

  (* ...AND THE READING A KILLED CHECK THAT WILL TEAR THE PROCESS DOWN
     NEEDS (design/pipe.md, "The exit path"): the taint, out of the paid
     arm.  The caller lends the incarnation's marker, which is what refutes
     the SPENT arm -- a row a self-kill founded is spent, and the process
     that founded it never traps again, so a live trap's own marker is the
     proof that the row it reads was paid by a third party. *)
  Lemma kill_paid_shot_tear (pid kl : mword 32) (dq : dfrac) (gn : gname) :
    kill_paid pid kl -∗ pid_reg pid dq gn -∗ ChildTok.taken_at gn -∗
    kill_paid pid kl ∗ pid_reg pid dq gn ∗ ChildTok.taken_at gn ∗
    (⌜kl = (mword_of_int 0 : mword 32)⌝
     ∨ (ChildTok.kill_shot gn ∗ app_taint)).
  Proof using .
    iIntros "Hkp Hmine Ht".
    iDestruct (kill_paid_agree pid kl dq gn with "Hkp Hmine")
      as "[Harm Hmine]".
    iDestruct "Harm" as "[[%Hz #Hf] | [%Hnz Hlive]]".
    - rewrite /kill_free. iDestruct "Hf" as %Hkz.
      iFrame "Hmine Ht". iSplitL.
      + iApply (kill_paid_zero pid kl Hz Hkz).
      + iLeft. iPureIntro; exact Hkz.
    - iDestruct "Hlive" as (Q) "(Hr & #Hmy & #Hw & Hrow)".
      rewrite /kill_row.
      iDestruct "Hrow" as "[[%Hk Hp] | [%Hkn [#Hs [[Ho #Hc] | Ht2]]]]".
      + iFrame "Hmine Ht". iSplitL.
        * iApply (kill_paid_of_reg pid kl gn Q Hnz with "Hr Hmy Hw").
          rewrite /kill_row. iLeft. iFrame "Hp". by iPureIntro.
        * iLeft. by iPureIntro.
      + iFrame "Hmine Ht". iSplitL.
        * iApply (kill_paid_of_reg pid kl gn Q Hnz with "Hr Hmy Hw").
          rewrite /kill_row. iRight. iSplitR; [ by iPureIntro | ].
          iSplitR; [ iExact "Hs" | ]. iLeft. iFrame "Ho". iExact "Hc".
        * iRight. iSplitR; [ iExact "Hs" | ]. iExact "Hc".
      + iDestruct (ChildTok.taken_at_excl with "Ht Ht2") as %[].
  Qed.

  (* ...AND THE CONVERSE, WHICH IS WHAT A KILLED CHECK NEEDS (lane
     TRAP-ROWS, T2/T3).  A party that already HOLDS the incarnation's
     one-shot -- because [setkilled] fired it, or because a call it made
     relayed it -- reads [p->killed] as NONZERO: within a live incarnation
     the flag is monotone and the row's paid arm says so.  This is what
     refutes usertrap's second killed check on the paths where the process
     is provably dead, and it is the only place that fact can be read: the
     row is linear and lives under <p->lock>.
     THE NONZERO PID IS A PREMISE and not a reading -- [kill_paid]'s free
     arm is a slot no one holds, and what rules it out is the caller's own
     block ([SlotGen.gen_halves_priv_nz]). *)
  Lemma kill_paid_shot_nz (pid kl : mword 32) (dq : dfrac) (gn : gname) :
    bv_unsigned pid <> 0 ->
    kill_paid pid kl -∗ pid_reg pid dq gn -∗ ChildTok.kill_shot gn -∗
    kill_paid pid kl ∗ pid_reg pid dq gn ∗
    ⌜kl <> (mword_of_int 0 : mword 32)⌝.
  Proof using .
    intro Hnz. iIntros "Hkp Hmine #Hs".
    iDestruct (kill_paid_agree pid kl dq gn with "Hkp Hmine")
      as "[Harm Hmine]".
    iDestruct "Harm" as "[[%Hz _] | [_ Hlive]]"; [ exfalso; exact (Hnz Hz) | ].
    iDestruct "Hlive" as (Q) "(Hr & #Hmy & #Hw & Hrow)".
    iDestruct (kill_row_shot_nz gn kl with "Hrow Hs") as "[Hrow %Hknz]".
    iFrame "Hmine". iSplitL; [ | by iPureIntro ].
    iApply (kill_paid_of_reg pid kl gn Q Hnz with "Hr Hmy Hw Hrow").
  Qed.

  (* THE TAKE, AND IT IS [kexit]'s ALONE (lane SELF-KILL, P6).  A dying
     process holding the SHOT (relayed by the [killed()] its trap loop
     called) and its own MARKER (out of its private block) exchanges the
     marker for the death payment the killer deposited.  Everything the
     step needs to refute is refuted: the shot kills the zero arm, the
     marker kills the spent arm.  See [kill_row_take].
     THE SIDE CONDITION is the caller's own block's ([SlotGen.gen_halves_at]):
     a live process's pid is not 0, which is what rules out the free arm. *)
  Lemma kill_paid_take (pid kl : mword 32) (dq : dfrac) (gn : gname) :
    bv_unsigned pid <> 0 ->
    ChildTok.kill_shot gn -∗ ChildTok.taken_at gn -∗
    pid_reg pid dq gn -∗ kill_paid pid kl -∗
    ChildTok.kill_owed gn ∗ pid_reg pid dq gn ∗ kill_paid pid kl.
  Proof using .
    intro Hpnz. iIntros "#Hs Ht Hmine Hkp".
    iDestruct (kill_paid_agree pid kl dq gn with "Hkp Hmine")
      as "[Harm Hmine]".
    iDestruct "Harm" as "[[%Hz _] | [%Hnz Hlive]]".
    - exfalso. exact (Hpnz Hz).
    - iDestruct "Hlive" as (Q) "(Hr & #Hmy & #Hw & Hrow)".
      iDestruct (kill_row_take gn kl with "Hs Ht Hrow") as "[Howed Hrow]".
      iFrame "Howed Hmine".
      iApply (kill_paid_of_reg pid kl gn Q Hnz with "Hr Hmy Hw Hrow").
  Qed.

  (* THE SLOT'S GENERATION IS NOT HERE.  A generation is a SAVED PREDICATE
     carrying the slot, the pid and the process's exit payload
     ([ChildTok.v]), and it is named by the PRIVATE BLOCK
     ([ProcDefs.pv_gen]) rather than by this payload -- because the parties
     that read it (the child's slot, the parent's token, the exit escrow)
     hold the block or a piece of the generation, and never p->lock.  So
     this payload is the three cells whose values no protocol step
     names. *)


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
  Proof using . intros Hd. rewrite /park_pay Hd. auto. Qed.

  Lemma park_pay_needs_ctx (pa : mword 64) (st : mword 32) :
    needs_ctx st = true -> ⊢ park_pay pa st.
  Proof using . intros Hn. exact (park_pay_live pa st (inv_dormant_of_needs_ctx st Hn)). Qed.

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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (γs : list gname).

  (* A6.128: THE PAYLOAD IS A FUNCTION OF THE CONTEXT [ξ] -- the identity of
     the thread that holds it, moved across the swtch crossing by
     [TsoCtx.ctx_move] ([p_sched_morph] below).  The ambient forms the
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

  (* THE PAYLOAD TRANSPORTS, one [CtxMorph] instance per named piece:
     CtxMorphTac's leaf dispatch is syntactic, so a named piece is resolved
     by instance search rather than unfolded by [apply].  Only the pieces
     the crossing payload needs BEFORE the slot pile below are stated here;
     the rest come from that pile, from [ProcPtOwn] ([proc_pt*]), from
     [ProcDefs] ([proc_dormant*]) and from [WpLock] ([lk_floor]). *)
  Global Instance locked_morph γ i :
    CtxMorph (λ ξ, WpLock.locked (XI := ξ) γ i).
  Proof using .
    rewrite /WpLock.locked /WpLock.locked_core /WpLock.lock_ctx_held.
    ctx_morph_solve.
  Qed.
  (* [proc_pub] is unfolded rather than taken by instance: its own instance
     stands with the slot pile further down, below this one. *)
  Global Instance proc_held_morph i j γl st ch :
    CtxMorph (λ ξ, proc_held (XI := ξ) i j γl st ch).
  Proof using . rewrite /proc_held /proc_pub. ctx_morph_solve. Qed.
  (* the dormant block is taken BY NAME: left to instance search, the leaf
     tries every later-declared instance against the block's body up to δ
     before reaching [ProcDefs.proc_dormant_noctx_morph] -- measured as a
     hang, not a slow step *)
  Global Instance park_pay_morph pa st :
    CtxMorph (λ ξ, park_pay (XI := ξ) pa st).
  Proof using .
    rewrite /park_pay. apply ctx_morph_if_then.
    apply ProcDefs.proc_dormant_noctx_morph.
  Qed.
  Global Instance is_lock_morph γ lk s R : CtxMorph (λ ξ, is_lock (XI := ξ) γ lk s R).
  Proof using . rewrite /is_lock. ctx_morph_solve. Qed.
  (* A6.139: the handler ENVIRONMENT re-homes across a domination by the
     witness packed beside it in [intr_res]; everything else in the bundle
     is context-free.  These two instances are what lets the payload rows
     stay pinned at the box's own ξ.  The transport class names no hart --
     the bundle's hart [CIDh] is a parameter of the payload. *)
  Global Instance intr_res_morph (kt : ktier) (CIDh : CpuId) :
    CtxMorph (λ ξ, intr_res (XI := ξ) (CID := CIDh) kt).
  Proof using .
    iIntros (ξ ξ') "Hd Hres".
    iEval (rewrite /intr_res) in "Hres".
    iDestruct "Hres" as (E) "(Hat & #HE & #Hmv)".
    iMod ("Hmv" $! ξ ξ' with "Hd HE") as "(Hd & #HE')".
    iModIntro. iFrame "Hd".
    iEval (rewrite /intr_res). iExists E. iFrame "Hat HE' Hmv".
  Qed.

  Global Instance trap_csrs_morph (kt : ktier) (CIDh : CpuId) :
    CtxMorph (λ ξ, trap_csrs (XI := ξ) (CID := CIDh) kt).
  Proof using . rewrite /trap_csrs. ctx_morph_solve. Qed.

  Global Instance p_sched_morph h A' c cret tpv p back :
    CtxMorph (λ ξ, p_sched h A' c cret tpv p back ξ).
  Proof using .
    rewrite /p_sched. ctx_morph_solve.
    all: apply (trap_csrs_morph KT1 h).
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using . vm_compute. reflexivity. Qed.

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
  (* THE MIGRATABLE RECORD'S TOKEN IS BESIDE IT, PARKED UNDER THE SLOT'S
     CONTEXT (A6.127 §6; claude-notes/projects/ctx-parent.md).  The record
     at its own identity [XIp] under the later it always arrives beneath;
     its token OUTSIDE the later, parked under the slot's context [ξl]
     ([TsoCtx.ctx_parked XIp ξl]) -- the ONLY context dependence of the
     slot, which is what makes [proc_lock_pay] a genuine λ-payload
     ([TsoCtx.ctx_parked_morph] transports the token; nothing else moves).
     The ambient form [proc_ctx] is the slot at the holder's own context:
     what a park hands the scheduler ([proc_ctx_of_tok]) and what a
     dispatch resumes ([proc_ctx_resume_tok]). *)
  Definition proc_ctx_at (ξl : CtxId) (pa : mword 64) : iProp Σ :=
    (∃ XIp : CtxId,
       ctx_parked XIp ξl ∗
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
     name, the invariant and a floor; a floor's dirty arm crosses by
     [TsoCtx.ctx_dom_wrote_floor]). *)
  Global Instance ctx_cells_morph c vs : CtxMorph (λ ξ, ctx_cells (XI := ξ) c vs).
  Proof using . rewrite /ctx_cells. apply ctx_cells_at_morph. Qed.
  Global Instance own_ctx_morph pa : CtxMorph (λ ξ, own_ctx (XI := ξ) pa).
  Proof using . rewrite /own_ctx. ctx_morph_solve. Qed.
  Global Instance run_slot_at_morph pa : CtxMorph (λ ξ, run_slot_at ξ pa).
  Proof using . rewrite /run_slot_at. ctx_morph_solve. Qed.



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
          and a ghost_var_frac does not move on half alone.  Half #2 is here too
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

  (* A6.129: THE TRANSPORT IS REAL NOW -- one [CtxMorph] instance per
     named piece (the pieces of a dormant slot down to its page table;
     [PtTreeMorph] carries the tree). *)
  Global Instance pname_cells_morph pa dq bs : CtxMorph (λ ξ, pname_cells (XI := ξ) pa dq bs).
  Proof using . rewrite /pname_cells. ctx_morph_solve. Qed.
  Global Instance proc_fields_morph pa dq V : CtxMorph (λ ξ, proc_fields (XI := ξ) pa dq V).
  Proof using . rewrite /proc_fields. ctx_morph_solve. Qed.
  Global Instance ofile_cells_morph pa fs : CtxMorph (λ ξ, ofile_cells (XI := ξ) pa fs).
  Proof using . rewrite /ofile_cells. ctx_morph_solve. Qed.
  Global Instance tf_words_morph tfp ws : CtxMorph (λ ξ, tf_words (XI := ξ) tfp ws).
  Proof using . rewrite /tf_words. ctx_morph_solve. Qed.
  Global Instance tf_tail_morph tfp : CtxMorph (λ ξ, tf_tail (XI := ξ) tfp).
  Proof using . rewrite /tf_tail. ctx_morph_solve. Qed.
  Global Instance tf_page_morph tfp ws : CtxMorph (λ ξ, tf_page (XI := ξ) tfp ws).
  Proof using . rewrite /tf_page. ctx_morph_solve. Qed.
  Global Instance is_kstack_morph pa ks : CtxMorph (λ ξ, is_kstack (XI := ξ) pa ks).
  Proof using . rewrite /is_kstack. ctx_morph_solve. Qed.
  Global Instance kstack_free_morph pa : CtxMorph (λ ξ, kstack_free (XI := ξ) pa).
  Proof using . rewrite /kstack_free. ctx_morph_solve. Qed.
  Global Instance phys_byte_any_morph a : CtxMorph (λ ξ, phys_byte_any (XI := ξ) a).
  Proof using . rewrite /phys_byte_any. ctx_morph_solve. Qed.
  Global Instance phys_page_own_morph ppn : CtxMorph (λ ξ, phys_page_own (XI := ξ) ppn).
  Proof using . rewrite /phys_page_own. ctx_morph_solve. Qed.
  Global Instance upt_pages_own_morph um : CtxMorph (λ ξ, upt_pages_own (XI := ξ) um).
  Proof using . rewrite /upt_pages_own. ctx_morph_solve. Qed.
  Global Instance proc_pt_own_morph P : CtxMorph (λ ξ, proc_pt_own (XI := ξ) P).
  Proof using . rewrite /proc_pt_own. ctx_morph_solve. Qed.
  (* [proc_pt]'s morphs are ProcPtOwn's (main keys the image by [M]);
     [proc_dormant*] morphs are ProcDefs'; [own_ctx]/cell towers are
     SwtchCtx's -- all imported, none restated here. *)
  Global Instance proc_pub_morph pa : CtxMorph (λ ξ, proc_pub (XI := ξ) pa).
  Proof using . rewrite /proc_pub. ctx_morph_solve. Qed.

  Global Instance proc_ctx_at_morph pa : CtxMorph (λ ξ, proc_ctx_at ξ pa).
  Proof using .
    rewrite /proc_ctx_at. apply ctx_morph_exist; intros XIp.
    apply ctx_morph_sep; [apply ctx_parked_morph | apply ctx_morph_const].
  Qed.
  Global Instance proc_slots_at_morph pa st : CtxMorph (λ ξ, proc_slots_at ξ pa st).
  Proof using . rewrite /proc_slots_at. ctx_morph_solve. Qed.
  Global Instance proc_lock_res_at_morph γl pa : CtxMorph (λ ξ, proc_lock_res_at ξ γl pa).
  Proof using . rewrite /proc_lock_res_at. ctx_morph_solve. Qed.
  Global Instance proc_lock_pay_morph γl pa : CtxMorph (proc_lock_pay γl pa).
  Proof using . rewrite /proc_lock_pay. apply _. Qed.

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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
     running context can move them ([TsoCtx.ctx_move]).  Neither had a
     consumer. *)

  (* ------------------------------------------------------------------ *)
  (* A6.127 §6: THE RECORD/TOKEN SHAPES THE SWTCH CONTRACT SPEAKS.         *)
  (* ------------------------------------------------------------------ *)

  (* the pinned record's running token, into and out of the later the
     record always arrives beneath ([own_context] is timeless) *)
  Lemma sched_vc_at_intro (h : CPU) (c p : mword 64) (XIs : CtxId) :
    own_context (CID := h) XIs -∗ ▷ valid_context p_sched (Some h) c p XIs -∗
    ▷ sched_vc_at h c p.
  Proof using .
    iIntros "Hown Hrec". rewrite /sched_vc_at bi.later_exist. iExists XIs.
    rewrite bi.later_sep. iFrame "Hrec". iNext. iExact "Hown".
  Qed.

  Lemma sched_vc_at_tok (E : coPset) (h : CPU) (c p : mword 64) :
    ▷ sched_vc_at h c p ={E}=∗
    ∃ XIs : CtxId, own_context (CID := h) XIs ∗ ▷ valid_context p_sched (Some h) c p XIs.
  Proof using .
    rewrite /sched_vc_at bi.later_exist. iIntros "(%XIs & H)".
    rewrite bi.later_sep. iDestruct "H" as "[Hown Hrec]".
    iPoseProof (@timeless _ _ (own_context (CID := h) XIs) (own_context_timeless (CID := h) XIs)
                  with "Hown") as "Hown".
    iMod "Hown". iModIntro. iExists XIs. iFrame.
  Qed.

  (* a migratable record at the holder's own context IS what swtch wants of
     its target: parked under [cur_ctx] ([SwtchCtx.resume_tok None]) *)
  Lemma proc_ctx_resume_tok (pa : mword 64) :
    proc_ctx pa -∗
    ∃ XIt : CtxId, resume_tok None XIt ∗
                   ▷ valid_context p_sched None (p_context pa) pa XIt.
  Proof using .
    rewrite /proc_ctx /proc_ctx_at /resume_tok /=.
    iIntros "(%XIp & Hpk & Hrec)". iExists XIp. iFrame "Hpk Hrec".
  Qed.

  (* ...and what a park hands the resumed scheduler -- the record parked
     under the scheduler's own context ([SwtchCtx.park_tok None]) -- IS the
     slot at that context *)
  Lemma proc_ctx_of_tok (pa : mword 64) (XIo : CtxId) :
    park_tok None XIo -∗ ▷ valid_context p_sched None (p_context pa) pa XIo -∗
    proc_ctx pa.
  Proof using .
    rewrite /park_tok /park_tok_at /proc_ctx /proc_ctx_at /=. iIntros "Hpk Hrec".
    iExists XIo. iFrame "Hpk Hrec".
  Qed.

  (* THE RECLAIMING SCHEDULER'S SLOT: what the crossing handed back -- a
     RECORD (parked under this scheduler) at a resumable park, the bare
     CELLS at a ZOMBIE one, in exactly the shape the slot's own [needs_ctx]
     guard asks for -- plus whatever [park_pay] carried (the dormant block
     at a ZOMBIE park, nothing at a resumable one), all at the scheduler's
     own context.  No token: the scheduler's release then deposits the slot
     as an ordinary payload. *)
  Lemma proc_slots_park_gen (pa : mword 64) (st : mword 32) :
    park_ok st = true ->
    (if needs_ctx st then proc_ctx pa else own_ctx (p_context pa)) -∗
    hart_at_any pa -∗ pslot_used_at pa -∗ park_pay pa st -∗
    proc_slots pa st.
  Proof using .
    intros Hst. iIntros "Hctx Hpark #Hused Hpay".
    pose proof (is_unused_of_park_ok st Hst) as Hu.
    apply park_ok_cases in Hst as [Hn | Hz].
    - rewrite Hn. rewrite /proc_slots /proc_slots_at Hn Hu.
      rewrite (inv_dormant_of_needs_ctx st Hn) (not_running_of_needs_ctx st Hn).
      rewrite (is_running_of_needs_ctx st Hn).
      iFrame "Hctx Hpark". by iFrame "Hused".
    - subst st. rewrite /park_pay inv_dormant_ZOMBIE needs_ctx_ZOMBIE_false.
      iAssert (proc_dormant pa ZOMBIE) with "[Hpay Hctx]" as "Hdorm".
      { iEval (rewrite proc_dormant_split). iFrame "Hpay Hctx". }
      rewrite /proc_slots /proc_slots_at not_running_ZOMBIE inv_dormant_ZOMBIE
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
  Proof using .
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
  Proof using .
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
  Proof using . apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ is_lock γl (proc_addr i) "proc"%string (proc_lock_pay γl (proc_addr i)).
  Proof using .
    iIntros (Hi) "[_ [Hbig _]]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* the array's length -- what a scan's fuel bound is stated over. *)
  Lemma procs_inv_len : procs_inv -∗ ⌜length γs = NPROC⌝.
  Proof using . iIntros "[$ _]". Qed.

  (* ... and the per-proc kstack address. *)
  Lemma procs_inv_kstack (i : nat) (γl : gname) :
    γs !! i = Some γl ->
    procs_inv -∗ ∃ ks : mword 64, is_kstack (proc_addr i) ks.
  Proof using .
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
  Proof using .
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
  Proof using . iIntros "Hs Hg Hc Hpub Hsl". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γl : gname) (pa : mword 64) :
    proc_lock_res γl pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ pstate_lock pa st ∗
      p_chan pa ↦₈ ch ∗ proc_pub pa ∗ proc_slots pa st.
  Proof using . iIntros "H". iExact "H". Qed.

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
  Proof using .
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
Section SchedCtxTable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (γs : list gname).
  Global Instance procs_inv_morph : CtxMorph (λ ξ, procs_inv (XI := ξ) γs).
  Proof using . rewrite /procs_inv. ctx_morph_solve. Qed.
End SchedCtxTable.



(* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md):
   [procs_inv] is two [∗ list]s over NPROC, and it is named in 166 files.
   AT THE END OF THE FILE, so the accessors above -- [procs_inv_len],
   [procs_inv_lookup] and the kstack one -- can still take it apart.  Those
   accessors are what a consumer should use; four files had been hand-rolling
   [iDestruct "Hpinv" as "[%Hl _]"] instead, and now call [procs_inv_len]. *)
(* the [Typeclasses Opaque procs_inv] perf seal is DROPPED at the cutover:
   flip-shaped proofs open the bundle raw ([iDestruct "Hpinv" as "[%Hl _]"],
   ProofPipeclose-class), and TC-opacity turns those into "No matching
   clauses" failures.  If the iFrame crawl cost returns, re-seal and give
   the openers an accessor instead. *)
