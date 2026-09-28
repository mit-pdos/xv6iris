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

   WHAT THE LOCK PROTECTS.  Four things; the middle two are the pid
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

   - THE PID LEDGER ([pid_ledger], NI-LEDGER-REST, design
     ni-pid-ledger.md D3): the authority of the actor-labelled history of
     every allocation and release ([PidEv.pev], at the canonical
     [Xv6Cameras.wpl_name]), tied to the register by -- the history's live
     set IS the register's domain.  allocproc appends [PAlloc p pid] at its
     insert and freeproc [PFree p pid] at its delete, each handing its
     caller a persistent receipt ([SlotGen.pid_receipt]) -- a fourth thing
     the lock protects, riding beside the register it mirrors.

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
Require Import PidEv.   (* [pev] / [live_of]: the pid ledger's vocabulary *)
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
  (* ...AND THE BOOT ERA'S TWO MARKS (lane TRAP-ROWS-4, B1b), one beside
     the counter and one beside the 64 values.  Each is
     [<the boot fact> ∨ SlotGen.nextpid_shot], and together they say:

       EITHER <nextpid> IS STILL THE 1 THE .data CARVE PINNED AND NO SLOT
       HOLDS PID 1 -- so the very next <allocpid> hands out 1 on its FIRST
       candidate, with no retry -- OR THE BOOT-ERA TOKEN HAS BEEN SHOT.

     That is what pins <init>'s pid to the literal 1: userinit's allocproc
     is the only caller that holds [SlotGen.nextpid_pend] (it rides the
     proc ledger's counted regime, [ProcAvail.procs_avail_at _ true]),
     the token REFUTES the right disjunct, and the left one gives the
     value and kills the retry branch.  That same call then shoots the
     token at its store to <nextpid> and puts the shot back here.
       EVERY OTHER PARTY IS UNAFFECTED.  A caller that does not write
     <nextpid> -- freeproc, whose [p->pid = 0] cannot make a zero equal to
     1 -- hands whichever disjunct it received straight back; a caller
     that does (an uncounted allocproc) holds the shot already, off
     [ProcAvail.procs_avail None].  The marks are CONTEXT-FREE, so the
     payload is still a [TsoCtx.CtxMorph]. *)
  (* ...AND THE PID LEDGER (design ni-pid-ledger.md D3, ruling R2(a)): the
     history's authority, tied to the register by its live set alone.  The
     counter tie and the scan's first-ness are not stated (R2(b)/(c)).
     CONTEXT-FREE, so the payload is still a [TsoCtx.CtxMorph]. *)
  Definition pid_ledger (R : gmap Z gname) : iProp Σ :=
    (∃ h : list pev, pid_led_auth h ∗ ⌜live_of h = dom R⌝)%I.

  Global Instance pid_ledger_timeless R : Timeless (pid_ledger R).
  Proof using . rewrite /pid_ledger. apply _. Qed.

  Definition nextpid_res_at (ξ : CtxIdDefs.CtxId) : iProp Σ :=
    ((∃ v : mword 32, TsoCtx.ctx_word4_pointsto ξ alp_nextpid (DfracOwn 1) v ∗
                      ⌜1 <= bv_unsigned v <= PIDMAX⌝ ∗
                      (⌜bv_unsigned v = 1⌝ ∨ SlotGen.nextpid_shot)) ∗
     (∃ (pids : list (mword 32)) (R : gmap Z gname),
        ⌜length pids = NPROC /\ pid_reg_dom R pids⌝ ∗
        ([∗ list] j ↦ p ∈ pids, pid_lock_share_at ξ (proc_addr j) p) ∗
        pid_reg_auth R ∗ pid_ledger R ∗
        (⌜Forall (fun q : mword 32 => bv_unsigned q <> 1) pids⌝
         ∨ SlotGen.nextpid_shot)))%I.
  Definition nextpid_res : iProp Σ := nextpid_res_at CtxIdDefs.cur_ctx.

  Global Instance nextpid_res_at_morph : TsoCtx.CtxMorph nextpid_res_at.
  Proof using . rewrite /nextpid_res_at /pid_lock_share_at. CtxMorphTac.ctx_morph_solve. Qed.

  (* THE BOOT CARVE'S SHAPE, GATHERED, exactly as the parent cells' is
     ([WaitInv.parents_cells_gather]): the carve hands the 64 quarters out
     indexed by the slot, all at the 0 the .bss pins, and the payload wants
     one LIST of values.  An OFFSET induction because [seq k (S n)] is
     [k :: seq (S k) n]. *)
  Lemma pid_shares_gather (n k : nat) (v : mword 32) :
    ([∗ list] i ∈ seq k n, pid_lock_share_at CtxIdDefs.cur_ctx (proc_addr i) v)
    -∗ [∗ list] j ↦ p ∈ replicate n v,
         pid_lock_share_at CtxIdDefs.cur_ctx (proc_addr (k + j)) p.
  Proof using .
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
      (∃ v : mword 32, alp_nextpid ↦₄ v ∗ ⌜1 <= bv_unsigned v <= PIDMAX⌝ ∗
                       (⌜bv_unsigned v = 1⌝ ∨ SlotGen.nextpid_shot)) ∗
      (∃ (pids : list (mword 32)) (R : gmap Z gname),
         ⌜length pids = NPROC /\ pid_reg_dom R pids⌝ ∗
         ([∗ list] j ↦ p ∈ pids, pid_lock_share (proc_addr j) p) ∗
         pid_reg_auth R ∗ pid_ledger R ∗
         (⌜Forall (fun q : mword 32 => bv_unsigned q <> 1) pids⌝
          ∨ SlotGen.nextpid_shot)).
  Proof using . rewrite /nextpid_res /nextpid_res_at /pid_lock_share. reflexivity. Qed.

  (* THE LEDGER'S GHOST STEPS (design ni-pid-ledger.md §3 W2).  Each mirrors
     the register step it rides beside ([SlotGen.pid_reg_insert] /
     [pid_reg_delete]) and hands back the receipt of the event it appended.
     The boot's: the empty history is the empty register's ledger. *)
  Lemma pid_ledger_empty : pid_led_auth [] -∗ pid_ledger ∅.
  Proof using .
    iIntros "Ha". iExists []. iFrame "Ha". iPureIntro.
    by rewrite live_of_nil dom_empty_L.
  Qed.

  Lemma pid_ledger_alloc R (act : mword 64) (pid : mword 32) (g : gname) :
    pid_ledger R ==∗ pid_ledger (<[bv_unsigned pid := g]> R) ∗
                     ∃ h, pid_receipt h (PAlloc act pid).
  Proof using .
    iIntros "(%h & Ha & %Hl)".
    iMod (pid_led_auth_grow h (PAlloc act pid) with "Ha") as "[Ha #Hb]".
    iModIntro. iSplitL "Ha".
    - iExists _. iFrame "Ha". iPureIntro.
      by rewrite live_of_snoc_alloc dom_insert_L Hl.
    - iExists h. iExact "Hb".
  Qed.

  Lemma pid_ledger_free R (act : mword 64) (pid : mword 32) :
    pid_ledger R ==∗ pid_ledger (delete (bv_unsigned pid) R) ∗
                     ∃ h, pid_receipt h (PFree act pid).
  Proof using .
    iIntros "(%h & Ha & %Hl)".
    iMod (pid_led_auth_grow h (PFree act pid) with "Ha") as "[Ha #Hb]".
    iModIntro. iSplitL "Ha".
    - iExists _. iFrame "Ha". iPureIntro.
      by rewrite live_of_snoc_free dom_delete_L Hl.
    - iExists h. iExact "Hb".
  Qed.

End PidLock.
