(* SpecAllocproc.v -- the public interface of allocproc() (kernel/proc.c),
   stated independently of its proof.

     static struct proc *allocproc(void) {
       struct proc *p;
       for (p = proc; p < &proc[NPROC]; p++) {
         acquire(&p->lock);
         if (p->state == UNUSED) goto found;
         else release(&p->lock);
       }
       return 0;
     found:
       p->pid = allocpid();
       p->state = USED;
       if ((p->trapframe = kalloc()) == 0) { ... return 0; }
       p->pagetable = proc_pagetable(p);
       if (p->pagetable == 0) { ... return 0; }
       memset(&p->context, 0, sizeof(p->context));
       p->context.ra = (uint64)forkret;
       p->context.sp = p->kstack + PGSIZE;
       return p;
     }

   @ KernelSyms.allocproc = 0x80001b28, fifty-five instructions: a 32-byte
   ra/s0/s1/s2 frame, the scan loop (+0x1c .. +0x30), the allocation body
   (+0x38 .. +0x76), one shared epilogue at +0x78, and the two [freeproc]
   failure tails at +0x86 / +0x96.

   THE HEADLINE.  This is the function that turns a [ProcInv.proc_dormant]
   back into a [ProcInv.proc_priv] -- the one producer of the private block
   every syscall consumes -- and it is where the page table's CONSTRUCTION
   side (proc_pagetable, completed/proc-pagetable.md) meets its OWNERSHIP
   side (ProcPtOwn, projects/proc-pagetable-ownership.md), at
   [ProcPtOwn.proc_pt_intro_ppt].

   ON SUCCESS IT RETURNS WITH THE LOCK HELD.  allocproc never releases the
   slot it took: its caller (fork / userinit) keeps writing the child under
   [p->lock] and releases it itself.  So the post hands back
   [SchedCtx.proc_held j gl USED ch] -- the lock token and every cell the
   invariant holds unconditionally -- together with the detached private
   block, and [cpu_own] comes out at [S lvl] with the matching
   [arm_pay].  On the empty-table path (a0 = 0) every lock the scan
   touched has been released and [cpu_own] is back at [lvl].

   TWO CONTRACTS, ONE PROOF.  [ALLOCPROC_GEN] below states what allocproc
   does at ANY page budget: there both failure tails are live code, they run
   freeproc for real, and the third arm of [allocproc_post] is what they
   return.  [ALLOCPROC] is the COUNTED specialisation -- with more than
   [K_allocproc] free pages neither the trapframe [kalloc] nor
   proc_pagetable can run dry, so that third arm is REFUTABLE from the
   caller's own premise and a counted caller never sees a resealed budget.
   The refutation is thirty lines (ProofAllocproc's [AllocprocSeal]); the
   instruction-level proof is elaborated once, for both.

   WHAT THE POST SAYS ABOUT THE PROCESS.  Its user address space is EMPTY
   ([pv_upt V = upt_desc root tfp], whose [ud_um] is the empty map): the
   table maps TRAMPOLINE and TRAPFRAME and nothing else.  Every descriptor is
   null and [cwd] is 0, straight out of the dormant block, so the caller owes
   no file reference.  [p->sz] and [p->name] are whatever the block already
   held -- allocproc writes neither, and freeproc's zeroing of them has no
   consumer (design/proc-struct.md).  The pid is existential: allocpid's
   contract says nothing about the counter's value.

   THE SAVED CONTEXT comes back as raw cells, not as a
   [SchedCtx.proc_ctx]: turning "ra = forkret, sp = kstack + PGSIZE" into a
   member of the scheduler's swtch chain is a Löb argument about forkret,
   which belongs to the caller that parks the process, not here.  The twelve
   callee-saved slots are existential -- memset zeroed them, but nothing
   consumes that, and a resumed context may not read them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
(* the proc table's two regimes -- the counted premise that refutes the
   empty-table arm, and the marker the found slot is minted with *)
Require Import ProcAvail.
Require Import ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import SpecAllocpid.
Require Import LockRank.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.


(* The pages allocproc consumes: the trapframe page, plus the three
   proc_pagetable builds (root + the l1/l0 pair the TRAMPOLINE walk needs;
   TRAPFRAME shares both).  The premise is STRICT -- [K_allocproc < nb] for a
   4-page consumption -- by the kalloc chain's counted-arm convention: a
   [Some 0] remainder would leave the last mappages' [avail_zero] arm
   unrefutable. *)
Notation K_allocproc := (7%nat) (only parsing).
(* the value [p->context.ra] is left holding *)
Definition forkret_pc : mword 64 := mword_of_int KernelSyms.forkret.

(* The postcondition, as a function of the RETURNED POINTER.  Factoring it
   out of the continuation is what lets the proof's shared epilogue (both
   exits join at +0x78) be one lemma: the epilogue moves [s1] into a0, so it
   knows the returned value and nothing else about which arm produced it.

   THE EXIT SIE INDEX IS PER-ARM, WHICH IS WHY [sie_cap_gpr] LIVES IN HERE
   RATHER THAN IN THE CONTINUATION.  allocproc RETURNS HOLDING p->lock on the
   found arm and never releases it, so [acquire]'s unbalanced exit index
   ([false] whatever the entry [b]) propagates all the way out to the caller
   -- while the null arm, which releases everything, exits at [b].  A single
   [sie_cap_gpr mr K b pme] in the shared continuation is not merely
   unreachable at [b = true], it is REFUTABLE: [sie_arm true pme] owns
   [cpu_hart 0 true pme] and the found arm owns [cpu_hart (S lvl) eb pme],
   which [CpuOwn.cpu_own_arm_excl] contradicts.  So the "found a free slot"
   execution -- an ordinary one -- would have had no derivation at [b = true].
   Nothing in the premises forces [b = false], and nothing about this fails to
   compile: the contract typechecks and only the proof discovers it.

   Stating the whole contract at [b = false] would also have closed the hole,
   but dishonestly: [userinit] is the only caller today and does run at boot
   with interrupts off, yet [fork] -- which is what allocproc exists for --
   calls it from a syscall with interrupts on.  The per-arm index says what is
   actually true, and it is what fork will need, since fork must [release] the
   proc it gets back and [release] demands [sie_cap_gpr … false …]. *)
Definition allocproc_post
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    {kt : ktier} (γa γf : gname) (γs : list gname) (lvl : nat) (eb : bool)
    (pme : mword 64) (on : option nat) (op : option nat)
    (b : bool) (lks : gset string)
    (mr : regfile) (K : nat)
    (rv : mword 64) : iProp Σ :=
  ( (* --- no free slot: a0 = 0, every lock released, budget untouched.

        AND THE ARM REPORTS WHY, exactly as the third one does and exactly
        as [KallocInv]'s [kalloc_post] does for a null page: the scan
        passed all [NPROC] slots, so the caller's PROC count -- if it has
        one -- must be 0.  A caller in the counted regime ([userinit],
        holding [procs_avail (Some (S k))]) refutes the whole arm from
        that, which is the only way a function that does not check
        allocproc's result can be proved at all; an uncounted one (kfork,
        [procs_avail None]) reads it as no information and handles the
        arm.  See [ProcAvail.v]'s header. --- *)
    (⌜ rv = (zero_reg : mword 64) ⌝ ∗
     ⌜ avail_zero op ⌝ ∗
     sie_cap_gpr kt mr K b pme ∗
     cpu_own lvl eb pme b lks ∗
     kalloc_env γa on ∗
     procs_avail op)
  ∨ (* --- found: a0 = &proc[j], j's lock HELD, the private block built --- *)
    (∃ (j : nat) (γl : gname) (ch : mword 64) (pid : mword 32)
       (V : pprivate) (root tfp : mword 44) (ks : mword 64)
       (rest : list (mword 64)) (nc : nat),
       ⌜ rv = proc_addr j /\
         (j < NPROC)%nat /\ γs !! j = Some γl /\
         pv_upt V = upt_desc root tfp /\
         pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
         pv_cwd V = (zero_reg : mword 64) /\
         length rest = 12%nat /\ (nc <= K_allocproc)%nat ⌝ ∗
       proc_held cpu_id j γl USED ch ∗
       (* proc j's HART TAG, whole.  A not-RUNNING proc keeps both halves in
          its lock ([SchedCtx.proc_slots]'s [not_running] arm), which is the
          arm allocproc emptied; the caller gets them back here and can
          rebuild [proc_lock_res] at USED / RUNNABLE. *)
       hart_at_any (proc_addr j) ∗
       (* THE DEFICIT BLOCK, not [proc_priv]: allocproc has not set
          [p->cwd] -- the arm's own [pv_cwd V = 0] says so -- and
          [ProcInv.cwd_ref] has no null arm, so there is no [proc_priv] at
          this [V] to hand back.  The caller closes the construction window
          when it installs a working directory ([proc_priv_split_cwd]);
          kfork does it at its [sd a0,336(s4)]. *)
       proc_priv_nocwd γf (proc_addr j) pid V ∗
       (* THE SLOT IS NOW ALLOCATED.  Persistent, minted here out of
          [procs_avail]'s authority, and what the caller hands to
          [SchedCtx.proc_slots_park] when it releases the slot at USED or
          RUNNABLE -- a slot that has left UNUSED carries this on every arm
          of its lock invariant ([ProcAvail.v]). *)
       pslot_used_at (proc_addr j) ∗
       fd_slots FDSPARE ∗
       (* THE CWD'S UNIT AND THE IREF ALLOWANCE, out of the dormant block
          allocproc took the slot from.  The [1] is what kfork spends on
          [idup] -- allocproc is the function that took the slot out of
          [procs_inv], so it is where the unit has to come from. *)
       iref_slots (1 + IREFSPARE) ∗
       is_kstack (proc_addr j) ks ∗
       ctx_cells (p_context (proc_addr j))
         (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) ∗
       (* [trap_res b + K], NOT [K]: allocproc RETURNS HOLDING p->lock, so
          this arm inherits [acquire]'s unbalanced exit index verbatim -- the
          caller's trap reserve has moved into the usable count for the
          interrupts-off critical section it is still inside, and it stays
          there until the caller's own [release] gives it back.  The null arms
          below released everything, so they exit at [K] with arm [b] and the
          reserve back inside [sie_cap]'s [trap_res b] summand. *)
       sie_cap_gpr kt mr (trap_res b + K)%nat false pme ∗
       (* the found slot's OWN lock is now held, on top of whatever the
          caller already held: this is the one arm allocproc returns
          without releasing everything it took. *)
       cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) ∗
       arm_pay kt lvl eb pme ∗
       kalloc_env γa (avail_sub on nc) ∗
       (* one slot fewer, by the same [avail_dec] the page count uses *)
       procs_avail (avail_dec op))
  ∨ (* --- a FAILURE TAIL ran: the slot was taken and then given back.  a0
        is 0 and every lock is released, exactly as in the first arm, but
        two things differ and both matter.

        The COUNT IS GONE.  The tails call freeproc, whose callees (kfree,
        proc_freepagetable) are stated only at [kalloc_env _ None], so the
        environment has been resealed and no caller can ever count again.
        That is why this cannot be folded into the first arm.

        And the arm records WHY it was reached: the allocator ran dry after
        [n <= K_allocproc] pages.  A COUNTED caller refutes the whole arm
        from its own [K_allocproc < nb]; an uncounted one (kfork) handles
        it.  Carrying the witness is what lets ONE proof serve both. --- *)
    (⌜ rv = (zero_reg : mword 64) ⌝ ∗
     ⌜ exists n : nat, (n <= K_allocproc)%nat /\ avail_zero (avail_sub on n) ⌝ ∗
     sie_cap_gpr kt mr K b pme ∗
     cpu_own lvl eb pme b lks ∗
     kalloc_env γa None ∗
     procs_avail op))%I.

Definition wp_allocproc_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (γp : gname) (γf : gname) 
    (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
    (pme : mword 64) (on : option nat) (op : option nat)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.allocproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* 4 slots for this frame, 44 for freeproc's -- the deepest callee now
     that the error tails are live code (proc_pagetable needs 40) *)
  (48 <= K)%nat ->
  (* the proc lock is HELD across kalloc / proc_pagetable, so their own
     push_off sees [S lvl] and needs one more slot of headroom than usual *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (exists nb, on = Some nb /\ (K_allocproc < nb)%nat) ->
  (* allocproc's own acquire needs every lock this hart already holds to
     rank below "proc" (11) -- the ONLY lock allocproc itself acquires.
     The nested calls it makes while p->lock is held (allocpid's "nextpid"
     (12), kalloc's "kmem" (13)) both rank ABOVE "proc", so
     [locks_below_mono] plus [locks_below_union_singleton] derive their
     order premises from this single bound; see ProofAllocproc.v. *)
  locks_below lks "proc" ->
  sie_cap_gpr kt m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv (kt := kt) γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  kalloc_env γa on -∗
  (* the proc table's regime, threaded exactly as [kalloc_env] is *)
  procs_avail op -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      allocproc_post (kt := kt) γa γf γs lvl eb pme on op b lks mr K
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE GENERAL CONTRACT.  Identical to the one below except that it drops the
   counted premise: everything allocproc actually does is here, and the third
   arm of [allocproc_post] is what makes an uncounted run STATABLE.  kfork
   calls allocproc with no page budget, and there the two freeproc tails are
   LIVE code. *)
Definition wp_allocproc_core_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (γp : gname) (γf : gname) 
    (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
    (pme : mword 64) (on : option nat) (op : option nat)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.allocproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (48 <= K)%nat ->
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* same order premise as the counted contract above -- "proc" is the
     lowest (only) rank this function itself acquires. *)
  locks_below lks "proc" ->
  sie_cap_gpr kt m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv (kt := kt) γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  kalloc_env γa on -∗
  (* the proc table's regime, threaded exactly as [kalloc_env] is *)
  procs_avail op -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      allocproc_post (kt := kt) γa γf γs lvl eb pme on op b lks mr K
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ALLOCPROC_GEN.
  Parameter wp_allocproc_core :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (γp : gname) (γf : gname) (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (on : option nat) (op : option nat)
      (b : bool) (lks : gset string),
      wp_allocproc_core_body kt γa γp γf γs m lvl K eb pme on op b lks.
End ALLOCPROC_GEN.

Module Type ALLOCPROC.
  Parameter wp_allocproc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (γp : gname) (γf : gname) (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (on : option nat) (op : option nat)
      (b : bool) (lks : gset string),
      wp_allocproc_sconf_body kt γa γp γf γs m lvl K eb pme on op b lks.
End ALLOCPROC.
