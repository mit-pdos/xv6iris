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
   [trap_csrs_pay].  On the empty-table path (a0 = 0) every lock the scan
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
Require Import ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import SpecAllocpid.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* The pages allocproc consumes: the trapframe page, plus the three
   proc_pagetable builds (root + the l1/l0 pair the TRAMPOLINE walk needs;
   TRAPFRAME shares both).  The premise is STRICT -- [K_allocproc < nb] for a
   4-page consumption -- by the kalloc chain's counted-arm convention: a
   [Some 0] remainder would leave the last mappages' [avail_zero] arm
   unrefutable. *)
Definition K_allocproc : nat := 4.

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
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa γf : gname) (γs : list gname) (lvl : nat) (eb : bool)
    (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool)
    (mr : regfile) (K : nat)
    (rv : mword 64) : iProp Σ :=
  ( (* --- no free slot: a0 = 0, every lock released, budget untouched --- *)
    (⌜ rv = (zero_reg : mword 64) ⌝ ∗
     sie_cap_gpr mr K b pme ∗
     cpu_own lvl eb pme C b ∗
     kalloc_env γa on)
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
       (* the OTHER half of proc j's park receipt.  [proc_held] carries one
          half (the crossing's share); the slot allocproc emptied held BOTH,
          since a not-RUNNING proc's receipt lives in its lock
          ([SchedCtx.proc_slots]).  So the caller gets the second half here
          and can rebuild [proc_lock_res] at USED / RUNNABLE. *)
       park_hlf j false ∗
       proc_priv γf (proc_addr j) pid V ∗
       fd_slots FDSPARE ∗
       is_kstack (proc_addr j) ks ∗
       ctx_cells (p_context (proc_addr j))
         (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) ∗
       sie_cap_gpr mr K false pme ∗
       cpu_own (S lvl) eb pme C false ∗
       trap_csrs_pay lvl eb ∗
       kalloc_env γa (avail_sub on nc))
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
     sie_cap_gpr mr K b pme ∗
     cpu_own lvl eb pme C b ∗
     kalloc_env γa None))%I.

Definition wp_allocproc_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γp : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
    (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.allocproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* 4 slots for this frame, 44 for freeproc's -- the deepest callee now
     that the error tails are live code (proc_pagetable needs 40) *)
  (48 <= K)%nat ->
  (* the proc lock is HELD across kalloc / proc_pagetable, so their own
     push_off sees [S lvl] and needs one more slot of headroom than usual *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (exists nb, on = Some nb /\ (K_allocproc < nb)%nat) ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv Φ γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  kalloc_env γa on -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      allocproc_post γa γf γs lvl eb pme C on b mr K
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* THE GENERAL CONTRACT.  Identical to the one below except that it drops the
   counted premise: everything allocproc actually does is here, and the third
   arm of [allocproc_post] is what makes an uncounted run STATABLE.  kfork
   calls allocproc with no page budget, and there the two freeproc tails are
   LIVE code. *)
Definition wp_allocproc_core_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γp : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
    (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.allocproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (48 <= K)%nat ->
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv Φ γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  kalloc_env γa on -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      allocproc_post γa γf γs lvl eb pme C on b mr K
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ALLOCPROC_GEN.
  Parameter wp_allocproc_core :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γp : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool),
      wp_allocproc_core_body γa γp γf Φ γs m lvl K eb pme C on b.
End ALLOCPROC_GEN.

Module Type ALLOCPROC.
  Parameter wp_allocproc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γp : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool),
      wp_allocproc_sconf_body γa γp γf Φ γs m lvl K eb pme C on b.
End ALLOCPROC.
