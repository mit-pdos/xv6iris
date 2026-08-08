(* SpecKfork.v -- the public interface of kfork() (kernel/proc.c), stated
   independently of its proof.

     int kfork(void) {
       int i, pid;
       struct proc *np;
       struct proc *p = myproc();

       if ((np = allocproc()) == 0) { return -1; }

       if (uvmcopy(p->pagetable, np->pagetable, p->sz) < 0) {
         freeproc(np); release(&np->lock); return -1;
       }
       np->sz = p->sz;

       *(np->trapframe) = *(p->trapframe);
       np->trapframe->a0 = 0;

       for (i = 0; i < NOFILE; i++)
         if (p->ofile[i]) np->ofile[i] = filedup(p->ofile[i]);
       np->cwd = idup(p->cwd);

       safestrcpy(np->name, p->name, sizeof(p->name));
       pid = np->pid;
       release(&np->lock);

       acquire(&wait_lock); np->parent = p; release(&wait_lock);

       acquire(&np->lock); np->state = RUNNABLE; release(&np->lock);

       return pid;
     }

   @ KernelSyms.kfork = 0x80001c76, 270 bytes: a 64-byte ra/s0/s1/s4/s5 frame
   (s2/s3/s4 LAZILY spilled -- see below), the two `if` failure tails, the
   trapframe word-copy loop (+0x4a..+0x58, four words/iteration), the
   [filedup] scan over [NOFILE] descriptors, and the two lock crossings
   ([np->lock] release/reacquire around [wait_lock]'s acquire/write/release).

   THE SHRINK-WRAPPED EPILOGUE.  Three exits share ONE tail (+0xfc,
   `mv a0,s1; <pop ra/s0/s1/s5>; ret`), but s2/s3/s4 are pushed/popped only
   on the arms that actually use them (kexit.md's "a lazily-spilled
   callee-saved register makes [callee_saved] a PREMISE of the epilogue" --
   the exact same shape here):
     - allocproc fails (+0x16): jumps straight past the s2/s3/s4 reloads --
       neither register was ever touched, so the CALLER'S values are still
       sitting in the physical registers, untouched.
     - uvmcopy fails (+0x7c): s4 (=np) WAS written, so its slot is reloaded
       before the jump; s2/s3 were never touched (they are pushed only after
       uvmcopy SUCCEEDS), so they are not reloaded either.
     - success: falls through the ordinary `ld s2,32(sp); ld s3,24(sp);
       ld s4,16(sp)` sequence.

   THE PRECONDITION IS GENERIC IN THE ALLOCATOR'S COUNT ([on : option nat]),
   NOT COUNTED -- kfork calls allocproc with no page budget
   (claude-notes/projects/proc-struct-resources.md, "S7 -- allocproc in the
   UNCOUNTED regime"), so both of allocproc's own [freeproc] failure tails
   are LIVE code here, and [kfork_post]'s first disjunct has to cover both
   of [allocproc_post]'s "no free slot" shapes (untouched count, or a
   resealed one that RAN a tail and can no longer say how many pages are
   left).

   THE COUNT IS GONE THE MOMENT [uvmcopy] IS CALLED, REGARDLESS OF WHICH ARM
   KFORK TAKES.  [uvmcopy]'s own contract only runs in the allocator's
   STEADY STATE ([kalloc_env γa None] -- and so does [freeproc]'s), so
   between allocproc's own [avail_sub on nc] and the [uvmcopy] call, kfork's
   proof must reseal ([KvmSpec.kalloc_env_seal]).  That makes EVERY arm past
   "allocproc found a slot" -- both the uvmcopy-failure arm and the success
   arm -- report [kalloc_env γa None] and nothing sharper; only the very
   first "no free slot" arm can still report the caller's own [on]
   unchanged (the one arm where [uvmcopy] never ran at all).

   NOTHING ABOUT THE CHILD COMES BACK, on EITHER of the two arms that reach
   a stable final state for it.  On the uvmcopy-failure arm, [freeproc]
   fully reclaims the slot to [proc_dormant _ UNUSED] and its lock is
   released, so the slot is back in [procs_inv] (persistent) with nothing
   owed to the caller.  On the success arm the child is parked at RUNNABLE,
   also inside [procs_inv], and design/proc-struct.md's "USED/RUNNING maps
   to emp" note is exactly what licenses NOT threading the child's private
   block back out through kfork's own postcondition -- it was handed
   entirely to the RUNNABLE park (a Löb argument about `forkret`, assumed
   here as [SpecForkretPark.FORKRET_PARK] -- see [ProofKfork.v]'s header for
   why that is a NEW, honest assumption and not a design shortcut).  Either
   way [kfork_post] says only: the return value, and [kalloc_env] at its
   final state.

   THE PARENT COMES BACK UNCHANGED, ON EVERY ARM.  kfork only ever READS
   [p]'s fields (pagetable/sz for uvmcopy, the trapframe contents, each
   [ofile] slot for [filedup], [cwd] for [idup], [name] for [safestrcpy]) --
   it writes nothing into the parent's block on any path -- so
   [proc_priv γf pme pid_p Vp] is taken as a precondition and handed back
   verbatim, exactly as [SpecUvmcopy.v]'s own "the parent's table comes back
   verbatim" note already says about the one piece of it uvmcopy itself
   touches.

   [pme] IS THE PARENT.  Every other whole-function contract in this tree
   names "the calling process" through [cpu_own]'s own [p] parameter rather
   than through a separate premise on [myproc()]'s result (myproc's own
   contract, [SpecMyproc.v], returns exactly THAT [p]), and kfork is no
   different: [pme] is both [cpu_own]'s process index and the parent [p] the
   C source calls [myproc()] to get. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import CpuOwn.
Require Import KallocInv.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import SpecAllocpid.
Require Import SpecAllocproc.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* kfork's own frame is 8 slots (addi sp,sp,-64); the deepest callee is
   allocproc's UNCOUNTED core, [wp_allocproc_core_body] (48) -- deeper than
   uvmcopy (42), freeproc (44), filedup/idup (14 apiece), acquire/release
   (10), myproc (10), safestrcpy (2). *)
Definition K_kfork : nat := 56%nat.

Definition kfork_post
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γf : gname) (lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
    (on : option nat) (b : bool) (pid_p : mword 32) (Vp : pprivate)
    (K : nat) (mr : regfile) (rv : mword 64) : iProp Σ :=
  ( sie_cap_gpr mr K b pme ∗
    cpu_own lvl eb pme C b ∗
    proc_priv γf pme pid_p Vp ∗
    ( (* --- allocproc itself found no slot: the same "not found" shape as
           [SpecAllocproc.allocproc_post]'s own first/third disjuncts,
           because kfork does nothing to the allocator's count between
           allocproc's return and its own [return -1] on this arm --- *)
      (⌜ rv = (mword_of_int (-1) : mword 64) ⌝ ∗
       ( kalloc_env γa on
         ∨ (∃ n : nat, ⌜ (n <= K_allocproc)%nat /\ avail_zero (avail_sub on n) ⌝ ∗
            kalloc_env γa None) ))
    ∨ (* --- uvmcopy failed: freeproc ran, the child is fully reclaimed
           (back in [procs_inv], nothing owed to the caller), and the
           allocator has been resealed to the steady state uvmcopy and
           freeproc both require --- *)
      (⌜ rv = (mword_of_int (-1) : mword 64) ⌝ ∗ kalloc_env γa None)
    ∨ (* --- success: the child is parked RUNNABLE (also back in
           [procs_inv], also nothing owed), and [rv] is its pid,
           sign-extended exactly as the `lw`/`mv a0,s1` pair leaves it --- *)
      (∃ pidv : mword 32,
         ⌜ rv = (sign_extend' 64 pidv : mword 64) ⌝ ∗ kalloc_env γa None) ) )%I.

Definition wp_kfork_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γp γw γl γf : gname) (Φ : mval -> iProp Σ) (γs : list gname)
    (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
    (on : option nat) (b : bool) (pid_p : mword 32) (Vp : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfork in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kfork <= K)%nat ->
  (* propagates to every callee's own nesting-level bound: allocproc's own
     (lvl+2), and -- once the lock is held -- uvmcopy/freeproc/filedup/idup
     at (S lvl)+1 = lvl+2 again. *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv Φ γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  is_ftable γl γf -∗
  kalloc_env γa on -∗
  proc_priv γf pme pid_p Vp -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      kfork_post γa γf lvl eb pme C on b pid_p Vp K mr
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KFORK.
  Parameter wp_kfork_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa γp γw γl γf : gname) (Φ : mval -> iProp Σ) (γs : list gname)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (on : option nat) (b : bool) (pid_p : mword 32) (Vp : pprivate),
      wp_kfork_sconf_body γa γp γw γl γf Φ γs m lvl K eb pme C on b pid_p Vp.
End KFORK.
