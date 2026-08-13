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

   THERE IS NO PAGE COUNT.  kfork is reached from [sys_fork] and from
   nowhere else, so it never runs in the allocator's COUNTED regime: the
   precondition is [kalloc_env γa None] outright, not a generic
   [on : option nat].  Two things follow and both simplify the contract.

   First, allocproc is called with no budget, so both of its own [freeproc]
   failure tails are LIVE code here (claude-notes/projects/
   proc-struct-resources.md, "S7 -- allocproc in the UNCOUNTED regime").

   Second, and this is what shrinks [kfork_post]: at [None] every arm
   reports the SAME thing.  [uvmcopy] and [freeproc] are stated only at
   [kalloc_env γa None], so the two arms past "found a slot" were always
   going to report it; and the "no free slot" arm, which used to be able to
   hand the caller's own [on] back untouched, now hands back [None] too --
   while [allocproc_post]'s third disjunct degenerates, since
   [avail_sub None n] is [None] and [avail_zero None] is [True], so its
   "the allocator ran dry after n pages" witness says nothing.  So
   [kalloc_env γa None] is hoisted OUT of the disjunction, beside
   [proc_priv], and the three arms collapse to TWO: the return value is
   either -1 or the child's pid, and that is the whole of what the arms
   still distinguish.

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
   C source calls [myproc()] to get.

   THE CWD REFERENCE IS INSIDE THE TWO [proc_priv] BLOCKS, WHICH IS WHY
   THIS CONTRACT NO LONGER NAMES AN INODE.  kfork runs
   [np->cwd = idup(p->cwd)], and [SpecIdup.v] wants a real
   [IcacheInv.inode_ref] on the entry [p->cwd] names.  That used to be a
   PREMISE -- together with [pv_cwd Vp = ientry ck] and the four parameters
   [ck cq cdev cinum] -- because [ProcInv.cwd_ref] was [emp] and the
   parent's own block could not produce it.  It is real now
   ([InodeRef.iref_at]), so the parent's block DOES produce it: the slot,
   the device and the inum are read off [cwd_ref (pv_cwd Vp)] inside
   [ProofKforkB4], idup's two halves go back into the parent's block and
   into the CHILD's, and nothing about an inode appears here or in
   [kfork_post].

   What is left of the icache is only what the LOCK needs:
   [IcacheEscrow.is_itable2 γil cn γfs γic cov logstart nib icfg_dev] (which drags
   the disk and log fabric -- [γfs], [cov], [logstart], [nib] -- along) and
   [itable_inv].  No coherence side condition ties the caller's lock to
   [ProcInv.cwd_ref]'s reference: both are stated over the same canonical
   [IcacheInv.iref_name] by construction, so there is nothing left to
   equate; [InodeRef.v]'s header explains why the authority's gname is
   canonical instead of threaded.

   THE CHILD IS HANDED OVER AS A DEFICIT BLOCK AND COMES BACK WHOLE.
   allocproc returns [ProcInv.proc_priv_nocwd] -- a process whose [p->cwd]
   is still 0 holds no reference and does not satisfy [proc_priv] -- and
   kfork's [sd a0,336(s4)] at +0xac is what closes the construction window,
   with idup's second half.  That is the whole reason idup returns two.

   AND THE [iref_slot] IS NOT A PREMISE EITHER.  What makes [ip->ref++]
   safe is one unit of [IrefSlots]' fixed supply, and it comes out of
   ALLOCPROC with the child's block -- allocproc is the function that took
   the slot out of [procs_inv], and a dormant process parks
   [iref_slots (1 + IREFSPARE)] exactly as it parks [fd_slots FDSPARE].
   The [1] is the child's own cwd unit: while [np->cwd] is 0 the process
   holds the unit itself, and the [sd a0,336(s4)] is where it stops --
   spent on the reference [idup] creates, and parked in the itable against
   it from then on.  That bijection is what makes
   [IREFSLOTS = NPROC*(1 + IREFSPARE) + NFILE] literally true. *)
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
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecAllocpid.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import PanicStub.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* kfork's own frame is 8 slots (addi sp,sp,-64); the deepest callee is
   allocproc's UNCOUNTED core, [wp_allocproc_core_body] (48) -- deeper than
   uvmcopy (42), freeproc (44), filedup/idup (14 apiece), acquire/release
   (10), myproc (10), safestrcpy (2). *)
Definition K_kfork : nat := 56%nat.

Definition kfork_post
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γf : gname) (cn : ic_names) (lvl : nat) (eb : bool)
    (pme : mword 64) (C : iProp Σ)
    (b : bool) (pid_p : mword 32) (Vp : pprivate)
    (K : nat) (mr : regfile) (rv : mword 64) : iProp Σ :=
  ( sie_cap_gpr mr K b pme ∗
    cpu_own lvl eb pme C b ∗
    (* THE PARENT COMES BACK VERBATIM on every arm -- kfork only reads it.
       Its cwd reference comes back INSIDE it: idup halves the fraction on
       the success path and does not run at all on the two failure paths,
       and [ProcInv.cwd_ref] hides the fraction, so the block is stated at
       the very same [Vp] either way. *)
    proc_priv γf pme pid_p Vp ∗
    (* THE ALLOCATOR'S STATE IS THE SAME ON EVERY ARM, so it is stated ONCE
       here rather than per-disjunct.  See the header: with no page count
       there is nothing left for the arms to disagree about. *)
    kalloc_env γa None ∗
    (* ... and what IS left is only the return value.  Nothing about the
       CHILD appears: on the failure arm freeproc returned it to
       [procs_inv], on the success arm the RUNNABLE park swallowed it. *)
    ( (* allocproc found no slot, or uvmcopy failed *)
      ⌜ rv = (mword_of_int (-1) : mword 64) ⌝
    ∨ (* the child's pid, sign-extended exactly as `lw`/`mv a0,s1` leaves it *)
      (∃ pidv : mword 32, ⌜ rv = (sign_extend' 64 pidv : mword 64) ⌝) ) )%I.

Definition wp_kfork_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ,
      !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γp γw γl γf γil γic : gname)  (γs : list gname)
    (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
    (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
    (b : bool) (pid_p : mword 32) (Vp : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfork in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kfork <= K)%nat ->
  (* propagates to every callee's own nesting-level bound: allocproc's own
     (lvl+2), and -- once the lock is held -- uvmcopy/freeproc/filedup/idup
     at (S lvl)+1 = lvl+2 again. *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* THE PARENT HAS A WORKING DIRECTORY.  [ProcInv.cwd_ref] is two-armed on
     the pointer -- a process between [p->cwd = 0] and its next chdir owns
     no reference.  xv6's fork runs [np->cwd = idup(p->cwd)] with no null
     test, and that is still the honest reading of the code -- but it is no
     longer a PREMISE: [ProcInv.cwd_ref] has no null arm, so the parent's
     own [proc_priv] carries it ([proc_priv_cwd_nonzero]). *)
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  is_ftable γl γf -∗
  is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
  itable_inv -∗
  kalloc_env γa None -∗
  proc_priv γf pme pid_p Vp -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      kfork_post γa γf cn lvl eb pme C b pid_p Vp K mr
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KFORK.
  Parameter wp_kfork_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ,
             !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa γp γw γl γf γil γic : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (b : bool) (pid_p : mword 32) (Vp : pprivate),
      wp_kfork_sconf_body γa γp γw γl γf γil γic γs cn γfs cov logstart nib
        m lvl K eb pme C b pid_p Vp.
End KFORK.
