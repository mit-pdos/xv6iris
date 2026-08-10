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

   THE ICACHE PREMISES ARE THE PRICE OF [ProcInv.cwd_ref] STILL BEING A
   HOLE, AND THEY ARE TEMPORARY -- BUT THEY HAVE GROWN.  kfork runs
   [np->cwd = idup(p->cwd)], and [SpecIdup.v] is no longer an assumed
   contract over the placeholder: it is proven against the real inode
   cache.  Its v2 form wants [IcacheEscrow.is_itable2 γil cn γfs γic cov
   logstart nib] -- which drags the DISK AND LOG fabric ([γfs], [cov],
   [logstart], [nib]) into kfork's contract -- plus [itable_inv (icn_ref
   cn)], one [IrefSlots.iref_slot], and an actual
   [IcacheInv.inode_ref (icn_ref cn) ck cq cdev cinum] on the entry
   [p->cwd] names.  kfork does no I/O and touches no log; it inherits all
   of that to bump ONE reference count.
   [ProcInv.cwd_ref] is [FileInv.inode_ref], which is literally [emp]
   (design/proc-struct.md's "holes to be honest about", tracked as S5 in
   claude-notes/projects/proc-struct-resources.md), so the parent's own
   [proc_priv] CANNOT produce that reference and kfork has to be handed it.
   Hence the premise [pv_cwd Vp = ientry ck] and the reference itself.

   The reference comes BACK -- at an unnamed fraction, because idup halves
   it and the two failure arms never call idup at all, so [∃ q'] is the only
   statement true on every path.  That is the same shape [ofile_slot] uses
   for a descriptor's [file_ref], and for the same reason.  The child's half
   is DROPPED: it should go into the child's [cwd_ref], which is [emp], so
   there is nowhere to put it.  The [iref_slot] is likewise consumed and not
   returned (it is spent on exactly the path that calls idup, and claiming
   it back on the others would be a stronger post than the code delivers for
   no consumer).

   When S5 lands -- [cwd_ref] becomes "v names a live itable entry and this
   is one of its references" -- ALL of this collapses: the parent's
   reference and the child's both come out of / go into their own
   [proc_priv] blocks, the [ientry] premise becomes a consequence of the
   parent's block, and the [iref_slot] rides beside a dormant process the
   way [fd_slots FDSPARE] already does.  Only this file and [ProofKfork.v]'s
   idup call site change; nothing else in kfork's proof touches them. *)
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
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
      !icacheG Σ, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γf : gname) (cn : ic_names) (lvl : nat) (eb : bool)
    (pme : mword 64) (C : iProp Σ)
    (b : bool) (pid_p : mword 32) (Vp : pprivate)
    (ck : nat) (cdev cinum : mword 32)
    (K : nat) (mr : regfile) (rv : mword 64) : iProp Σ :=
  ( sie_cap_gpr mr K b pme ∗
    cpu_own lvl eb pme C b ∗
    (* THE PARENT COMES BACK VERBATIM on every arm -- kfork only reads it. *)
    proc_priv γf pme pid_p Vp ∗
    (* ... and so does its cwd reference, at whatever is left of it: idup
       halves it on the success path and never runs on the two failure
       paths, so [∃ q'] is the only statement true on all of them. *)
    (∃ q' : Qp, inode_ref (icn_ref cn) ck q' cdev cinum) ∗
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
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
      !icacheG Σ, !irefslotG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa γp γw γl γf γil γic : gname)  (γs : list gname)
    (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
    (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
    (b : bool) (pid_p : mword 32) (Vp : pprivate)
    (ck : nat) (cq : Qp) (cdev cinum : mword 32) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfork in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kfork <= K)%nat ->
  (* propagates to every callee's own nesting-level bound: allocproc's own
     (lvl+2), and -- once the lock is held -- uvmcopy/freeproc/filedup/idup
     at (S lvl)+1 = lvl+2 again. *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* p->cwd names itable entry [ck].  A consequence of the parent's own
     block once [ProcInv.cwd_ref] stops being [emp]; a premise until then. *)
  pv_cwd Vp = ientry ck ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  is_ftable γl γf -∗
  is_itable2 γil cn γfs γic cov logstart nib -∗
  itable_inv (icn_ref cn) -∗
  iref_slot -∗
  inode_ref (icn_ref cn) ck cq cdev cinum -∗
  kalloc_env γa None -∗
  proc_priv γf pme pid_p Vp -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ (mr : regfile),
      ⌜ callee_saved m mr ⌝ -∗
      pc_is ret_tgt -∗
      kfork_post γa γf cn lvl eb pme C b pid_p Vp ck cdev cinum K mr
        (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KFORK.
  Parameter wp_kfork_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
             !icacheG Σ, !irefslotG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa γp γw γl γf γil γic : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (b : bool) (pid_p : mword 32) (Vp : pprivate)
      (ck : nat) (cq : Qp) (cdev cinum : mword 32),
      wp_kfork_sconf_body γa γp γw γl γf γil γic γs cn γfs cov logstart nib
        m lvl K eb pme C b pid_p Vp ck cq cdev cinum.
End KFORK.
