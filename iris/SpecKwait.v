(* SpecKwait.v -- the public interface of kwait(), stated independently of its
   proof.

     int kwait(uint64 addr) {
       struct proc *pp;
       int havekids, pid;
       struct proc *p = myproc();
       acquire(&wait_lock);
       for (;;) {
         havekids = 0;
         for (pp = proc; pp < &proc[NPROC]; pp++) {
           if (pp->parent == p) {
             acquire(&pp->lock);
             havekids = 1;
             if (pp->state == ZOMBIE) {
               pid = pp->pid;
               if (addr != 0 && copyout(p->pagetable, addr,
                                        (char * )&pp->xstate,
                                        sizeof(pp->xstate)) < 0) {
                 release(&pp->lock); release(&wait_lock); return -1;
               }
               pp->parent = 0;
               freeproc(pp);
               release(&pp->lock); release(&wait_lock);
               return pid;
             }
             release(&pp->lock);
           }
         }
         if (!havekids || killed(p)) { release(&wait_lock); return -1; }
         sleep(p, &wait_lock);
       }
     }

   @ KernelSyms.kwait = 0x80002176, 248 bytes / ninety-two instructions.  The
   shape, read off the image (the spec has to be honest about all of it):

     +0x00  an 80-byte frame: ra and s0..s7 are all saved.  s1 = pp (the scan
            cursor), s2 = p, s3 = &proc[NPROC] during the scan and the RETURN
            VALUE afterwards, s4 = ZOMBIE, s5 = 1, s6 = &wait_lock,
            s7 = addr.  [havekids] lives in a4 -- a caller-saved temp, which
            is legal only because gcc rewrites it after every call that could
            clobber it (+0xc6), so it is never live across one.
     +0x18  myproc()      +0x26  acquire(&wait_lock)     +0x3e  -> +0xdc
     +0xdc  THE OUTER LOOP head: havekids = 0, pp = &proc[0], -> +0xae
     +0xae  THE INNER SCAN: ld a5,56(s1) / bne s2,a5 -> +0xa6 / acquire /
            lw a5,24(s1) / beq s4,a5 -> +0x40 / release / a4 = 1 / -> +0xa6
     +0xa6  pp++         +0xaa  beq s1,s3 -> +0xca (end of table)
     +0x40  THE FOUND ARM: pid = pp->pid; the addr != 0 copyout; the
            [pp->parent = 0] store; freeproc; the two releases; -> +0x78
     +0x90  copyout failed: the two releases, s3 = -1, -> +0x78
     +0xca  havekids == 0 -> +0xe8; killed(p) != 0 -> +0xe8; else sleep,
            then the outer back edge to +0xdc
     +0xe8  release(&wait_lock), s3 = -1, -> +0x78
     +0x78  the one epilogue: a0 = s3, restore, ret

   THE CONTRACT.  Three things make it different from every syscall proved
   before it.

   * IT TAKES A SECOND LOCK, AND THE SECOND LOCK'S RESOURCE IS THE POINT.
     [WaitInv.wait_res] -- all NPROC [p->parent] cells -- is what wait_lock
     protects, and holding it is what licenses BOTH the [ld a5,56(s1)] the
     scan runs on every slot and the [sd x0,56(s1)] that disowns the child.
     [parent] cannot live in [SchedCtx.proc_lock_res]: it is read across
     processes by a holder of wait_lock who holds no proc lock at all, and
     putting it there would make the documented lock order wait_lock ->
     p->lock unstateable.  See WaitInv.v.

   * IT REACHES A ZOMBIE'S PRIVATE BLOCK, WHICH NOTHING ELSE DOES.  The
     child's [ProcInv.proc_dormant _ ZOMBIE] comes out of the child's own
     lock through [SchedCtx.proc_slots]'s [inv_dormant] guard, and
     [SpecFreeproc.fp_of_dormant_zombie] is what turns it into freeproc's
     precondition.  That bridge is exactly the gap SpecFreeproc.v used to
     record as unwritten; closing it is what made this proof possible.

   * WHAT IT SAYS ABOUT THE RESULT IS ALL THAT IS TRUE.  Nothing in the tree
     ties a pid to a slot ([SchedCtx.proc_pub] quantifies every slot's pid
     existentially), and nothing ties a parent cell to a process, so the
     return value can only be reported as SOME sign-extended [int] -- the
     same honesty as kkill's and killed's.  Note this covers both arms: the
     found arm returns [pp->pid] through an [lw] (hence sign-extended) and
     the three failure arms return [li -1].

   NOT here: [arm_pay].  kwait's own acquire(&wait_lock) produces the
   level-0 pay that sleep wants, and every exit's release consumes it, so
   kwait as a whole is balanced and must not ask the caller for one -- the
   sys_pause rule (a second [trap_csrs] makes the eb = true precondition
   unsatisfiable and the spec vacuous exactly where interrupts are on).

   [eb = true] IS A PREMISE, for the reason every parking function has it:
   at level 0 with an enabled base the pushing acquire hands out the trap
   CSRs the chain payload demands (SpecSched.v).

   THE PRIVATE BLOCK GOES IN AND COMES BACK AT AN EXTENDED DESCRIPTOR.  The
   only thing kwait does to the caller's own address space is copyout's
   lazy faulting, so the post is [proc_priv] at [upd_upt V P'] with
   [uptd_ext_sz], exactly as fetchaddr's is.  On the three arms that never
   call copyout, [P' = pv_upt V]. *)
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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WaitInv.
Require Import SpecProcinit.   (* [wait_lock_addr] -- procinit is what makes it *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* kwait's own ten frame slots, plus the deepest callee below it (copyout's
   52; freeproc wants 44, sleep 22, killed 14, acquire/release/myproc 10).

   THE COPYOUT CALL GETS NO TRAP RESERVE, which is why this is a straight
   10 + 52 rather than piperead's arithmetic.  kwait is [eb]-generic and
   [trap_res false = 0] (IntrDefs.v), so the call site can offer only
   [K - 10]; there is no reserve to borrow against, and 60 leaves the
   obligation at [52 <= 50].  copyout's own budget went 50 -> 52 because
   [psz] has to outlive walkaddr / vmfault / memmove, so gcc gave it a
   callee-saved home in s11 and the frame grew to 14 slots (SpecCopyout.v). *)
Notation K_kwait := (62%nat) (only parsing).
Definition wp_kwait_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa γf γw : gname)  (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (b : bool)
    (pid : mword 32) (V : pprivate) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kwait in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_kwait <= av)%nat ->
  (* the PARKING premise: everything that sleeps needs it (SpecSched.v) *)
  eb = true ->
  (* kwait acquires wait_lock (10) and, nested under it, each pp->lock ("proc",
     11); freeproc/either_copyout reach "kmem" (13).  10 is the floor, and the
     nested acquires follow by [locks_below_union_singleton]/[locks_below_mono]. *)
  locks_below lks "wait_lock" ->
  sie_cap_gpr KT1 m av b pj -∗
  (* entered with no lock held *)
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the proc table, and the scheduler chain sleep parks into *)
  procs_inv γs -∗
  (* the running-thread bundle sleep needs *)
  (* wait_lock, and what it protects *)
  is_lock γw wait_lock_addr "wait_lock"%string <{ wait_res }> -∗
  (* copyout's lazy faulting and freeproc's kfree chain both live here *)
  kalloc_env γa None -∗
  (* the caller's own private block: copyout reads p->pagetable and p->sz *)
  proc_priv γf pj pid V -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd) (rv : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 rv ⌝ -∗
      ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KWAIT.
  Parameter wp_kwait_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (b : bool)
      (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_kwait_sconf_body γa γf γw γs j γl m av eb b pid V lks.
End KWAIT.
