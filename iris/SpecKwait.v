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
     [WaitInv.wait_res] -- all NPROC [p->parent] cells and the children
     sets beside them -- is what wait_lock
     protects, and holding it is what licenses BOTH the [ld a5,56(s1)] the
     scan runs on every slot and the [sd x0,56(s1)] that disowns the child.
     [parent] cannot live in [SchedCtx.proc_lock_res]: it is read across
     processes by a holder of wait_lock who holds no proc lock at all, and
     putting it there would make the documented lock order wait_lock ->
     p->lock unstateable.  See WaitInv.v.

   * IT MOVES THE CALLER'S CHILDREN ROW, and that is what makes a reap a
     reap rather than a store.  The row ([WaitInv.ch_frag], off the trap
     residue) is handed in at [cs] and comes back at [cs'], and the
     contract says which member left: the reap takes the reaped generation
     out of it -- out of BOTH columns of the wait-lock invariant, which is
     where "that zombie is my child" lives
     ([WaitInv.children_inv_reap]) -- and every failing arm returns it
     unmoved.  The answer names that generation, so the row's move and the
     escrow that redeems it are one statement
     ([UserChildren.wait_ans]).

   * IT REACHES A ZOMBIE'S PRIVATE BLOCK, WHICH NOTHING ELSE DOES.  The
     child's [ProcInv.proc_dormant _ ZOMBIE] comes out of the child's own
     lock through [SchedCtx.proc_slots]'s [inv_dormant] guard, and
     [SpecFreeproc.fp_of_dormant_zombie] is what turns it into freeproc's
     precondition.  That bridge is exactly the gap SpecFreeproc.v used to
     record as unwritten; closing it is what made this proof possible.

   * WHAT IT SAYS ABOUT THE RESULT IS THE REAPED CHILD'S ESCROW.  The
     return value is a sign-extended [int] ([lw] of [pp->pid] on the found
     arm, [li -1] on the three failure arms), and on the found arm it NAMES
     the generation kwait reaped: the post's [UserChildren.wait_ans] hands
     out that generation's escrow ([ChildTok.exit_tok], the payload its
     exit paid, keyed at the status this call copied out) together with the
     pid uniqueness over the caller's own children ([ChildTok.gen_uniq])
     that makes the number identify it.  Both come off the wait-lock
     invariant, which the reaper holds open across the reap
     ([WaitInv.children_inv_reap] / [children_inv_pid]).
     THE -1 ARM SAYS ONLY THAT NOTHING MOVED, and that is the code: of its
     three exits only the childless one has an empty children reading --
     the other two are a killed caller and a copyout that could not place
     the status, and both happen with children present.

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
   call copyout, [P' = pv_upt V].

   WHAT STAYS EXISTENTIAL IS A LENGTH, NOT AN IMAGE.  The only write kwait
   can make to user memory is copyout's: the found zombie's four-byte
   [xstate] at [addr], and only when [addr <> 0].  The post therefore
   carries [umem_wr (us_M U) addr d (nth_byte xw)] for some [d <= 4] and
   some four-byte STATUS WORD [xw] -- the bytes are that word's, at every
   arm, because a partial copyout still copies a prefix of it.  [xw] is the
   word the ESCROW is keyed at as well (the reaper holds both halves of
   [pp->xstate]), which is what ties the number a parent reads out of its
   own buffer to the payload it redeems.  The [addr = 0] arm, the
   no-zombie-child arm, and copyout's own failure prefix all move nothing:
   they instantiate [d := 0], where [umem_wr M addr 0 bs = M] on the nose.
   A caller reads its own untouched bytes back with
   [UserPtTree.umem_wr_lookup_out]. *)
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
Require Import RiscvModelBytes.   (* [nth_byte] -- the status word the copyout places *)
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
Require Import PidLock.   (* freeproc takes <pid_lock> around [p->pid = 0] *)
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
Definition wp_kwait_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa γp γf γw : gname)  (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (b : bool)
    (pid : mword 32) (U : ustate) (lks : gset string) (cs : gset gname) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kwait in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let addr := m !!! Regidx (mword_of_int 10 : mword 5) in
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
  is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at) -∗
  (* copyout's lazy faulting and freeproc's kfree chain both live here *)
  kalloc_env γa None -∗
  (* <pid_lock>: freeproc acquires it around [p->pid = 0] (upstream ded23f2),
     and kwait reaches freeproc when it reaps a ZOMBIE child *)
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at -∗
  (* the caller's own private block: copyout reads p->pagetable and p->sz *)
  proc_priv γf pj pid U -∗
  (* ...AND THE CALLER'S OWN CHILDREN ROW, which is what makes a reap a
     reap.  It rides the trap residue ([UsertrapRes.ut_own]) beside the
     descriptor fragments, kwait holds <wait_lock> -- the authority the row
     belongs to -- across everything it does, and the reap MOVES it: the
     reaped generation leaves the set.  The mold is sys_exit's, which
     relays the same row to kexit ([SpecKexit]). *)
  ch_frag (pv_chg (us_V U)) pj cs -∗
  wp_next b pj (fun (CID : CpuId) =>
    (* THE ONLY THING kwait WRITES IS THE FOUR-BYTE EXIT STATUS, AT [addr],
       AND ONLY WHEN [addr <> 0].  [d] is the count copyout actually placed
       ([d = 0] on the [addr = 0] arm, on the no-zombie-child arm, and on
       copyout's own failure prefix; [d <= 4] on the success arm, where
       [sizeof(pp->xstate) = 4]), and the bytes are those of ONE status
       word [xw] -- the zombie's, which is also the word the escrow below
       is keyed at.  A caller reads its own untouched bytes back with
       [UserPtTree.umem_wr_lookup_out]. *)
    ∀ (mf : regfile) (P' : uptd) (rv : mword 32) (d : nat) (xw : mword 32)
      (cs' : gset gname),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 rv ⌝ -∗
      ⌜ uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P' ⌝ -∗
      ⌜ (d <= 4)%nat ⌝ -∗
      (* ...AND A NULL DESTINATION IS NOT A DESTINATION.  kwait's own
         [addr != 0] test is the C's, so the null arm copies nothing at
         all -- which is what lets a caller passing a NULL pointer keep
         everything it held across the call.  Without this the row would
         still permit a four-byte write at address 0. *)
      ⌜ addr = (zero_reg : mword 64) -> d = 0%nat ⌝ -∗
      (* ...AND WHAT THE CALL ANSWERED, in wait's two arms
         ([UserChildren.wait_ans]): -1 and nothing moved, or the reaped
         child's pid with its ESCROW, the pid uniqueness that makes the
         number name a generation, and the caller's reading at what the
         reap left it.  THE ESCROW IS AT THE WORD THE COPYOUT PLACED:
         [xw] is the same status the window above is written from, because
         the reaper holds both halves of the zombie's [p->xstate] and the
         escrow is keyed at what that cell reads
         ([ProcDefs.proc_dormant]'s ZOMBIE arm). *)
      wait_ans rv (xstate_val xw) cs cs' -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pid
        (upd_usM (us_upt U P') (umem_wr (us_M U) addr d (fun i => nth_byte xw i))) -∗
      (* THE ROW COMES BACK AT WHAT THE REAP LEFT IT.  A reap takes ONE
         generation out of the caller's reading -- the one it reaped, and
         [WaitInv.children_inv_reap] takes it out of both columns of the
         invariant -- and every failing arm returns the set unmoved (the C
         returns before [pp->parent = 0], so nothing was reaped).  WHICH
         generation left is the answer's own [γ'], beside the escrow that
         redeems it. *)
      ch_frag (pv_chg (us_V U)) pj cs' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KWAIT.
  Parameter wp_kwait_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa γp γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (b : bool)
      (pid : mword 32) (U : ustate) (lks : gset string) (cs : gset gname),
      wp_kwait_sconf_body γa γp γf γw γs j γl m av eb b pid U lks cs.
End KWAIT.
