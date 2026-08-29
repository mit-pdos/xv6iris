(* SpecConsoleread.v -- the public interface of consoleread, stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     int consoleread(int user_dst, uint64 dst, int n) {
       uint target = n;  int c;  char cbuf;
       acquire(&cons.lock);
       while (n > 0) {
         while (cons.r == cons.w) {
           if (killed(myproc())) { release(&cons.lock); return -1; }
           sleep_prepare(&cons.r);
           release(&cons.lock);
           sleep();
           acquire(&cons.lock);
         }
         c = cons.buf[cons.r++ % INPUT_BUF_SIZE];
         if (c == C('D')) { if (n < target) cons.r--; break; }
         cbuf = c;
         if (either_copyout(user_dst, dst, &cbuf, 1) == -1) break;
         dst++;  --n;
         if (c == '\n') break;
       }
       release(&cons.lock);
       return target - n;
     }

   @ KernelSyms.consoleread = 0x80000178, 89 instructions / 274 bytes; a
   96-byte frame with ra/s0/s1/s2/s3/s4/s6/s7 saved in the prologue and s5 --
   the byte just read -- SHRINK-WRAPPED onto the paths that have one.

   THE SHAPE IS PIPEREAD'S, and not by imitation: the two are the same animal,
   a blocking read into USER memory by the running thread, under a spinlock
   that a wakeup-issuing interrupt handler also takes.  Conjunct for conjunct,
   [SpecPiperead.v] with the pipe replaced by the console:

   * [ConsoleInv.is_conslock γc] is THE WHOLE CREDENTIAL -- one persistent
     proposition, no reference, no fraction.  [cons] is a static global, so
     unlike a pipe's page it is never freed and its lock is not cancellable;
     what the lock protects is [ConsoleInv.cons_res], the 128-byte ring and
     the three index words, and nothing of it comes back out to a caller;
   * it SLEEPS, so it threads the running-thread bundle ([procs_inv]) and
     takes the hart-generic parking premise [eb = true] at [noff = 0] --
     cons.lock is the only lock it holds and sleep demands that.  The parked
     scheduler record is NOT threaded: it lives in the running proc's own
     [p->lock] ([SchedCtx.run_slot]), which sleep reaches by holding it.  The
     condition lock is dropped and re-taken by consoleread ITSELF, through
     the ordinary RELEASE / ACQUIRE contracts (SpecSleep.v's split protocol);
   * it copies out, so it takes [proc_priv_core] and [kalloc_env]
     (either_copyout reaches copyout, hence vmfault, hence kalloc) and gives
     the block back at an EXTENDED page table ([uptd_ext]), exactly as
     readi's user arm does;
   * it gives back every callee-saved register and the nesting level.

   ---- WHAT IT PROMISES ABOUT THE OUTPUT -------------------------------

   The RETURN VALUE RANGE, [-1 <= r <= n], and nothing else.  The [-1] is
   real here (unlike consolewrite's): a process killed while it waits gets
   it.  ([Z.max 0 n] rather than [n] so the statement is true at a
   non-positive request too, where the loop never runs and the answer is 0.)

   WHAT IT DOES NOT PROMISE IS WHICH BYTES ARRIVED, and that is a property of
   [ConsoleInv.cons_res] rather than of this contract: the ring's contents
   are unconstrained there because the only thing that FILLS them is
   consoleintr, which is assumed (LinkConsoleintr.v).  See ConsoleInv.v's
   header for why a coupling stated today would be an assumption in
   disguise.  What fileread's caller gets out of the call is the range above,
   which is what [SpecFileread.fileread_ret] consumes. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import ConsoleInv.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* consoleread's own frame plus its deepest callee.  It reaches
   either_copyout -> copyout -> vmfault, the same tower piperead is sized by
   (50), on top of sleep (22) and acquire/release (10); the constant is
   piperead's, which is the honest bound for "a blocking read into user
   memory". *)
Notation consoleread_stack := (70%nat) (only parsing).
Definition wp_consoleread_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname) (γc : gname)
    (m : regfile) (av : nat) (eb : bool)
    (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consoleread in
  let pj := proc_addr j in
  (* a1 = dst, the user destination the bytes are copied to *)
  let dst := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep/killed's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = 1: the destination is a USER address.  fileread's dispatch passes
     the literal 1, and this contract is only stated for that case -- the
     kernel-destination arm has no caller. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consoleread_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol).  See SpecSched.v. *)
  eb = true ->
  (* consoleread's own acquire(&cons.lock) needs every lock this hart
     already holds to rank below "cons".  The lock is released again
     before every exit (the killed early-return, the ^D/copy/'\n' breaks,
     and the [n <= 0] loop exit all release before returning), so [lks]
     itself is unchanged end to end -- none of consoleread's other callees
     (myproc, killed, sleep_prepare, sleep, either_copyout) surface a lock
     of their own through this contract. *)
  locks_below lks "cons" ->
  sie_cap_gpr KT1 m av b pj -∗
  (* noff = 0: sleep demands cons.lock be the ONLY lock held *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* THE WHOLE CREDENTIAL: cons.lock, whose resource is the ring and the
     three indices (ConsoleInv.v).  Persistent, so nothing about the console
     is threaded and nothing comes back. *)
  is_conslock γc -∗
  proc_priv_core pj pid U -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  wp_next b pj (fun (CID : CpuId) =>
    (* THE IMAGE MOVES, AND THE MOVE IS A WINDOW.  consoleread's only write
       to user memory is the loop's one-byte-per-round either_copyout,
       walking [dst] upwards, so the block comes back at the image it went
       in at WITH THE RUN [dst .. dst+d) WRITTEN and nothing else touched.
       A caller reads its own untouched bytes back with
       [UserPtTree.umem_wr_lookup_out].

       WHAT STAYS EXISTENTIAL IS A LENGTH AND THE BYTES, NOT AN IMAGE.  [d]
       is how far the loop got -- NOT pinned to [r], because a copyout that
       faults part-way may still have moved its byte before the loop broke.
       [bs] is what came out of the console ring, which no contract at this
       tier can name: the ring is the existential half of [ConsoleInv]'s
       invariant and the loop sleeps inside the read. *)
  ∀ (mf : regfile) (r : Z) (P' : uptd) (d : nat) (bs : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      (* the whole of what a device read promises: it delivered somewhere
         between "failed" and "all of it". *)
      ⌜(-1 <= r <= Z.max 0 n)%Z⌝ -∗
      ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid
        (upd_usM (us_upt U P') (umem_wr (us_M U) dst d bs)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEREAD.
  Parameter wp_consoleread_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (γc : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string),
      wp_consoleread_sconf_body γa γf γs j γlp γc m av eb pid U n b lks.
End CONSOLEREAD.
