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

   THE RETURN VALUE RANGE, [-1 <= r <= n].  The [-1] is real here (unlike
   consolewrite's): a process killed while it waits gets it.  ([Z.max 0 n]
   rather than [n] so the statement is true at a non-positive request too,
   where the loop never runs and the answer is 0.)  It is what
   [SpecFileread.fileread_ret] consumes.

   ...AND THE LEDGER: the [d] bytes the call copied out are [d] bytes the
   UART really delivered, in copy order, each with the application's
   persistent claim about the history it arrived at.
   [ConsoleInv.cons_tagged bs hs d] is the tie -- [hs !! j] ends in an
   [ObsUartIn Uart0 b] whose [ConsoleInv.cons_xlate b] IS the [j]th byte of the
   run -- and [[∗ list] h ∈ hs, riscv_rx_tag h] is the claim.  It comes
   out of the ring's coupling (ConsoleInv.v's header): the loop pops at
   [cons.r] while [cons.r != cons.w], so every byte it copies is inside
   the live range the row speaks for.  The tags are PERSISTENT, so this
   costs the ring nothing.

   THE -1 ARM IS NOT AN EXCEPTION.  A process killed mid-loop has already
   copied earlier rounds' bytes, and those bytes were tagged; the ledger
   is stated at the same [d] on every arm, so a caller need not case on
   the answer to read it.

   WHAT IS STILL NOT PROMISED is a LINE DISCIPLINE -- that what was typed
   is what is read, in the order it was typed.  The ledger says each byte
   delivered arrived at a history that ends in it; it does not order the
   histories, and it does not say the ring was not edited (C('U') and
   backspace drop bytes that were tagged).  What the read syscall's
   console receipt carries to the process is exactly this
   ([SpecFileread.console_receipt]). *)
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
Require Import WpUart.   (* [uart_inv], [cons_read_pay], [read_link]: E5's
                            console I/O boundary, fired at the final release *)
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CtxIdDefs.
Import Defs.
Local Open Scope Z_scope.

(* consoleread's own frame plus its deepest callee.  It reaches
   either_copyout -> copyout -> vmfault, the same tower piperead is sized by
   (50), on top of sleep (22) and acquire/release (10); the constant is
   piperead's, which is the honest bound for "a blocking read into user
   memory". *)
Notation consoleread_stack := (70%nat) (only parsing).
Definition wp_consoleread_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname) (γc : gname) (cn : cons_names)
    (Wd : iProp Σ)
    (m : regfile) (av : nat) (eb : bool)
    (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
    (* HOW THE CALLER PAYS (app-echo.md, lane CONS-CURSOR, C3, and the
       owner's ruling on the tokenless read).  [Some nrd] is a caller that
       holds the reader token at its own cursor; [None] is one that does not
       and pays [Wd] -- the application's supply credential -- instead.  It
       is a PARAMETER and the payment is a RESOURCE because the receipt
       names a window of the ring's stored sequence, and a post cannot name
       a number a premise hid under an existential. *)
    (ord : option nat)
    (* WHAT THE PROCESS ASKS TO BE TOLD ABOUT THE INPUT IT CONSUMED
       (app-echo.md, lane CONS-IO, milestone B, B3).  The application owns
       the console UART's accepted-input log and the sequence delivered out
       of it ([RiscvPtsto.riscv_cons_res]); a read moves the second, and it
       moves it through ONE fupd the process supplies,
       [WpUart.cons_read_pay (S gen_id) Rin], fired HERE -- at the final release, on
       the CLEAN arm, where the ring's own account of the window is still
       in hand.  [Rin ws] is what the process gets back, at the window it
       actually consumed. *)
    (Rin : list (list mobs * bv 8) -> iProp Σ) :=
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
  is_conslock cn Wd γc -∗
  (* THE CALLER'S PAYMENT.  The reader token at [Some nrd] -- the other half
     of the ring's reader cursor, which this call moves and hands back -- or,
     at [None], the price of reading without it.  A TOKENLESS READ IS LEGAL:
     the kernel cannot make console reading exclusive, because a generic
     process must be able to answer read(0,..) and the generic slot's supply
     law has to pay for it.  What it does instead is RECORD the read, and
     the record is what the token holder reads off its own receipt. *)
  cons_pay cn Wd ord -∗
  (* ...AND THE INPUT LINK IT SPENDS.  Consumed exactly once, on the clean
     arm; a call that finds the ring MARKED drops it (its [dl] is frozen
     and the caller's continuation is generic anyway). *)
  WpUart.cons_read_pay (S gen_id) Rin -∗
  (* THE CONSOLE PORT'S OWN INVARIANT, which is where the boundary's two
     resources live.  A new premise (ruling F6): the fire opens [uartN
     Uart0] inside the WP, and neither [is_conslock] nor [console_caps]
     reaches this function.  fileread supplies it from its own [dev_inv]
     and the tie [cn_uart fsc_cons = fsc_uart]. *)
  WpUart.uart_inv Uart0 (cn_uart cn) -∗
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
       [bs] is what came out of the console ring, which this contract does
       not spell out byte for byte: the ring is the existential half of
       [ConsoleInv]'s invariant and the loop sleeps inside the read.  What
       it DOES say about those bytes is the ledger below -- each one is a
       byte the UART delivered, translated by [ConsoleInv.cons_xlate], with
       its tag. *)
  ∀ (mf : regfile) (r : Z) (P' : uptd) (d dc cur : nat) (bs : nat -> bv 8)
      (hs : list (list mobs)) (sl : list (list mobs * bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      (* the whole of what a device read promises: it delivered somewhere
         between "failed" and "all of it". *)
      ⌜(-1 <= r <= Z.max 0 n)%Z⌝ -∗
      (* ...AND A NEGATIVE ANSWER IS A KILL (lane KILL-PAY, K4(b)(ii)).
         There is exactly ONE exit that returns -1: the [killed(myproc())]
         test inside the wait loop, which fires only against a NONZERO
         [p->killed].  IT USED TO CARRY THE APPLICATION'S KILL CREDENTIAL
         (KILL-PAY K4(b)), and that row is GONE (lane SELF-KILL, §4b'):
         [SchedCtx]'s killed row is per-incarnation and LINEAR now -- the
         payment for THIS incarnation's death -- so a reader can neither
         copy it out nor relay it, and [killed()] reports the flag and
         nothing else.  Nothing consumed the relayed credential
         ([UkSh.ush_read_ans]'s minus-one arm was its only destination and
         only [ush_read_ans_pos] is spent), so the row is dropped rather
         than weakened to something vacuous. *)
      (* ...AND A NEGATIVE ANSWER HANDS THE READER THE KILL FACT (lane
         TRAP-ROWS, T2).  The one exit that returns -1 is the
         [killed(myproc())] test inside the wait loop; it fires only
         against a NONZERO [p->killed], and [killed()] hands the caller
         this incarnation's one-shot at that flag
         ([SchedCtx.kill_paid_shot]).  The shot is PERSISTENT, so relaying
         it costs the arm nothing and the reader keeps it -- which is what
         lets usertrap's second killed check refute its own resume branch,
         and hence what makes "read never answers -1 to user mode" a fact
         of the kernel rather than a discipline. *)
      (⌜(r < 0)%Z⌝ -∗ ChildTok.kill_shot (pv_gen (us_V U))) -∗
      ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ -∗
      (* ...AND ON A NON-NEGATIVE RETURN THE RUN IS EXACTLY THAT LONG: the
         copy is one byte per round and a failing one-byte either_copyout
         moves none, so the loop breaks having delivered exactly the
         [target - n] it returns.  The -1 arm keeps only the bound --
         consoleread's [killed] test is INSIDE its copy loop -- but that
         arm is NOT OBSERVABLE FROM USER MODE: -1 is returned only when the
         process was killed, and a killed process is never resumed in user
         mode.  The bound is kept because this contract is stated for the
         kernel caller, which does see the arm. *)
      ⌜(0 <= r)%Z -> r = Z.of_nat d⌝ -∗
      (* ...AND WHERE THE REQUEST WAS FILLED, NOTHING EXTRA WAS POPPED
         (app-echo.md, lane CONS-ROWS, B1).  The two exits that pop a byte
         and do not deliver it both fire with the request still open: the
         [C('D')] arm runs INSIDE the [n > 0] test, and the copy-out
         failure breaks having delivered [target - n] with [n] still
         positive.  So a call whose run is as long as its request -- and
         that includes the empty request, whose loop never runs at all --
         moved the cursor by exactly the run.  Without this row a one-byte
         reader that got its byte still cannot rule out that the call ate
         a second one, and the byte past the request is one it does not
         own, so it cannot refute the swallow arm's copy-out reason
         either. *)
      ⌜Z.of_nat d = Z.max 0 n -> dc = d⌝ -∗
      (* ...AND A NON-NEGATIVE RETURN THAT DELIVERED NOTHING AGAINST A
         POSITIVE REQUEST DID POP ONE (B4).  The loop is entered ([n > 0]),
         so it reached a byte; the exits that leave the run empty are the
         [C('D')] arm with nothing delivered and the first byte's copy-out
         failure, and both pop.  ([killed] also exits with an empty run,
         which is why the guard [0 <= r] is here: that arm returns -1 and
         pops nothing.)  A caller reading one byte at a time reads this
         row as "r = 0 means the byte is gone", refutes
         [ConsoleInv.cons_swallow]'s left arm with it, and takes the
         reason off the right. *)
      ⌜(0 <= r)%Z -> d = 0%nat -> (0 < n)%Z -> dc = (d + 1)%nat⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      (* THE LEDGER: one tag per byte copied, in copy order, tied to the
         run's own source function.  Stated as a PURE clause beside a
         persistent big-op rather than as one existential proposition, so
         a caller that wants only the bytes can drop the tags by framing
         and a caller that wants only the tie never opens an ∃. *)
      ⌜cons_tagged bs hs d⌝ -∗
      ([∗ list] h ∈ hs, riscv_rx_tag h) -∗
      (* ...AND THE WINDOW (app-echo.md, lane CONS-CURSOR, C3), UNDER THE
         SAME DISJUNCTION AS THE POSITION.  On the left arm the [d] bytes
         are the ring's stored sequence at positions [cur .. cur + d), with
         their histories; [sl] is a LOWER BOUND on that sequence, so two
         reads by the same holder of the token hand back two bounds that
         agree on every index both have and the second window begins exactly
         where the first ended; [cons_chain sl] is the order along it; and
         the cursor moved by [dc], which is [d] or ONE MORE -- two of the
         loop's exits pop a byte and do not deliver it (the [C('D')] arm
         whose [cons.r--] push-back is skipped because nothing has been
         delivered yet, and the [either_copyout == -1] break, which has
         already advanced [cons.r] past the byte it failed to copy).

         WHY IT IS NOT UNCONDITIONAL.  The copy loop SLEEPS -- it drops
         cons.lock at [cons.r == cons.w] and takes it back afterwards -- and
         the kernel cannot exclude a second reader across that gap: reading
         the console without the token is paid for with
         [ConsoleInv.cons_dirty_cred], which is PERSISTENT
         ([ConsoleInv.cons_acc]'s second disjunct, and the generic slot's
         supply law is the reason it has to be), so arbitrarily many
         processes can be inside consoleread at once.  A reader that pops
         while this call sleeps moves the ring's committed count without
         moving the cursor, so this call's bytes are no longer consecutive
         and its own advance is no longer [d] or [d+1].  What that reader
         DOES leave behind is the ring's marker, and the marker is the
         credential: so contiguity is promised exactly where the position
         is, and the right arm hands back the credential that sends the
         caller's continuation generic instead.

         [cons_stored_lb] and [cons_tagged] STAY UNCONDITIONAL: a bound on
         the committed sequence and the per-byte tags hold on every arm --
         every byte delivered really did arrive at its history -- and it is
         only their CONSECUTIVENESS that a concurrent reader can take
         away.

         ...AND THE SWALLOWED BYTE IS NAMED (app-echo.md, "SH-LINE PHASE 2
         -- THE SWALLOWED BYTE"; lane CONS-SWALLOW).  [dc = d + 1] is a byte
         this call popped and did not deliver, and
         [ConsoleInv.cons_swallow] says WHICH byte and WHY: its history is
         the next element of the committed sequence, it carries the input
         tag, and the reason is the one of the code's two exits that fired
         -- the byte was [C('D')] with nothing delivered yet, or its
         copy-out faulted, which is [SpecCopyout.copyout_wrote]'s clause at
         this call's own destination and the entry table.  Without it a
         one-byte reader cannot tell a delivered line from a line with a
         hole in it. *)
      cons_stored_lb cn sl -∗
      (⌜cons_window sl cur d bs hs⌝ ∗ ⌜cons_chain sl⌝
         ∗ cons_swallow cn
             (~ uva_wmapped (pv_upt (us_V U))
                  (uint (add_vec_int dst (Z.of_nat d)))) sl d dc
         (* ...AND THE BOUNDARY'S ANSWER (lane CONS-IO, milestone B, B3).
            On the clean arm the call fired the process's link at the
            window it CONSUMED -- [dc] entries, delivered or swallowed --
            and hands back what the process asked for at that window.
            [sl'] and not [sl] (ruling F5): at [dc = d + 1] the swallowed
            byte is one past [sl]'s end, so the row is stated at the bound
            [cons_swallow] extends to. *)
         ∗ (∃ (sl' ws : list (list mobs * bv 8)),
              cons_stored_lb cn sl' ∗ ⌜sl `prefix_of` sl'⌝ ∗
              ⌜length sl' = (cur + dc)%nat⌝ ∗ ⌜length ws = dc⌝ ∗
              ⌜forall j : nat, (j < dc)%nat ->
                 ws !! j = sl' !! (cur + j)%nat⌝ ∗
              Rin ws)
       (* ...AND ON THE MARKED ARM, WHERE THE BYTES CAME FROM (lane seccomp
          S2k, seccomp.md 10.12).  The window is gone -- a tokenless reader
          popped in one of this call's sleeps -- but every pop is at the
          ring's cursor, the byte it takes is the stored sequence's element
          there, and the cursor is never below the reader's own position.
          So the [j]th delivered byte sits in [sl] at SOME position at or
          after [cur] ([ConsoleInv.cons_placed]), with its history in the
          ring's own era [cn_era cn], along the stored order
          [cons_chain sl].  [cur] is the position this call reports: a
          token holder's own [n0] on both arms ([cons_out] says so on the
          marked arm too), and nothing at all for a tokenless caller.  The
          positions are NOT promised to increase with [j] -- the ring keeps
          no witness that its cursor is monotone across a release -- and
          nothing is fired. *)
       ∨ cons_dirty_cred Wd ∗ ⌜cons_chain sl⌝
           ∗ ⌜cons_placed sl cur (cn_era cn) d hs⌝
           (* ...AND THE SWALLOWED BYTE, PLACED THE SAME WAY (lane seccomp
              S2k3): at [dc = d + 1] the call popped one byte it did not
              deliver, and it sits in [sl] at or after [cur] with its tag
              and the ring's era ([ConsoleInv.cons_swallow_placed]). *)
           ∗ cons_swallow_placed sl cur (cn_era cn) d dc) -∗
      cons_out cn Wd ord cur dc -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid
        (upd_usM (us_upt U P') (umem_wr (us_M U) dst d bs)) -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type CONSOLEREAD.
  Parameter wp_consoleread_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (γc : gname) (cn : cons_names) (Wd : iProp Σ)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
      (ord : option nat)
      (Rin : list (list mobs * bv 8) -> iProp Σ),
      wp_consoleread_sconf_body γa γf γs j γlp γc cn Wd m av eb pid U n b lks
        ord Rin.
End CONSOLEREAD.
