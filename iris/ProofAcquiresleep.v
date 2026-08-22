(* ProofAcquiresleep.v -- acquiresleep() over the SIE-agnostic sconf world.

   acquiresleep(slk) @ 0x80003f02: the 32-byte 4-register frame (ra/s0/s1/s2)
   trade, then s1:=slk, s2:=&slk->lk (= sl_lk slk), acquire(&slk->lk); then the
   condition-variable WAIT LOOP

      while (slk->locked) {
        sleep_prepare(slk);      /* +0x1c mv a0,s1  ; +0x1e jal  */
        release(&slk->lk);       /* +0x22 mv a0,s2  ; +0x24 jal  */
        sleep();                 /* +0x28 jal                    */
        acquire(&slk->lk);       /* +0x2c mv a0,s2  ; +0x2e jal  */
      }

   over the inner spinlock, then slk->locked:=1, slk->pid:=myproc()->pid,
   release(&slk->lk), epilogue.

   THE SLEEP PROTOCOL IS SPLIT (SpecSleep.v's header): the caller registers
   its channel under [sleep_prepare], drops the condition lock ITSELF, parks
   in the parameterless [sleep], and re-takes the lock ITSELF.  So the body of
   one iteration now contains four calls rather than one, and the trip through
   [release] .. [acquire] is the stretch where the resource index is [eb]
   rather than the literal [false]: the loop invariant carries [trap_csrs] and
   [cpu_claim pj] index-free, [arm_pay_ext_split] hands the pay half to the
   interior release and the [_ext] complement to sleep (which is exactly the
   pair sleep's contract asks for), and [arm_pay_ext_join] puts them back
   together after the re-acquire.

   The retry loop is UNBOUNDED (sleep may never see the lock free), so it is
   proved by iLöb over a loop lemma whose back edge (the c.bnez after the
   post-sleep reload) closes against the later-handing taken leaf
   [wp_cbnez_taken_s_sconf].  The two [lw]/branch sites (+0x18 beqz at entry,
   +0x32 bnez in-loop) both destruct [sl_res]: the FREE arm exits (beqz taken /
   bnez falls through), the HELD arm loops (beqz falls / bnez taken).

   sleep_prepare's "chan <> 0" premise is discharged INSIDE the loop, not
   demanded of acquiresleep's caller: the invariant owns the sleeplock's own
   word cell [slk ↦₄ _], and a [↦ₘ] byte carries [addr_is_ram] of its
   address, which is [0x80000000 <= slk] ([asl_word4_nonzero] below).

   THE HART-GENERIC PROTOCOL, IN THE [wp_next] FORM.  Every leaf and every
   callee hands its continuation back through [wp_next b p (fun CID => ...)],
   so the resumed hart arrives as an ordinary binder and every resource in the
   continuation is automatically about it -- no [(CID := h)] annotations and,
   since the SIE ghost went canonical per hart, no [g] to thread at all.  What
   is left to think about is WHERE the hart can actually move:

     * the entry index is DERIVABLY [true] ([CpuOwn.cpu_own_forces_on]: level 0
       with an enabled base has no [b = false] instance), so the prologue, the
       acquire crossing, the post-release epilogue and acquiresleep's own
       [wp_next] obligation are all hart-GENERIC;
     * from acquire's return to release's call the lock is HELD, i.e. the index
       is the literal [false], so every leaf in that stretch is a plain
       [rewrite wp_next_off] and the hart is pinned -- that is most of the
       function;
     * the genuine hart changes inside the wait loop are the interior
       release (whose exit index is [eb], because it pops back to level 0)
       and the park: [sleep]'s
       crossing index is the literal [true] because a [swtch] moves the hart
       with interrupts off.  Because the park is INSIDE the retry loop, it is
       the LOOP INVARIANT that has to survive a hart change.

   [asl_loop] / [asl_exit] are therefore themselves [wp_next]s, anchored at the
   whole function's entry hart [CID0] (the shape the porting guide recommends
   for a loop): forwarding one across an iteration is the identity, and only a
   USE costs a [wp_next_chain].  The three straight-line stretches stay their
   own lemmas -- [asl_exit_body] (+0x36..ret), [asl_post_sleep_body]
   (+0x32..the branch) and [asl_loop_body] (+0x1c..the sleep call) -- each with
   its OWN ambient [`{GEN : GenId} `{CID : CpuId}] plus the anchor [CID0] and the one chained
   equality that links them.  The anchor is taken at type [CPU] rather than
   [CpuId] on purpose: it must NOT be an instance candidate, or it would
   compete with the lemma's ambient hart.

     * [asl_regs] is now hart-FREE: [HartTp.tp_pin] pins tp to the hart that
       owns the register file, so no map ever observes its tp slot and the
       old [cid_word_of h] conjunct (and with it the [callee_saved_notp]
       family) is gone.  A same-hart hop and a parking hop are the same
       [callee_saved] transport, [asl_regs_cs].
     * the trap CSRs ride the loop: acquire(&slk->lk) mints
       [arm_pay 0 eb _], sleep carries it across the park and hands it
       back, and the final release(&slk->lk) spends it.  acquiresleep is
       therefore trap-CSR-balanced and its own contract does not mention them.
     * the parked-scheduler record is NOT threaded here at all.  It lives in
       the running proc's own [p->lock] ([SchedCtx.run_slot]), which sleep
       reaches by holding that lock; acquiresleep never parks itself and so
       never names it.
     * The panic credentials are what acquire and sleep take; acquiresleep has no
       panic arm of its own after the park.

   THE HOLDER DEPOSIT, AND THE THREE PIECES THE FILE IS NOW IN.
   [SleepLock.sl_res_gen]'s HELD arm holds a resource the acquirer brought --
   [H q], the deposit -- because nothing weaker can ever be refuted from
   outside (SleepLock.v's header carries the frame argument).  So every
   stretch that can reach the [locked := 1] store threads [H q], the wait
   loop carries both it and the lock's own [sl_dep], and the exit stretch
   re-targets the free arm's junk fraction to the caller's [q]
   ([sl_free_retarget]) so that what stays in the lock is pinned to the token
   the call walks away with.

   That let the NESTED body be split so a contract can REFUTE its wait loop
   instead of proving it:

     * [asl_nested_core] -- everything but the wait loop, with the
       LOCKED arm handed off to whatever [asl_nloop] the caller supplies.
       Nothing in it reaches [sleep_prepare], so its held-set premise is down
       to FRESHNESS ("sleep lock" ∉ lks) -- no rank bound anywhere.
     * [wp_acquiresleep_nb_sconf] over it, which supplies a REFUTATION of
       the loop out of the caller's [slh_auth γt None].  There is no longer
       a BLOCKING nested contract to supply the loop itself: it reached
       [sleep] at noff >= 2, where sched panics, and iput -- its only
       consumer -- takes the non-blocking one now.  So the only acquiresleep
       that can sleep is the level-0 one, at [cpu_own 0].

   [asl_nexit] / [asl_nloop] carry a ROUTED resource [X], and it is not
   decoration: the entry test picks exactly one arm, and the non-blocking
   instance needs its counting authority on BOTH -- to refute the locked arm,
   and to hand back on the free one.  A static split is impossible, so the
   core takes [X] and routes it.

   A functor over ACQUIRE / RELEASE / MYPROC / SLEEP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes KernelText WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import KernelRvcDecode.
Require Import WpSmodeIntr.
Require Import ProcGeom.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpLock.
Require Import SleepLock.
Require Import CodeSleeplock.
Require Import SpecAcquire SpecRelease SpecMyproc SpecSleep SpecSleepPrepare.
Require Import SpecAcquiresleep.
Require Import ProcDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  The loop/exit register-map invariant.  HART-FREE: tp is pinned to     *)
(*  whichever hart owns the register file ([HartTp]), so it is not a      *)
(*  conjunct here and a park needs no separate transport.                 *)
(*                                                                        *)
(*  s1 = slk, s2 = sl_lk slk, sp = the pushed frame base, and s3..s11     *)
(*  preserved from the entry map [m].                                      *)
(* ===================================================================== *)
Definition asl_regs (m M : regfile) (slk spd : mword 64) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = slk /\
  M !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk /\
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

(* ANY hop -- a leaf write, a non-parking callee, or the park itself.  The
   park used to need its own [callee_saved_notp] twin; with tp out of the
   relation the two coincide. *)
Lemma asl_regs_cs (m M1 M2 : regfile) (slk spd : mword 64) :
  callee_saved M1 M2 -> asl_regs m M1 slk spd -> asl_regs m M2 slk spd.
Proof.
  intros Hcs Ha. unfold asl_regs in *.
  destruct Ha as (A&B&C&E&F&G&H&I&J&K&L&N).
  repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact H.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact I.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). exact J.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). exact K.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). exact L.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). exact N.
Qed.

(* ===================================================================== *)
(*  "THE SLEEPLOCK'S ADDRESS IS NOT NULL", OUT OF THE CELL ITSELF.        *)
(* ===================================================================== *)
(* sleep_prepare(chan) panics on a zero channel, so its contract takes
   [chan <> 0] as a premise -- and acquiresleep passes [slk], which its own
   contract never constrains.  It does not have to: the wait loop OWNS the
   sleeplock word [slk ↦₄ _], every [↦ₘ] byte inside it records
   [addr_is_ram] of its own address ([RiscvPtsto.mem_pointsto]'s third
   conjunct, at the IDENTITY address given by its fourth), and RAM starts at
   [ram_base = 0x80000000].  So the premise is discharged where the resource
   is, and no caller of acquiresleep has to carry it. *)
Lemma asl_word4_nonzero `{!riscvGS Σ} (a : mword 64) (dq : dfrac) (w : mword 32) :
  a ↦₄{dq} w ⊢ ⌜eq_vec a (zero_reg : mword 64) = false⌝.
Proof.
  iIntros "H".
  iDestruct (word4_pointsto_bytes with "H") as "Hbs".
  iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "Hb0".
  { rewrite lookup_seq_lt; [reflexivity | lia]. }
  iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(_ & _ & %Hram & %Hid & _)".
  iPureIntro.
  rewrite Hid pa_add_0 in Hram.
  apply eq_vec_false_iff. intros Heq.
  rewrite Heq in Hram.
  assert (Hz : uint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  unfold addr_is_ram, ram_base, ram_size in Hram. rewrite Hz in Hram. lia.
Qed.

Section AslProps.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* The shared exit-path continuation (control at +0x36), and the wait-loop
     invariant (control at +0x1c).  Both are [wp_next]s ANCHORED at the
     function's entry hart [CID0]: the park inside the loop means either can
     be entered at a hart nobody knew about when it was established, and a
     [wp_next] is exactly the proposition that survives that.  There is NO
     section [Context {CID : CpuId}] here, so the [fun CID => ...] binder is
     the only hart in scope inside the body and every resource resolves at
     it automatically. *)
  Definition asl_exit `{GEN : GenId} (CID0 : CPU)
       (γs : list gname) (j : nat)
      (γl γsl : gname) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (pidv : mword 32)
      (av : nat) (Vpr : pprivate) (slk spd sp0 : mword 64)
      (eb : bool) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ asl_regs m M slk spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      (* the free arm's holder-shaped pair: the idle token AND the pid field
         at 0, which is what [SleepLock.sl_free_hold] is (the field rides
         inside [sleeplocked_q] now, so it is no longer a row of its own). *)
      locked γl cpu_id -∗ sl_free_hold γsl slk -∗ H q -∗ R -∗
      slk ↦₄ (mword_of_int 0 : mword 32) -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* HELD: the sleeplock's inner "sleep lock"-rank spinlock is taken
         while inside this stretch (it is released by the [+0x44 jal
         release] this covers) -- [lks] itself is the OUTER set, matching
         what this stretch's own continuation ([Hcont], threaded straight
         through from the caller) hands back once that release fires. *)
      cpu_own 1 eb (proc_addr j) false ({["sleep lock"]} ∪ lks) -∗
      trap_csrs KT1 -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr KT1 M (trap_res eb + (av - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.acquiresleep + 0x36)) -∗
      WP (Loop : expr riscv_lang)))%I.

  Definition asl_loop `{GEN : GenId} (CID0 : CPU)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (pidv : mword 32)
      (av : nat) (Vpr : pprivate) (slk spd sp0 : mword 64)
      (eb : bool) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ asl_regs m M slk spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked γl cpu_id -∗
      (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝) -∗
      sl_dep γsl H -∗ H q -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* same convention as [asl_exit]: [lks] is the OUTER set, this loop
         iteration is entered still HOLDING "sleep lock". *)
      cpu_own 1 eb (proc_addr j) false ({["sleep lock"]} ∪ lks) -∗
      trap_csrs KT1 -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr KT1 M (trap_res eb + (av - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.acquiresleep + 0x1c)) -∗
      asl_exit CID0 γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks -∗
      WP (Loop : expr riscv_lang)))%I.

  (* ---- THE NESTED PAIR: the same two anchors (control at +0x36 and at
     +0x1c), for the [cpu_own (S n)] contract.  Three differences, all
     forced:

       * NO [wp_next] and no anchor hart.  A spinlock is held from entry to
         exit, so the index is the literal [false] everywhere and no leaf,
         callee or park can move the hart -- including the interior release,
         which pops to [S n] and therefore re-enables nothing.
       * the level is [S (S n)] (the sleeplock's inner spinlock on top of
         the caller's), and what travels between the interior release and
         the interior acquire is the ordinary [arm_pay (S n) eb pj] the
         pair hands back and forth -- NOT the [trap_csrs]/[cpu_claim] pair,
         which only a level-0 park needs.
       * the loop is REACHABLE and REAL.  It used to be dead: sleep with a
         lock held was stated as a divergence.  The split protocol's sleep
         parks only when [p->chan] is still armed, and nothing can rule out
         a wakeup landing in the window (SpecSleep.v's header), so the
         locked branch is an honest Löb loop -- a thread that keeps being
         woken and keeps finding the sleeplock taken. *)
  Definition asl_nexit `{GEN : GenId} `{CID : CpuId}
      (γl γsl : gname) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp) (X : iProp Σ)
      (m : regfile) (j : nat) (pidv : mword 32)
      (av : nat) (Vpr : pprivate) (slk spd sp0 : mword 64)
      (eb : bool) (n : nat) (lks : gset string) : iProp Σ :=
    (∀ (M : regfile),
      ⌜ asl_regs m M slk spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked γl cpu_id -∗ sl_free_hold γsl slk -∗ H q -∗ X -∗ R -∗
      slk ↦₄ (mword_of_int 0 : mword 32) -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* HELD, same convention as [asl_exit]: [lks] is the OUTER set, this
         stretch is entered still holding "sleep lock" (released by the
         [+0x44 jal release] it covers). *)
      cpu_own (S (S n)) eb (proc_addr j) false ({["sleep lock"]} ∪ lks) -∗
      arm_pay KT1 (S n) eb (proc_addr j) -∗
      sie_cap_gpr KT1 M (av - 4)%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.acquiresleep + 0x36)) -∗
      WP (Loop : expr riscv_lang))%I.

  Definition asl_nloop `{GEN : GenId} `{CID : CpuId}
      (γl γsl : gname) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp) (X : iProp Σ)
      (m : regfile) (j : nat) (pidv : mword 32)
      (av : nat) (Vpr : pprivate) (slk spd sp0 : mword 64)
      (eb : bool) (n : nat) (lks : gset string) : iProp Σ :=
    (∀ (M : regfile),
      ⌜ asl_regs m M slk spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked γl cpu_id -∗
      (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝) -∗
      sl_dep γsl H -∗ H q -∗ X -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* HELD, same convention as [asl_loop]: [lks] is the OUTER set, this
         loop iteration is entered still holding "sleep lock". *)
      cpu_own (S (S n)) eb (proc_addr j) false ({["sleep lock"]} ∪ lks) -∗
      arm_pay KT1 (S n) eb (proc_addr j) -∗
      sie_cap_gpr KT1 M (av - 4)%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.acquiresleep + 0x1c)) -∗
      asl_nexit γl γsl R H q X m j pidv av Vpr slk spd sp0 eb n lks -∗
      WP (Loop : expr riscv_lang))%I.

End AslProps.

(* ===================================================================== *)

Module AcquiresleepProof (Acquire : ACQUIRE) (Release : RELEASE) (Myproc : MYPROC)
                         (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) : ACQUIRESLEEP.

(* register disequality guard (perf rule): unify settles convertibility
   cheaply, so [discriminate] only ever runs on a genuine miss. *)
Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

(* ===================================================================== *)
(*  THE STRAIGHT-LINE STRETCHES.  Each has its OWN ambient hart binder     *)
(*  [`{GEN : GenId} `{CID : CpuId}] plus the function's entry anchor [CID0 : CPU] and the *)
(*  chained equality that links the two, which is what lets it use the     *)
(*  [wp_next]-shaped [asl_loop] / [asl_exit] / [Hcont] at its own hart.    *)
(* ===================================================================== *)
Section AslBodies.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* ---- the exit path: +0x36 (locked:=1) .. +0x52 (c.ret) ---- *)
  Lemma asl_exit_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU) (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m M : regfile) (pidv : mword 32) (av : nat) (Vpr : pprivate)
      (slk spd sp0 : mword 64) (eb : bool) (lks : gset string) :
    let pj := proc_addr j in
    (26 <= av)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    asl_regs m M slk spd ->
    (* [lks] is the OUTER set (see [asl_exit]'s header note); this is what
       lets the [Hcont]-shaped continuation below be handed the CALLER's own
       [Hcont] unmodified. *)
    locks_below lks "sleep lock" ->
    kernel_text -∗
    is_sleeplock_gen γl γsl slk s R H -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked γl cpu_id -∗ sl_free_hold γsl slk -∗ H q -∗ R -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["sleep lock"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (av - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.acquiresleep + 0x36)) -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf ⌝ -∗
        sie_cap_gpr KT1 mf av eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        sleeplocked_q γsl q slk pidv -∗
        R -∗
        proc_priv_bare pj pidv Vpr -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hav Hanch Hspd Hsp0 Hasl Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    destruct Hasl as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hslk Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HR Hw Hpid Hown Htc Hclm Hcg Hpc Hcont".
    (* THE DEPOSIT'S GHOST STEP: the free arm's fraction is junk, so re-target
       it to the caller's own [q].  What stays behind in the lock is then
       pinned to the token this call walks away with, and releasesleep gives
       the caller back exactly [H q]. *)
    iMod (sl_free_retarget γsl slk q with "Hstok") as "[Hstok Hha]".
    (* the pid field, out of the re-targeted token for the [c.sw a5,40(s1)]
       below and back in at [pidv] -- which is what a holder walks away with *)
    iDestruct (sleeplocked_q_pid with "Hstok") as "[Hspid Hstokback]".
    (* the four saved-slot addresses, in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x36 c.li a5,1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              M (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_36 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M) with E1.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E1 upd_ne; [ exact Hs1 | reg_neq ]).
    (* +0x38 c.sw a5,0(s1) : slk->locked := 1 *)
    assert (Hlw0 : add_vec (rget E1 (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rgne. rewrite HE1s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x38)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) E1 (trap_res eb + (av - 4))%nat (mword_of_int 0 : mword 32) false
              with "Hcg Hpc [] [Hw]").
    { iApply (asl_38 with "Htext"). }
    { iEval (rewrite Hlw0). iExact "Hw". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hw".
    iEval (rewrite Hlw0) in "Hw".
    assert (Hsv1 : trunc32 (rget E1 (mword_of_int 15 : mword 5)) = (mword_of_int 1 : mword 32)).
    { rgne. rewrite /E1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hsv1) in "Hw".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a jal ra,myproc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x3a)) (mword_of_int 1 : mword 5) (mword_of_int 2087204 : mword 21)
              E1 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_3a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4)]> E1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4)]> E1) with E2.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) (sign_extend' 64 (mword_of_int 2087204 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HE2ra : E2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4) by (rewrite /E2; apply upd_eq).
    iApply (Myproc.wp_myproc_sconf E2 (trap_res eb + (av - 4))%nat 1%nat eb pj false _
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hown Htext Hpc").
    iApply wp_next_off_intro.
    iIntros (ms_m mfm) "%Hms_m Hcg Hown Hpc %Hmp".
    destruct Hmp as (Hmp_cs & Hmp_a0).
    assert (Hpc3e : ret_pc (E2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x3e)) by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3e) in "Hpc".
    assert (Hmfma0 : mfm !!! Regidx (mword_of_int 10 : mword 5) = pj) by exact Hmp_a0.
    (* +0x3e c.lw a5,48(a0) : a5 := myproc()->pid *)
    assert (Hppid : add_vec (rget mfm (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")))) = p_pid pj).
    { rgne. rewrite Hmfma0. rewrite /p_pid.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) : mword 64)
        with (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      reflexivity. }
    (* [p->pid] is READ here, so this one load does need the field
       itself.  It is BORROWED out of the caller's [proc_priv_bare]
       block for the length of the load and handed straight back a
       few lines below: the contract, and every chain threading
       through it, passes the whole block around, never a loose
       quarter of the cell. *)
    iDestruct (proc_priv_bare_pid with "Hpid") as "[Hpidq Hpidbk]".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x3e)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) mfm (trap_res eb + (av - 4))%nat pidv false (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hpidq]").
    { iApply (asl_3e with "Htext"). }
    { iEval (rewrite Hppid). iExact "Hpidq". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hpidq".
    iEval (rewrite Hppid) in "Hpidq".
    iDestruct ("Hpidbk" with "Hpidq") as "Hpid".
    set (E3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm) with E3.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HmfmS1 : mfm !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HE1s1. }
    assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E3 upd_ne; [ exact HmfmS1 | reg_neq ]).
    (* +0x40 c.sw a5,40(s1) : slk->pid := pidv *)
    assert (Hspidaddr : add_vec (rget E3 (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")))) = sl_pid slk).
    { rgne. rewrite HE3s1. rewrite /sl_pid.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) : mword 64)
        with (sign_extend' 64 (mword_of_int 40 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      reflexivity. }
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x40)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) E3 (trap_res eb + (av - 4))%nat (mword_of_int 0 : mword 32) false
              with "Hcg Hpc [] [Hspid]").
    { iApply (asl_40 with "Htext"). }
    { iEval (rewrite Hspidaddr). iExact "Hspid". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hspid".
    iEval (rewrite Hspidaddr) in "Hspid".
    assert (Hsvpid : trunc32 (rget E3 (mword_of_int 15 : mword 5)) = pidv).
    { rgne. rewrite /E3 upd_eq. apply trunc32_sext. }
    iEval (rewrite Hsvpid) in "Hspid".
    iDestruct ("Hstokback" $! pidv with "Hspid") as "Hstok".
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 c.mv a0,s2 : a0 := sl_lk slk *)
    assert (HmfmS2 : mfm !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /E1 upd_ne; [ exact Hs2 | reg_neq ]. }
    assert (HE3s2 : E3 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk) by (rewrite /E3 upd_ne; [ exact HmfmS2 | reg_neq ]).
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              E3 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_42 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3) with E4.
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 2083970 : mword 21)
              E4 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_44 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4)]> E4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4)]> E4) with E5.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 2083970 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4) by (rewrite /E5; apply upd_eq).
    assert (HE5a0 : E5 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. rewrite add_vec_zero_l. exact HE3s2. }
    (* re-close sl_res in the HELD state (word = 1) *)
    iDestruct (sl_res_close_held_q γsl slk R H (mword_of_int 1 : mword 32) q ltac:(vm_compute; reflexivity) with "Hw Hha HHq") as "HRc".
    assert (Hrel_lka : add_vec (E5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = sl_lk slk).
    { rewrite HE5a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    (* SPLIT AT THE INDEX: release takes [arm_pay 0 eb pj] -- the pair at
       [eb = true], [emp] at [eb = false] -- and the complement rides out to
       the caller, which is what makes this contract index-generic. *)
    iDestruct (arm_pay_ext_split eb _ with "Htc Hclm") as "[Hpay Hext]".
    iApply (Release.wp_release_sconf KT1 γl (sl_lk slk) "sleep lock"%string (sl_res_gen γsl slk R H) E5
              0%nat eb pj (av - 4)%nat
              ({["sleep lock"]} ∪ lks)
              Hrel_lka ltac:(lia)
              with "Hcg Htext Hpc [] Htok HRc Hown Hpay").
    { iApply (is_sleeplock_gen_lock with "Hslk"). }
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hrelcs Hown".
    (* asl_exit_body's own [lks] is OUTER: the set release hands back
       collapses to it, matching [Hcont]'s expectation unmodified. *)
    assert (Hsetback : ({["sleep lock"]} ∪ lks) ∖ {["sleep lock"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (Hpc48 : ret_pc (E5 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x48)) by (rewrite HE5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc48) in "Hpc".
    (* ===== EPILOGUE (0x3a..0x44): restore ra/s0/s1/s2, frame pop, ret =====
       release exits at [outb = eb], so THIS stretch is hart-generic
       again: one fresh binder per leaf, chained at the end. *)
    pose proof Hrelcs as Hrelcs2.
    assert (HmfmSp : mfm !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hmp_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /E1 upd_ne; [ exact Hsp | reg_neq ]. }
    assert (HE5csp : E5 !!! Regidx csp_rs1 = spd).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq]. exact HmfmSp. }
    assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HE5csp. }
    (* +0x48 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x48)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr24]").
    { iApply (asl_48 with "Htext"). }
    { iEval (rewrite HmrelSp Hb1). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite HmrelSp Hb1) in "Hr24".
    set (Q3a := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with Q3a.
    assert (HQ3asp : Q3a !!! Regidx csp_rs1 = spd) by (rewrite /Q3a upd_ne; [ exact HmrelSp | reg_neq ]).
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4a)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q3a (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr16]").
    { iApply (asl_4a with "Htext"). }
    { iEval (rewrite HQ3asp Hb2). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HQ3asp Hb2) in "Hr16".
    set (Q3c := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a) with Q3c.
    assert (HQ3csp : Q3c !!! Regidx csp_rs1 = spd) by (rewrite /Q3c upd_ne; [ exact HQ3asp | reg_neq ]).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4c)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q3c (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr8]").
    { iApply (asl_4c with "Htext"). }
    { iEval (rewrite HQ3csp Hb3). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HQ3csp Hb3) in "Hr8".
    set (Q3e := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c) with Q3e.
    assert (HQ3esp : Q3e !!! Regidx csp_rs1 = spd) by (rewrite /Q3e upd_ne; [ exact HQ3csp | reg_neq ]).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4e)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q3e (av - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr0]").
    { iApply (asl_4e with "Htext"). }
    { iEval (rewrite HQ3esp Hb4). iExact "Hr0". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr0".
    iEval (rewrite HQ3esp Hb4) in "Hr0".
    set (Q40 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e) with Q40.
    assert (HQ40sp : Q40 !!! Regidx csp_rs1 = spd) by (rewrite /Q40 upd_ne; [ exact HQ3esp | reg_neq ]).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.addi16sp sp,32 -- the frame trade back (pop 4) *)
    assert (Hwv : add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HQ40sp -Hspd. apply frame_cancel_32. }
    assert (Hpop : Q40 !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HQ40sp -Hspd. unfold pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x50)) (mword_of_int 2 : mword 6) Q40 (av - 4)%nat 4 eb Hpop
              with "Hcg Hpc [] Hframe4").
    { iApply (asl_50 with "Htext"). }
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (Q42 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40) with Q42.
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 c.ret *)
    assert (HQ42ra : Q42 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq].
      rewrite /Q3c upd_ne; [| reg_neq]. rewrite /Q3a upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x52)) (mword_of_int 1 : mword 5) Q42 av eb
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (asl_52 with "Htext"). }
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (Q42 !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rewrite HQ42ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* the postcondition *)
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 15 ->
              c <> mword_of_int 18 ->
              Q42 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9 N10 N15 N18.
      rewrite /Q42 /Q40 /Q3e /Q3c /Q3a. repeat (rewrite upd_ne; [| congruence]).
      rewrite (callee_saved_lookup Hrelcs2 c Hcs).
      rewrite /E5 /E4 /E3. repeat (rewrite upd_ne; [| congruence]).
      rewrite (callee_saved_lookup Hmp_cs c Hcs).
      rewrite /E2 /E1. repeat (rewrite upd_ne; [| congruence]). reflexivity. }
    iDestruct (cpu_own_transport CIDr CIDe6 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* the complement the release did not take, at the hart the epilogue
       ends on.  Free at both indices: [emp] at [eb = true], and at
       [eb = false] no step here could have moved the hart. *)
    iDestruct "Hext" as "[Hextc Hextm]".
    iDestruct (trap_csrs_ext_transport CID CIDe6 eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDe6 eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q42 with "[%] Hcg Hown Hextc Hextm Hpc Hstok HR Hpid").
    { unfold callee_saved.
      split. { (* sp *) rewrite /Q42 upd_eq. rewrite Hwv. exact Hsp0. }
      split. { (* s0 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq]. rewrite /Q3c upd_eq. reflexivity. }
      split. { (* s1 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_eq. reflexivity. }
      split. { (* s2 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_eq. reflexivity. }
      split. { rewrite (Hthr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H19. }
      split. { rewrite (Hthr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
      split. { rewrite (Hthr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
      split. { rewrite (Hthr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
      split. { rewrite (Hthr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
      split. { rewrite (Hthr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
      split. { rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
      split. { rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
      { rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. } }
  Qed.

  (* ---- the post-park stretch: +0x32 (reload) .. +0x34 (the branch).
     THIS runs at the hart sleep() resumed on -- but the lock is HELD, so the
     two instructions are interrupts-off and the hart does not move again
     inside this lemma.  Its two arms are the two anchored propositions: the
     exit path, or the loop's own Löb IH. ---- *)
  Lemma asl_post_sleep_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m M : regfile) (pidv : mword 32) (av : nat) (Vpr : pprivate)
      (slk spd sp0 : mword 64) (eb : bool) (lks : gset string) :
    let pj := proc_addr j in
    (26 <= av)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    asl_regs m M slk spd ->
    kernel_text -∗
    ▷ asl_loop CID0 γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks -∗
    asl_exit CID0 γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked γl cpu_id -∗
    sl_res_gen γsl slk R H -∗ H q -∗
    proc_priv_bare pj pidv Vpr -∗
    (* OUTER convention, matching [asl_loop]/[asl_exit]: still holding
       "sleep lock" here (the reload+branch at +0x32..+0x34 happens before
       either arm touches the lock). *)
    cpu_own 1 eb pj false ({["sleep lock"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (av - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.acquiresleep + 0x32)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    (* NB: [eb] is deliberately NOT substituted here.  This body runs [iNext]
       over [cpu_own], and with [eb] literal [intr_count]'s [if eb] reduces,
       [iNext] descends into [IntrDefs.intr_res] and strips ITS later, after
       which the resource can no longer be folded back to [cpu_own]. *)
    intros pj Hav Hanch Hasl.
    iIntros "#Htext IH Hexit Hr24 Hr16 Hr8 Hr0 Htok HRc HHq Hpid Hown Htc Hclm Hcg Hpc".
    assert (HaslM : asl_regs m M slk spd) by exact Hasl.
    destruct Hasl as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    (* open the fresh sl_res, do the +0x32 reload *)
    iDestruct "HRc" as (vp) "[Hwp Harm]".
    assert (Hlw24 : add_vec (rget M (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rgne. rewrite Hs1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x32)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M (trap_res eb + (av - 4))%nat vp false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hwp]").
    { iApply (asl_32 with "Htext"). }
    { iEval (rewrite Hlw24). iExact "Hwp". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hwp".
    iEval (rewrite Hlw24) in "Hwp".
    set (La5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 vp)]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 vp)]> M) with La5.
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    assert (HLa5_15 : La5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 vp) by (rewrite /La5; apply upd_eq).
    assert (HcsMLa5 : callee_saved M La5).
    { rewrite /La5. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HaslLa5 : asl_regs m La5 slk spd) by (apply (asl_regs_cs m M La5 slk spd HcsMLa5 HaslM)).
    (* +0x34 c.bnez a5 : free -> fall to +0x36 (exit); held -> back edge to +0x1c *)
    iDestruct "Harm" as "[(%Hvp0 & Hstok & HRu) | (%Hvph & Hdep)]".
    - (* FREE: vp = 0 -> bnez falls through to +0x36 -> exit *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x34)) (mword_of_int 244 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                La5 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HLa5_15 Hvp0; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_34 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iEval (rewrite Hvp0) in "Hwp".
      rewrite /asl_exit.
      iSpecialize ("Hexit" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Hexit" $! La5 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HRu Hwp Hpid Hown Htc Hclm Hcg Hpc").
      exact HaslLa5.
    - (* HELD: vp <> 0 -> bnez TAKEN, back edge to +0x1c (the Löb IH).  Hand the
         loop resources -- INCLUDING the IH, which arrives under a [▷] -- to the
         taken leaf's later-continuation bracket, so the inner [iNext] strips
         exactly this controlled context. *)
      iAssert (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)%I with "[Hwp]" as "Hheldw".
      { iExists vp. iFrame "Hwp". iPureIntro. exact Hvph. }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x34)) (mword_of_int 244 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                La5 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HLa5_15; exact Hvph)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [Hr24 Hr16 Hr8 Hr0 Htok Hpid Hown Htc Hclm IH Hexit Hheldw Hdep HHq]").
      { iApply (asl_34 with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hbk : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x34) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 244 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.acquiresleep + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk) in "Hpc".
      rewrite /asl_loop.
      iSpecialize ("IH" $! CID with "[%]"); [wp_next_chain|].
      iApply ("IH" $! La5 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hheldw Hdep HHq Hpid Hown Htc Hclm Hcg Hpc Hexit").
      exact HaslLa5.
  Qed.

  (* ---- one loop iteration: +0x1c (sleep_prepare) .. +0x2e (the
     re-acquire), i.e. the whole four-call split-sleep protocol ---- *)
  Lemma asl_loop_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat)
      (γpl γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m M : regfile) (pidv : mword 32) (av : nat) (Vpr : pprivate)
      (slk spd sp0 : mword 64) (eb : bool) (lks : gset string) :
    let pj := proc_addr j in
    (26 <= av)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γpl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    asl_regs m M slk spd ->
    (* OUTER convention, matching [asl_loop]/[asl_exit]/[asl_post_sleep_body];
       needed for the interior release .. re-acquire round trip below. *)
    locks_below lks "sleep lock" ->
    kernel_text -∗
    is_sleeplock_gen γl γsl slk s R H -∗
    procs_inv γs -∗
    ▷ asl_loop CID0 γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked γl cpu_id -∗
    (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝) -∗
    sl_dep γsl H -∗ H q -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["sleep lock"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (av - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.acquiresleep + 0x1c)) -∗
    asl_exit CID0 γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hav Hj Hjpl Hanch Hasl Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Htext #Hslk #Hpinv IH Hr24 Hr16 Hr8 Hr0 Htok Hheld Hdep HHq Hpid Hown Htc Hclm Hcg Hpc Hexit".
    assert (HaslM : asl_regs m M slk spd) by exact Hasl.
    destruct Hasl as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iDestruct "Hheld" as (vh) "[Hw %Hvh]".
    (* sleep_prepare's "chan <> 0", straight out of the word cell we hold *)
    iDestruct (asl_word4_nonzero with "Hw") as %Hslknz.
    (* ===== +0x1c c.mv a0,s1 : a0 := slk ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              M (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_1c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M) with L0.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== +0x1e jal ra,sleep_prepare ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2088778 : mword 21)
              L0 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_1e with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1e) : mword 64) 4)]> L0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1e) : mword 64) 4)]> L0) with L1.
    assert (Hjsp : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2088778 : mword 21)) = mword_of_int KernelSyms.sleep_prepare)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsp) in "Hpc".
    assert (HL1a0 : L1 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /L1 upd_ne; [| reg_neq]. rewrite /L0 upd_eq. rewrite Hs1. apply add_vec_zero_l. }
    assert (HL1ra : L1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1e) : mword 64) 4)
      by (rewrite /L1; apply upd_eq).
    assert (HcsML1 : callee_saved M L1).
    { rewrite /L1 /L0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HaslL1 : asl_regs m L1 slk spd) by (apply (asl_regs_cs m M L1 slk spd HcsML1 HaslM)).
    assert (Hchan : eq_vec (L1 !!! Regidx (mword_of_int 10 : mword 5)) (zero_reg : mword 64) = false)
      by (rewrite HL1a0; exact Hslknz).
    (* sleep_prepare(slk): noff-balanced at level 1, index [false], so it
       neither moves the hart nor touches the lock we still hold. *)
    iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γpl L1 (trap_res eb + (av - 4))%nat 1%nat eb false
              ({["sleep lock"]} ∪ lks)
              Hj Hjpl Hchan ltac:(lia) ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hown Htext Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mfp) "%Hspcs Hcg Hown Hpc".
    assert (Hpc22 : ret_pc (L1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x22)) by (rewrite HL1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    assert (HaslMfp : asl_regs m mfp slk spd)
      by (apply (asl_regs_cs m L1 mfp slk spd Hspcs HaslL1)).
    assert (Hmfp_s2 : mfp !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk)
      by (destruct HaslMfp as (_ & Xs2 & _); exact Xs2).
    (* ===== +0x22 c.mv a0,s2 : a0 := sl_lk slk ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x22)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              mfp (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_22 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 18 : mword 5)))]> mfp).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 18 : mword 5)))]> mfp) with L3.
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 jal ra,release ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x24)) (mword_of_int 1 : mword 5) (mword_of_int 2084002 : mword 21)
              L3 (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_24 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (L4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x24) : mword 64) 4)]> L3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x24) : mword 64) 4)]> L3) with L4.
    assert (Hjrl : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x24) : mword 64) (sign_extend' 64 (mword_of_int 2084002 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrl) in "Hpc".
    assert (HL4a0 : L4 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_eq. rewrite Hmfp_s2. apply add_vec_zero_l. }
    assert (HL4ra : L4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x24) : mword 64) 4)
      by (rewrite /L4; apply upd_eq).
    assert (HcsL4 : callee_saved mfp L4).
    { rewrite /L4 /L3.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HaslL4 : asl_regs m L4 slk spd) by (apply (asl_regs_cs m mfp L4 slk spd HcsL4 HaslMfp)).
    (* re-close [sl_res] HELD and hand the lock back.  THE INDEX SPLIT: the
       pay half goes to this release, the [_ext] complement is exactly what
       sleep() asks for and rides through the park. *)
    iDestruct (sl_res_close_held γsl slk R H vh Hvh with "Hw Hdep") as "HRc".
    assert (Hrel_lka : add_vec (L4 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = sl_lk slk).
    { rewrite HL4a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iDestruct (arm_pay_ext_split eb _ with "Htc Hclm") as "[Hpay Hext]".
    iApply (Release.wp_release_sconf KT1 γl (sl_lk slk) "sleep lock"%string (sl_res_gen γsl slk R H) L4
              0%nat eb pj (av - 4)%nat
              ({["sleep lock"]} ∪ lks)
              Hrel_lka ltac:(lia)
              with "Hcg Htext Hpc [] Htok HRc Hown Hpay").
    { iApply (is_sleeplock_gen_lock with "Hslk"). }
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hrelcs Hown".
    (* back to the OUTER set across the sleep_prepare/release/sleep/acquire
       round trip -- [Hfresh] is what makes the singleton insert/delete
       cancel. *)
    assert (Hsetback : ({["sleep lock"]} ∪ lks) ∖ {["sleep lock"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (Hpc28 : ret_pc (L4 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x28)) by (rewrite HL4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HaslMrel : asl_regs m mrel slk spd)
      by (apply (asl_regs_cs m L4 mrel slk spd Hrelcs HaslL4)).
    iDestruct "Hext" as "[Hextc Hextm]".
    iDestruct (trap_csrs_ext_transport CID CIDr eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDr eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    (* ===== +0x28 jal ra,sleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x28)) (mword_of_int 1 : mword 5) (mword_of_int 2088828 : mword 21)
              mrel (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_28 with "Htext"). }
    iIntros (CIDj Hsj) "Hcg Hpc".
    set (L5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x28) : mword 64) 4)]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x28) : mword 64) 4)]> mrel) with L5.
    assert (Hjsl : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2088828 : mword 21)) = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsl) in "Hpc".
    assert (HL5ra : L5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x28) : mword 64) 4)
      by (rewrite /L5; apply upd_eq).
    assert (HcsL5 : callee_saved mrel L5).
    { rewrite /L5. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HaslL5 : asl_regs m L5 slk spd) by (apply (asl_regs_cs m mrel L5 slk spd HcsL5 HaslMrel)).
    iDestruct (cpu_own_transport CIDr CIDj 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CIDr CIDj eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDr CIDj eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    (* THE PARK.  sleep()'s contract names no lock at all any more -- we
       dropped ours two instructions ago -- so all it takes beyond the
       running-thread bundle is the [_ext] complement, index-generic. *)
    iApply (Sleep.wp_sleep_sconf γs j γpl L5 (av - 4)%nat eb
              lks   (* the release above already cancelled the singleton *)
              Hj Hjpl ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hown Htext Hpc Hpinv Hextc Hextm").
    all: try lkbelow.
    (* SLEEP RETURNS ON HART [CIDs]. *)
    iIntros (CIDs Hss mfs) "%Hs_cs Hcg Hown Hpc Hextc Hextm".
    assert (Hpc2c : ret_pc (L5 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x2c)) by (rewrite HL5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HaslMfs : asl_regs m mfs slk spd)
      by (apply (asl_regs_cs m L5 mfs slk spd Hs_cs HaslL5)).
    assert (Hmfs_s2 : mfs !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk)
      by (destruct HaslMfs as (_ & Xs2 & _); exact Xs2).
    (* ===== +0x2c c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x2c)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              mfs (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_2c with "Htext"). }
    iIntros (CIDm Hsm) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 18 : mword 5)))]> mfs).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 18 : mword 5)))]> mfs) with L6.
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x2e)) (mword_of_int 1 : mword 5) (mword_of_int 2083856 : mword 21)
              L6 (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_2e with "Htext"). }
    iIntros (CIDa Hsa) "Hcg Hpc".
    set (L7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x2e) : mword 64) 4)]> L6).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x2e) : mword 64) 4)]> L6) with L7.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 2083856 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HL7a0 : L7 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /L7 upd_ne; [| reg_neq]. rewrite /L6 upd_eq. rewrite Hmfs_s2. apply add_vec_zero_l. }
    assert (HL7ra : L7 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x2e) : mword 64) 4)
      by (rewrite /L7; apply upd_eq).
    assert (HcsL7 : callee_saved mfs L7).
    { rewrite /L7 /L6.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HaslL7 : asl_regs m L7 slk spd) by (apply (asl_regs_cs m mfs L7 slk spd HcsL7 HaslMfs)).
    iDestruct (cpu_own_transport CIDs CIDa 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* ===== acquire(&slk->lk) again: back to level 1, index [false] ===== *)
    iApply (Acquire.wp_acquire_sconf KT1 γl "sleep lock"%string (sl_res_gen γsl slk R H) L7
              0%nat eb pj (av - 4)%nat eb lks
              ltac:(lia)
              ltac:(lia)
              Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HL7a0). iApply (is_sleeplock_gen_lock with "Hslk"). }
    iIntros (CIDq Hsq ms_a Macq) "%Hms_a Hcg Hpc %Hpins Htok HR Hown Hpay".
    iDestruct (trap_csrs_ext_transport CIDs CIDq eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDs CIDq eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iDestruct (arm_pay_ext_join eb _ with "Hpay [$Hextc $Hextm]") as "[Htc Hclm]".
    assert (Hpc32 : ret_pc (L7 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x32)) by (rewrite HL7ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    assert (HaslMacq : asl_regs m Macq slk spd)
      by (apply (asl_regs_cs m L7 Macq slk spd Hpins HaslL7)).
    iApply (asl_post_sleep_body (CID := CIDq) CID0 γs j γl γsl R H q m Macq pidv av Vpr slk spd sp0 eb lks
              Hav ltac:(wp_next_chain) HaslMacq
              with "Htext IH Hexit Hr24 Hr16 Hr8 Hr0 Htok HR HHq Hpid Hown Htc Hclm Hcg Hpc").
  Qed.

End AslBodies.

(* ===================================================================== *)

Section ProofAcquiresleep.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_acquiresleep_gen_sconf
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (pidv : mword 32) (Vpr : pprivate) (av : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_acquiresleep_gen_sconf_body γs j γl γsl s R H q m pidv Vpr av eb b lks.
  Proof.
    cbv beta delta [wp_acquiresleep_gen_sconf_body].
    intros pcE slk pj ret_tgt Hj Hav Hbelow.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hslk HHq Hpid #Hpinv Hcont".
    (* LEVEL 0 TIES THE TWO INDICES: [cpu_own_eb_agree] gives [eb = b]
       outright, so the function runs at ONE index throughout and there is
       nothing left to pin.  This used to derive [b = true] from the
       [eb = true] premise; with that premise gone the derivation is the
       agreement alone, which is what makes the [eb = false] instance live
       rather than vacuous. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    cbn [Nat.iter] in Hbm. subst b.
    (* derive proc j's own lock gname γpl from procs_inv (persistent, peek) *)
    iAssert (⌜length γs = NPROC⌝)%I as %Hlen. { by iDestruct "Hpinv" as "[$ _]". }
    destruct (lookup_lt_is_Some_2 γs j ltac:(rewrite Hlen; exact Hj)) as [γpl Hjpl].
    (* ===== PROLOGUE: 4-slot frame trade + saves ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* the frame-base equation the extracted bodies take *)
    assert (Hspd : add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd)
      by reflexivity.
    assert (Hsp0 : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 eb ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (asl_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (av - 4)%nat vr24 eb with "Hcg Hpc [] Hr24").
    { iApply (asl_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat vr16 eb with "Hcg Hpc [] Hr16").
    { iApply (asl_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (av - 4)%nat vr8 eb with "Hcg Hpc [] Hr8").
    { iApply (asl_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (av - 4)%nat vr0 eb with "Hcg Hpc [] Hr0").
    { iApply (asl_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    iEval (rgne) in "Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* the four frame cells now hold m's ra/s0/s1/s2; re-anchor at pa_stk sp0 k *)
    iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".  iEval (rewrite Hb4) in "Hr0".
    assert (Hr1v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr8v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr9v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr18v : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hr1v) in "Hr24". iEval (rewrite Hr8v) in "Hr16".
    iEval (rewrite Hr9v) in "Hr8".  iEval (rewrite Hr18v) in "Hr0".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat eb ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    (* +0x0c c.mv s1,a0 : s1 := slk *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2) with C0.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HC0a0 : C0 !!! Regidx (mword_of_int 10 : mword 5) = slk) by (rewrite /C0 upd_ne; [ exact HR2a0 | reg_neq ]).
    (* +0x0e addi s2,a0,8 : s2 := sl_lk slk *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 12)
              C0 (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0e with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0) with C1.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.acquiresleep + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HC1s2 : C1 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /C1 upd_eq. rewrite HC0a0. reflexivity. }
    (* +0x12 c.mv a0,s2 : a0 := sl_lk slk *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              C1 (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_12 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1) with C2.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2083882 : mword 21)
              C2 (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_14 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (Maq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)]> C2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)]> C2) with Maq.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2083882 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    (* facts about the acquire-entry map Maq *)
    assert (HMaqa0 : Maq !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_eq. rewrite add_vec_zero_l. exact HC1s2. }
    assert (HMaqra : Maq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)
      by (rewrite /Maq; apply upd_eq).
    assert (HMaqcsp : Maq !!! Regidx csp_rs1 = spd).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. exact HspR1. }
    assert (HMaqs1 : Maq !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_eq. rewrite add_vec_zero_l. exact HR2a0. }
    assert (HMaqs2 : Maq !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq]. exact HC1s2. }
    (* the s3..s11 preservation from m through the prologue (no writes) *)
    assert (Hpro_cs : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 10 -> c <> mword_of_int 18 -> c <> mword_of_int 1 ->
              Maq !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N9 N10 N18 N1.
      rewrite /Maq upd_ne; [| congruence]. rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence]. rewrite /C0 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence]. rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ===== acquire(&slk->lk): cpu_own 0 -> 1, returns locked + sl_res + pay ===== *)
    iDestruct (cpu_own_transport CID CID10 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf KT1 γl "sleep lock"%string (sl_res_gen γsl slk R H) Maq
              0%nat eb pj (av - 4)%nat eb lks
              ltac:(lia)
              ltac:(lia)
              Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HMaqa0). iApply (is_sleeplock_gen_lock with "Hslk"). }
    iIntros (CID11 Hs11 ms_a Macq) "%Hms_a Hcg Hpc %Hpins Htok HR Hown Hpay".
    (* JOIN AT THE INDEX: the acquire's push_off freed the pair at
       [eb = true] and nothing at [eb = false], where the caller brought it.
       From here the loop carries [trap_csrs ∗ cpu_claim pj] index-free.
       The caller's complement is hart-indexed and the prologue rebound the
       hart, so move it first -- free at both indices. *)
    iDestruct (trap_csrs_ext_transport CID CID11 eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID11 eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iDestruct (arm_pay_ext_join eb _ with "Hpay [$Hextc $Hextm]") as "[Htc Hclm]".
    assert (Hpc18 : ret_pc (Maq !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x18)) by (rewrite HMaqra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* asl_regs for the post-acquire map (via callee_saved from Maq) *)
    assert (Hasl_acq : asl_regs m Macq slk spd).
    { unfold asl_regs.
      repeat split.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs1.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs2.
      - rewrite (callee_saved_lookup Hpins csp_rs1 ltac:(vm_compute; reflexivity)). exact HMaqcsp.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq. }

    (* ============ the anchored EXIT continuation (+0x36 -> ret) ============ *)
    iAssert (asl_exit CID γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks) with "[Hcont]" as "Hexit".
    { rewrite /asl_exit.
      iIntros (CIDx Hsx M) "%HaslE Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HRx Hw Hpid Hown Htc Hclm Hcg Hpc".
      iApply (asl_exit_body (CID := CIDx) CID γs j γl γsl s R H q m M pidv av Vpr slk spd sp0 eb lks
                Hav Hsx Hspd Hsp0 HaslE Hbelow
                with "Htext Hslk Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HRx Hw Hpid Hown Htc Hclm Hcg Hpc Hcont"). }

    (* ============ the WAIT LOOP (iLöb over the anchored invariant) ============ *)
    iAssert (asl_loop CID γs j γl γsl R H q m pidv av Vpr slk spd sp0 eb lks) with "[]" as "Hloop".
    { iLöb as "IH". rewrite /asl_loop.
      iIntros (CIDy Hsy M) "%HaslL Hr24 Hr16 Hr8 Hr0 Htok Hheld Hdep HHq Hpid Hown Htc Hclm Hcg Hpc Hexit".
      iApply (asl_loop_body (CID := CIDy) CID γs j γpl γl γsl s R H q m M pidv av Vpr slk spd sp0 eb lks
                Hav Hj Hjpl Hsy HaslL Hbelow
                with "Htext Hslk Hpinv IH Hr24 Hr16 Hr8 Hr0 Htok Hheld Hdep HHq Hpid Hown Htc Hclm Hcg Hpc Hexit"). }

    (* ============ entry dispatch at +0x18 (lw then c.beqz) ============ *)
    pose proof Hasl_acq as HaslAcqW.
    destruct Hasl_acq as (Hacq_s1 & Hacq_s2 & Hacq_sp & Ha19 & Ha20 & Ha21 & Ha22 & Ha23 & Ha24 & Ha25 & Ha26 & Ha27).
    iDestruct "HR" as (v0) "[Hw0 Harm0]".
    assert (Hlw18 : add_vec (rget Macq (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rgne. rewrite Hacq_s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    (* +0x18 lw a5,0(s1) *)
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) Macq (trap_res eb + (av - 4))%nat v0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hw0]").
    { iApply (asl_18 with "Htext"). }
    { iEval (rewrite Hlw18). iExact "Hw0". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hw0".
    iEval (rewrite Hlw18) in "Hw0".
    set (Me := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq) with Me.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HMe15 : Me !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 v0) by (rewrite /Me; apply upd_eq).
    assert (HcsAcqMe : callee_saved Macq Me).
    { rewrite /Me. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HaslMe : asl_regs m Me slk spd) by (apply (asl_regs_cs m Macq Me slk spd HcsAcqMe HaslAcqW)).
    iDestruct "Harm0" as "[(%Hv00 & Hstok & HRu) | (%Hv0h & Hdep)]".
    - (* FREE at entry: v0 = 0 -> c.beqz TAKEN -> +0x36 (exit) *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1a)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (trap_res eb + (av - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HMe15 Hv00; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_1a with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt36 : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x1a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.acquiresleep + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt36) in "Hpc".
      iEval (rewrite Hv00) in "Hw0".
      rewrite /asl_exit.
      iSpecialize ("Hexit" $! CID11 with "[%]"); [wp_next_chain|].
      iApply ("Hexit" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HRu Hw0 Hpid Hown Htc Hclm Hcg Hpc").
      exact HaslMe.
    - (* HELD at entry: v0 <> 0 -> c.beqz falls through -> +0x1c (the loop) *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1a)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (trap_res eb + (av - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HMe15; assert (Hx : neq_vec (sign_extend' 64 v0) zero_reg = true) by exact Hv0h; unfold neq_vec in Hx; apply negb_true_iff in Hx; exact Hx)
                with "Hcg Hpc []").
      { iApply (asl_1a with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      iAssert (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)%I with "[Hw0]" as "Hheldw".
      { iExists v0. iFrame "Hw0". iPureIntro. exact Hv0h. }
      rewrite /asl_loop.
      iSpecialize ("Hloop" $! CID11 with "[%]"); [wp_next_chain|].
      iApply ("Hloop" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hheldw Hdep HHq Hpid Hown Htc Hclm Hcg Hpc Hexit").
      exact HaslMe.
  Qed.

  (* ===================================================================== *)
  (*  ROUTE B (3): THE NESTED acquiresleep, at [cpu_own (S n) eb pj C false]. *)
  (* ===================================================================== *)
  (* iput calls acquiresleep(&ip->lock) while HOLDING itable.lock (fs.c:348,
     the kernel's only nested acquiresleep).  The ordinary contract demands
     [cpu_own 0], because everything below it sleeps.  Design fs-icache.md
     13.12 rules that the sleeping branch DIVERGES instead -- sleep at
     noff >= 2 reaches sched's panic("sched locks") -- so the nested
     contract is the ordinary one restricted to the FREE branch, and it
     returns holding the sleeplock's resource exactly as the ordinary one
     delivers it.

     Three things fall out and none of them is a choice:
       - the resource index is the LITERAL [false] ([cpu_own]'s enabled arm
         demands noff = 0, which [S n] refutes), so there is no [b] binder,
         no [cpu_own_eb_agree] step and no [cpu_own_transport];
       - there is NO [eb = true] parking premise: the returning path never
         parks, and the branch that would has no postcondition to state;
       - the crossing index is [false] as well, so every leaf -- including
         the epilogue after release, which at level 0 exits at [outb = eb]
         and is therefore hart-generic there -- collapses through
         [wp_next_off_intro], and the whole function is ONE straight-line
         lemma.  In particular the [asl_loop] iLob invariant and its
         [asl_exit] anchor are NOT needed: the wait loop is entered only
         from the locked branch, which diverges before it can go round. *)
  (* ==================================================================== *)
  (*  THE NESTED BODY MINUS ITS WAIT LOOP.                                 *)
  (*                                                                      *)
  (* Prologue, entry [acquire(&slk->lk)], the [locked := 1] /              *)
  (* [pid := myproc()->pid] stores, the interior release and the entry     *)
  (* dispatch -- with the LOCKED arm handed off to whatever [asl_nloop]    *)
  (* the caller supplies.  ONE caller does: the NON-BLOCKING contract,     *)
  (* which supplies a REFUTATION -- the locked arm cannot happen when no   *)
  (* share of the "may hold" right exists.  (A blocking nested contract    *)
  (* used to supply the loop itself; it is gone -- file header.)           *)
  (*                                                                      *)
  (* Nothing here reaches [sleep_prepare], so the held-set precondition is *)
  (* only what the interior acquire's ghost step consumes: FRESHNESS.      *)
  (* [X] is a resource routed to whichever arm the entry test picks: the   *)
  (* counting authority, which the non-blocking caller needs BOTH to       *)
  (* refute the locked arm and to hand back on the free one.               *)
  (* ==================================================================== *)
  Lemma asl_nested_core
      (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp) (X : iProp Σ)
      (m : regfile) (j : nat) (pidv : mword 32) (Vpr : pprivate) (av : nat) (eb : bool)
      (n : nat) (lks : gset string) :
    let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
    let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (26 <= av)%nat ->
    (Z.of_nat n + 4 < 2 ^ 31)%Z ->
    "sleep lock" ∉ lks ->
    sie_cap_gpr KT1 m av false pj -∗
    cpu_own (S n) eb pj false lks -∗
    kernel_text -∗ pc_is pcE -∗
    is_sleeplock_gen γl γsl slk s R H -∗
    H q -∗
    X -∗
    proc_priv_bare pj pidv Vpr -∗
    asl_nloop γl γsl R H q X m j pidv av Vpr slk
      (add_vec (m !!! Regidx csp_rs1 : mword 64)
         (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      (m !!! Regidx csp_rs1 : mword 64) eb n lks -∗
    wp_next false pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf ⌝ -∗
        sie_cap_gpr KT1 mf av false pj -∗
        cpu_own (S n) eb pj false lks -∗
        pc_is ret_tgt -∗
        sleeplocked_q γsl q slk pidv -∗
        X -∗
        R -∗
        proc_priv_bare pj pidv Vpr -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pcE slk pj ret_tgt Hav Hb31 Hfresh.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hown #Htext Hpc #Hslk HHq HX Hpid Hnloop Hcont".
    (* the crossing is at index [false], so the continuation is usable at
       THIS hart with no anchoring at all. *)
    iEval (rewrite wp_next_off) in "Hcont".
    (* ===== PROLOGUE: 4-slot frame trade + saves ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* the frame-base equation the extracted bodies take *)
    assert (Hspd : add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd)
      by reflexivity.
    assert (Hsp0 : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 false ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (asl_00 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (av - 4)%nat vr24 false with "Hcg Hpc [] Hr24").
    { iApply (asl_02 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat vr16 false with "Hcg Hpc [] Hr16").
    { iApply (asl_04 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (av - 4)%nat vr8 false with "Hcg Hpc [] Hr8").
    { iApply (asl_06 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (av - 4)%nat vr0 false with "Hcg Hpc [] Hr0").
    { iApply (asl_08 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr0".
    iEval (rgne) in "Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* the four frame cells now hold m's ra/s0/s1/s2; re-anchor at pa_stk sp0 k *)
    iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".  iEval (rewrite Hb4) in "Hr0".
    assert (Hr1v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr8v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr9v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr18v : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hr1v) in "Hr24". iEval (rewrite Hr8v) in "Hr16".
    iEval (rewrite Hr9v) in "Hr8".  iEval (rewrite Hr18v) in "Hr0".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    (* +0x0c c.mv s1,a0 : s1 := slk *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2) with C0.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HC0a0 : C0 !!! Regidx (mword_of_int 10 : mword 5) = slk) by (rewrite /C0 upd_ne; [ exact HR2a0 | reg_neq ]).
    (* +0x0e addi s2,a0,8 : s2 := sl_lk slk *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 12)
              C0 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_0e with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0) with C1.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.acquiresleep + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HC1s2 : C1 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /C1 upd_eq. rewrite HC0a0. reflexivity. }
    (* +0x12 c.mv a0,s2 : a0 := sl_lk slk *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              C1 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (asl_12 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1) with C2.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2083882 : mword 21)
              C2 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (asl_14 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Maq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)]> C2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)]> C2) with Maq.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2083882 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    (* facts about the acquire-entry map Maq *)
    assert (HMaqa0 : Maq !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_eq. rewrite add_vec_zero_l. exact HC1s2. }
    assert (HMaqra : Maq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x14) : mword 64) 4)
      by (rewrite /Maq; apply upd_eq).
    assert (HMaqcsp : Maq !!! Regidx csp_rs1 = spd).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. exact HspR1. }
    assert (HMaqs1 : Maq !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_eq. rewrite add_vec_zero_l. exact HR2a0. }
    assert (HMaqs2 : Maq !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq]. exact HC1s2. }
    (* the s3..s11 preservation from m through the prologue (no writes) *)
    assert (Hpro_cs : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 10 -> c <> mword_of_int 18 -> c <> mword_of_int 1 ->
              Maq !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N9 N10 N18 N1.
      rewrite /Maq upd_ne; [| congruence]. rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence]. rewrite /C0 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence]. rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ===== acquire(&slk->lk): cpu_own 0 -> 1, returns locked + sl_res + pay ===== *)
    iApply (Acquire.wp_acquire_fresh_sconf KT1 γl "sleep lock"%string (sl_res_gen γsl slk R H) Maq
              (S n) eb pj (av - 4)%nat false lks
              ltac:(lia)
              ltac:(lia)
              Hfresh
              with "Hcg Hown Htext Hpc []").
    { iEval (rewrite HMaqa0). iApply (is_sleeplock_gen_lock with "Hslk"). }
    iApply wp_next_off_intro.
    iIntros (ms_a Macq) "%Hms_a Hcg Hpc %Hpins Htok HR Hown Hpay".
    assert (Hpc18 : ret_pc (Maq !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.acquiresleep + 0x18)) by (rewrite HMaqra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* asl_regs for the post-acquire map (via callee_saved from Maq) *)
    assert (Hasl_acq : asl_regs m Macq slk spd).
    { unfold asl_regs.
      repeat split.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs1.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs2.
      - rewrite (callee_saved_lookup Hpins csp_rs1 ltac:(vm_compute; reflexivity)). exact HMaqcsp.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq. }
    (* ============ entry dispatch at +0x18 (lw then c.beqz) ============ *)
    pose proof Hasl_acq as HaslAcqW.
    destruct Hasl_acq as (Hacq_s1 & Hacq_s2 & Hacq_sp & Ha19 & Ha20 & Ha21 & Ha22 & Ha23 & Ha24 & Ha25 & Ha26 & Ha27).
    iDestruct "HR" as (v0) "[Hw0 Harm0]".
    assert (Hlw18 : add_vec (rget Macq (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rgne. rewrite Hacq_s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    (* +0x18 lw a5,0(s1) *)
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) Macq (av - 4)%nat v0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hw0]").
    { iApply (asl_18 with "Htext"). }
    { iEval (rewrite Hlw18). iExact "Hw0". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hw0".
    iEval (rewrite Hlw18) in "Hw0".
    set (Me := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq) with Me.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HMe15 : Me !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 v0) by (rewrite /Me; apply upd_eq).
    assert (HcsAcqMe : callee_saved Macq Me).
    { rewrite /Me. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HaslMe : asl_regs m Me slk spd) by (apply (asl_regs_cs m Macq Me slk spd HcsAcqMe HaslAcqW)).
    pose proof HaslMe as HaslMeW.

    (* ============ the EXIT continuation (+0x36 -> ret) ============ *)
    iAssert (asl_nexit γl γsl R H q X m j pidv av Vpr slk spd sp0 eb n lks) with "[Hcont]" as "Hnexit".
    { iIntros (M) "%HaslE Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HX HR Hw Hpid Hown Hpay Hcg Hpc".
      iMod (sl_free_retarget γsl slk q with "Hstok") as "[Hstok Hha]".
      iDestruct (sleeplocked_q_pid with "Hstok") as "[Hspid Hstokback]".
      destruct HaslE as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
      (* the four saved-slot addresses, in the [c.ldsp] leaf's spelling *)
      assert (HbE1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
      { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      assert (HbE2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
      { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      assert (HbE3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
      { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      assert (HbE4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
      { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      (* +0x36 c.li a5,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                M (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_36 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M) with E1.
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E1 upd_ne; [ exact Hs1 | reg_neq ]).
      (* +0x38 c.sw a5,0(s1) : slk->locked := 1 *)
      assert (Hlw0 : add_vec (rget E1 (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
      { rgne. rewrite HE1s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x38)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) E1 (av - 4)%nat (mword_of_int 0 : mword 32) false
                with "Hcg Hpc [] [Hw]").
      { iApply (asl_38 with "Htext"). }
      { iEval (rewrite Hlw0). iExact "Hw". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hw".
      iEval (rewrite Hlw0) in "Hw".
      assert (Hsv1 : trunc32 (rget E1 (mword_of_int 15 : mword 5)) = (mword_of_int 1 : mword 32)).
      { rgne. rewrite /E1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hsv1) in "Hw".
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a jal ra,myproc *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x3a)) (mword_of_int 1 : mword 5) (mword_of_int 2087204 : mword 21)
                E1 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_3a with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4)]> E1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4)]> E1) with E2.
      assert (Hjmp : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) (sign_extend' 64 (mword_of_int 2087204 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmp) in "Hpc".
      assert (HE2ra : E2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3a) : mword 64) 4) by (rewrite /E2; apply upd_eq).
      iApply (Myproc.wp_myproc_sconf E2 (av - 4)%nat (S (S n)) eb pj false _
                ltac:(lia)
                ltac:(lia)
                with "Hcg Hown Htext Hpc").
      iApply wp_next_off_intro.
      iIntros (ms_m mfm) "%Hms_m Hcg Hown Hpc %Hmp".
      destruct Hmp as (Hmp_cs & Hmp_a0).
      assert (Hpc3e : ret_pc (E2 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.acquiresleep + 0x3e)) by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3e) in "Hpc".
      assert (Hmfma0 : mfm !!! Regidx (mword_of_int 10 : mword 5) = pj) by exact Hmp_a0.
      (* +0x3e c.lw a5,48(a0) : a5 := myproc()->pid *)
      assert (Hppid : add_vec (rget mfm (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")))) = p_pid pj).
      { rgne. rewrite Hmfma0. rewrite /p_pid.
        replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) : mword 64)
          with (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      (* [p->pid] is READ here, so this one load does need the field
         itself.  It is BORROWED out of the caller's [proc_priv_bare]
         block for the length of the load and handed straight back a
         few lines below: the contract, and every chain threading
         through it, passes the whole block around, never a loose
         quarter of the cell. *)
      iDestruct (proc_priv_bare_pid with "Hpid") as "[Hpidq Hpidbk]".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x3e)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) mfm (av - 4)%nat pidv false (dqm := DfracOwn (1/4))
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hpidq]").
      { iApply (asl_3e with "Htext"). }
      { iEval (rewrite Hppid). iExact "Hpidq". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hpidq".
      iEval (rewrite Hppid) in "Hpidq".
      iDestruct ("Hpidbk" with "Hpidq") as "Hpid".
      set (E3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm) with E3.
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (HmfmS1 : mfm !!! Regidx (mword_of_int 9 : mword 5) = slk).
      { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HE1s1. }
      assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E3 upd_ne; [ exact HmfmS1 | reg_neq ]).
      (* +0x40 c.sw a5,40(s1) : slk->pid := pidv *)
      assert (Hspidaddr : add_vec (rget E3 (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")))) = sl_pid slk).
      { rgne. rewrite HE3s1. rewrite /sl_pid.
        replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) : mword 64)
          with (sign_extend' 64 (mword_of_int 40 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.acquiresleep + 0x40)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) E3 (av - 4)%nat (mword_of_int 0 : mword 32) false
                with "Hcg Hpc [] [Hspid]").
      { iApply (asl_40 with "Htext"). }
      { iEval (rewrite Hspidaddr). iExact "Hspid". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hspid".
      iEval (rewrite Hspidaddr) in "Hspid".
      assert (Hsvpid : trunc32 (rget E3 (mword_of_int 15 : mword 5)) = pidv).
      { rgne. rewrite /E3 upd_eq. apply trunc32_sext. }
      iEval (rewrite Hsvpid) in "Hspid".
      iDestruct ("Hstokback" $! pidv with "Hspid") as "Hstok".
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* +0x42 c.mv a0,s2 : a0 := sl_lk slk *)
      assert (HmfmS2 : mfm !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
      { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
        rewrite /E1 upd_ne; [ exact Hs2 | reg_neq ]. }
      assert (HE3s2 : E3 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk) by (rewrite /E3 upd_ne; [ exact HmfmS2 | reg_neq ]).
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
                E3 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (asl_42 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (E4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3) with E4.
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 2083970 : mword 21)
                E4 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_44 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4)]> E4).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4)]> E4) with E5.
      assert (Hjrel : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 2083970 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjrel) in "Hpc".
      assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x44) : mword 64) 4) by (rewrite /E5; apply upd_eq).
      assert (HE5a0 : E5 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. rewrite add_vec_zero_l. exact HE3s2. }
      (* re-close sl_res in the HELD state (word = 1) *)
      iDestruct (sl_res_close_held_q γsl slk R H (mword_of_int 1 : mword 32) q ltac:(vm_compute; reflexivity) with "Hw Hha HHq") as "HRc".
      assert (Hrel_lka : add_vec (E5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = sl_lk slk).
      { rewrite HE5a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      iApply (Release.wp_release_sconf KT1 γl (sl_lk slk) "sleep lock"%string (sl_res_gen γsl slk R H) E5
                (S n) eb pj (av - 4)%nat
                ({["sleep lock"]} ∪ lks)
                Hrel_lka ltac:(lia)
                with "Hcg Htext Hpc [] Htok HRc Hown Hpay").
      { iApply (is_sleeplock_gen_lock with "Hslk"). }
      iApply wp_next_off_intro.
      iIntros (mrel) "Hcg Hpc %Hrelcs Hown".
      (* FREE branch, straight out of entry acquire: back to the OUTER [lks]
         Hcont expects.  FRESHNESS, not a bound, is what cancels the pair. *)
      assert (Hsetback : ({["sleep lock"]} ∪ lks) ∖ {["sleep lock"]} = lks)
      by (apply locks_add_del; exact Hfresh).
      iEval (rewrite Hsetback) in "Hown".
      assert (Hpc48 : ret_pc (E5 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.acquiresleep + 0x48)) by (rewrite HE5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc48) in "Hpc".
      (* ===== EPILOGUE (0x3a..0x44): restore ra/s0/s1/s2, frame pop, ret =====
         release exits at [outb = false] -- the level only unwinds to
         [S n] >= 1 -- so unlike the level-0 contract this stretch stays on
         ONE hart and every leaf collapses through [wp_next_off_intro]. *)
      pose proof Hrelcs as Hrelcs2.
      assert (HmfmSp : mfm !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hmp_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /E1 upd_ne; [ exact Hsp | reg_neq ]. }
      assert (HE5csp : E5 !!! Regidx csp_rs1 = spd).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq]. exact HmfmSp. }
      assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HE5csp. }
      (* +0x48 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x48)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hr24]").
      { iApply (asl_48 with "Htext"). }
      { iEval (rewrite HmrelSp HbE1). iExact "Hr24". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr24".
      iEval (rewrite HmrelSp HbE1) in "Hr24".
      set (Q3a := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with Q3a.
      assert (HQ3asp : Q3a !!! Regidx csp_rs1 = spd) by (rewrite /Q3a upd_ne; [ exact HmrelSp | reg_neq ]).
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4a)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                Q3a (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hr16]").
      { iApply (asl_4a with "Htext"). }
      { iEval (rewrite HQ3asp HbE2). iExact "Hr16". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr16".
      iEval (rewrite HQ3asp HbE2) in "Hr16".
      set (Q3c := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a).
      change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a) with Q3c.
      assert (HQ3csp : Q3c !!! Regidx csp_rs1 = spd) by (rewrite /Q3c upd_ne; [ exact HQ3asp | reg_neq ]).
      assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4c) in "Hpc".
      (* +0x4c c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4c)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                Q3c (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hr8]").
      { iApply (asl_4c with "Htext"). }
      { iEval (rewrite HQ3csp HbE3). iExact "Hr8". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr8".
      iEval (rewrite HQ3csp HbE3) in "Hr8".
      set (Q3e := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c) with Q3e.
      assert (HQ3esp : Q3e !!! Regidx csp_rs1 = spd) by (rewrite /Q3e upd_ne; [ exact HQ3csp | reg_neq ]).
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* +0x4e c.ldsp s2,0(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x4e)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
                Q3e (av - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hr0]").
      { iApply (asl_4e with "Htext"). }
      { iEval (rewrite HQ3esp HbE4). iExact "Hr0". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr0".
      iEval (rewrite HQ3esp HbE4) in "Hr0".
      set (Q40 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e) with Q40.
      assert (HQ40sp : Q40 !!! Regidx csp_rs1 = spd) by (rewrite /Q40 upd_ne; [ exact HQ3esp | reg_neq ]).
      assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 c.addi16sp sp,32 -- the frame trade back (pop 4) *)
      assert (Hwv : add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HQ40sp -Hspd. apply frame_cancel_32. }
      assert (Hpop : Q40 !!! Regidx csp_rs1
                     = pa_stk (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HQ40sp -Hspd. unfold pa_stk, add_vec_int.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
        iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x50)) (mword_of_int 2 : mword 6) Q40 (av - 4)%nat 4 false Hpop
                with "Hcg Hpc [] Hframe4").
      { iApply (asl_50 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (Q42 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40).
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40) with Q42.
      assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      (* +0x52 c.ret *)
      assert (HQ42ra : Q42 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq].
        rewrite /Q3c upd_ne; [| reg_neq]. rewrite /Q3a upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x52)) (mword_of_int 1 : mword 5) Q42 av false
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc []").
      { iApply (asl_52 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (Q42 !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
        by (rewrite HQ42ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* the postcondition *)
      assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 15 ->
                c <> mword_of_int 18 ->
                Q42 !!! Regidx c = M !!! Regidx c).
      { intros c Hcs N1 N2 N8 N9 N10 N15 N18.
        rewrite /Q42 /Q40 /Q3e /Q3c /Q3a. repeat (rewrite upd_ne; [| congruence]).
        rewrite (callee_saved_lookup Hrelcs2 c Hcs).
        rewrite /E5 /E4 /E3. repeat (rewrite upd_ne; [| congruence]).
        rewrite (callee_saved_lookup Hmp_cs c Hcs).
        rewrite /E2 /E1. repeat (rewrite upd_ne; [| congruence]). reflexivity. }
      iApply ("Hcont" $! Q42 with "[%] Hcg Hown Hpc Hstok HX HR Hpid").
      { unfold callee_saved.
        split. { (* sp *) rewrite /Q42 upd_eq. rewrite Hwv. exact Hsp0. }
        split. { (* s0 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq]. rewrite /Q3c upd_eq. reflexivity. }
        split. { (* s1 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_eq. reflexivity. }
        split. { (* s2 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_eq. reflexivity. }
        split. { rewrite (Hthr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H19. }
        split. { rewrite (Hthr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
        split. { rewrite (Hthr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
        split. { rewrite (Hthr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
        split. { rewrite (Hthr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
        split. { rewrite (Hthr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
        split. { rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
        split. { rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
        { rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. } }
    }


    (* ============ entry dispatch at +0x1a ============ *)
    iDestruct "Harm0" as "[(%Hv00 & Hstok & HR) | (%Hv0h & Hdep)]".
    - (* FREE at entry: v0 = 0 -> c.beqz TAKEN -> +0x36 (exit) *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1a)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (av - 4)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HMe15 Hv00; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (asl_1a with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt36 : add_vec (mword_of_int (KernelSyms.acquiresleep + 0x1a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.acquiresleep + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt36) in "Hpc".
      iEval (rewrite Hv00) in "Hw0".
      iApply ("Hnexit" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hstok HHq HX HR Hw0 Hpid Hown Hpay Hcg Hpc").
      exact HaslMeW.
    - (* HELD at entry: v0 <> 0 -> c.beqz falls through -> +0x1c (the loop) *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.acquiresleep + 0x1a)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (av - 4)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HMe15; assert (Hx : neq_vec (sign_extend' 64 v0) zero_reg = true) by exact Hv0h; unfold neq_vec in Hx; apply negb_true_iff in Hx; exact Hx)
                with "Hcg Hpc []").
      { iApply (asl_1a with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.acquiresleep + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.acquiresleep + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      iAssert (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)%I with "[Hw0]" as "Hheldw".
      { iExists v0. iFrame "Hw0". iPureIntro. exact Hv0h. }
      iApply ("Hnloop" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hheldw Hdep HHq HX Hpid Hown Hpay Hcg Hpc Hnexit").
      exact HaslMeW.
  Qed.

  (* ==================================================================== *)
  (*  THE FOUR PUBLIC CONTRACTS.                                           *)
  (* ==================================================================== *)

  (* the level-0 contract at the UNTRACKED instance: the deposit is [emp],
     the fraction invisible, and every existing caller (bget, ilock) reads
     exactly as before. *)
  Lemma wp_acquiresleep_sconf
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (Vpr : pprivate) (av : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_acquiresleep_sconf_body γs j γl γsl s R m pidv Vpr av eb b lks.
  Proof.
    cbv beta delta [wp_acquiresleep_sconf_body].
    intros pcE slk pj ret_tgt Hj Hav Hbelow.
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hslk Hpid #Hpinv Hcont".
    iAssert (emp)%I with "[]" as "Hemp"; [ first [ done | iEmpIntro ] |].
    iApply (wp_acquiresleep_gen_sconf γs j γl γsl s R sl_untracked 1%Qp m pidv Vpr av eb b lks
              Hj Hav Hbelow
              with "Hcg Hown Hextc Hextm Htext Hpc Hslk Hemp Hpid Hpinv [Hcont]").
    iIntros (CIDf Hsf mf) "%Hcs Hcg Hown Hextc Hextm Hpc Hstok HR Hpid".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [ exact Hsf |].
    iAssert (sleeplocked γsl slk pidv) with "[Hstok]" as "Hstok";
      [ iExists 1%Qp; iFrame |].
    iApply ("Hcont" $! mf with "[%] Hcg Hown Hextc Hextm Hpc Hstok HR Hpid").
    exact Hcs.
  Qed.

  (* ==================================================================== *)
  (*  THE NON-BLOCKING CONTRACT.                                          *)
  (* ==================================================================== *)
  Lemma wp_acquiresleep_nb_sconf
      (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ) (γt : gname) (q : Qp)
      (m : regfile) (pidv : mword 32) (Vpr : pprivate) (av : nat) (eb : bool)
      (n : nat) (lks : gset string)
    : wp_acquiresleep_nb_body j γl γsl s R γt q m pidv Vpr av eb n lks.
  Proof.
    cbv beta delta [wp_acquiresleep_nb_body].
    intros pcE slk pj ret_tgt Hav Hb31 Hfresh.
    iIntros "Hcg Hown #Htext Hpc #Hslk Hauth Hpid Hcont".
    (* the share this call will deposit, minted out of the authoritative
       zero.  It is spent only on the FREE arm; on the other arm it is still
       in hand, which is what makes the refutation below go through. *)
    iMod (slh_mint_none γt q with "Hauth") as "[Hauth Htokq]".
    iApply (asl_nested_core γl γsl s R (slh_tok γt) q (slh_auth γt (Some q))
              m j pidv Vpr av eb n lks Hav Hb31 Hfresh
              with "Hcg Hown Htext Hpc Hslk Htokq Hauth Hpid [] Hcont").
    (* THE REFUTATION.  Reaching the wait loop means the lock was HELD, i.e.
       its held arm holds somebody's share [q']; this call still holds its own
       [q]; and the authority says the total outstanding is exactly [q].
       [q + q' <= q] is false in [Qp]. *)
    iIntros (M) "%HaslL Hr24 Hr16 Hr8 Hr0 Htok Hheld Hdep HHq HX Hpid Hown Hpay Hcg Hpc Hnexit".
    iDestruct "Hdep" as (q') "[_ Htok']".
    iDestruct (slh_tok_join with "HHq Htok'") as "Hsum".
    iDestruct (slh_auth_tok_le with "HX Hsum") as %(t' & Ht' & Hle).
    injection Ht' as Ht'. subst t'.
    iExFalso. iPureIntro. exact (Qp.not_add_le_l q q' Hle).
  Qed.

End ProofAcquiresleep.

End AcquiresleepProof.
