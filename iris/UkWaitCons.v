(* UkWaitCons.v -- THE CONSUMER TEST for wait at a real status pointer
   (lane RD-7).

   WHAT IT IS FOR.  [UkRunSys.wp_uk_ecall_wait_status] is the first wait
   leaf whose caller may pass a pointer, and the only way to see that the
   statement is USABLE is to spend it: a parent holding
   [ChildTok.child_tok] for the one child it forked calls wait at a buffer
   it owns, and comes back holding BOTH halves of what a reap answers --
   the payload its child's exit paid ([ChildTok.gen_pay]) and the four
   bytes of the status that payload is keyed at, in its own memory.
   Neither was stateable before: the null leaves copy nothing, and the
   window leaf excludes wait because a reap moves the children reading.

   THE TEST IS AT ONE CHILD, deliberately.  With [Sc = {[γc]}] the reaped
   generation is the caller's own by set arithmetic alone, so the test
   measures the INTERFACE and not a pid comparison the program would
   otherwise have to run (init's loop does run one --
   [UkInitMain]'s [beq] against the shell's pid -- and this leaf serves it
   just as well; what it needs from the answer is exactly what is taken
   here).

   WHAT THE -1 ARM COSTS.  It is handed back with the buffer and the token
   and NOTHING said about why.  The reason is precise and is the lane's
   one identified wall: [UserChildren.wait_why]'s first exit -- a zombie
   child was there and copyout could not place its status -- is guarded on
   the status pointer being NULL, so a caller that passes a real pointer
   buys the status word and pays the -1 arm's reason.  Refuting that exit
   needs kwait to publish copyout's own [~ UserPtTree.uva_wmapped]
   witness, the way consoleread's swallow arm publishes its own
   ([UkRunSys.uk_read_nofault] is the U-tier half, already built).  See
   claude-notes/design/user-proc.md. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map ghost_var invariants.
From transfinite.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import UserFd.
Require Import UserHeap.
Require Import ProcGeom.           (* [tf_arg_idx] / [xstate_val] *)
Require Import ChildTok.
Require Import UserChildren.
Require Import UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Local Open Scope Z_scope.
Import Defs.

Section UkWaitCons.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* ===================================================================== *)
  (* THE TEST.  A parent with exactly one child, a four-byte buffer it     *)
  (* owns, and its own pid (which it knows is not <init>'s) waits at that  *)
  (* buffer.                                                              *)
  (*                                                                       *)
  (* ON THE REAPING ARM it learns FOUR things, and the last two are what   *)
  (* the lane exists for:                                                  *)
  (*   - the number it got back is its child's pid, sign-extended;         *)
  (*   - its children reading is now empty;                                *)
  (*   - the payload it chose at fork, at the status the child exited      *)
  (*     with ([Q (xstate_val xw)]);                                       *)
  (*   - and the four bytes IN ITS OWN BUFFER are that same word, read     *)
  (*     little-endian ([RiscvModelBytes.nth_byte]).                       *)
  (* The last two are keyed at ONE [xw], which is the whole content of     *)
  (* the join: a program can branch on the status it READ and know what    *)
  (* the payload it REDEEMED is about.                                    *)
  (* ===================================================================== *)
  Lemma wp_uk_wait_learn_status (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (dst : mword 64) (f : nat -> bv 8) (avail : nat)
      (p : Z) (γc : gname) (pidc : mword 32) (Q : Z -> iProp Σ) :
    usysno m = USYS_wait ->
    m !!! Regidx (mword_of_int 10) = dst ->
    dst <> (zero_reg : mword 64) ->
    (* the caller is not <init>, which is what makes a reaped generation
       ITS OWN ([UexecRet.uwait_ans_pid_mine]'s premise); a forked child
       holds it off its own fork. *)
    p <> 1%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) {[γc]} -∗
    ubytes (ukn_d N) (uint dst) 4 f -∗
    UserChildren.upid (ukn_pid N) p -∗
    child_tok γc pidc Q -∗
    (* THE REAP *)
    (∀ (h' : CpuId) (g : nat -> bv 8) (xw : mword 32),
       ⌜ forall j : nat, (j < 4)%nat -> g j = nth_byte xw j ⌝ -∗
       ▷ Q (xstate_val xw) -∗
       UserChildren.upid (ukn_pid N) p -∗
       urun N h' (<[Regidx (mword_of_int 10) := (sign_extend' 64 pidc : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) (∅ : gset gname) -∗
       ubytes (ukn_d N) (uint dst) 4 g -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ...AND THE ARM THE INTERFACE CANNOT RULE OUT: a -1, at which the
       caller keeps its token, its buffer and its reading, and is told
       nothing about why. *)
    (∀ (h' : CpuId) (Sc' : gset gname) (g : nat -> bv 8),
       UserChildren.upid (ukn_pid N) p -∗
       child_tok γc pidc Q -∗
       urun N h' (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       ubytes (ukn_d N) (uint dst) 4 g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hdst Hnz Hp1 Hal4.
    iIntros "#Hi Hrun Hsb Hch Hbuf Hpid Htok Hreap Hfail".
    iApply (wp_uk_ecall_wait_status N h m pc dst 4 f avail {[γc]} p
              Hn Hdst Hnz ltac:(lia) Hal4
              with "Hi Hrun Hsb Hch Hbuf Hpid").
    iIntros (h' r Sc' pidv g) "%Hpv Hpid %Hgf Hans Hrun Hch Hbuf".
    destruct (decide (r = (mword_of_int (-1) : mword 64))) as [-> | Hm1].
    { (* nothing to read: the reason is not on offer at a real pointer *)
      iApply ("Hfail" $! h' Sc' g with "Hpid Htok Hrun Hch Hbuf"). }
    (* THE CALLER IS NOT <INIT>, off the pid fragment it spent going in *)
    assert (Hpne : pidv <> (mword_of_int 1 : mword 32)).
    { intros Hc. apply Hp1. rewrite <- Hpv, Hc. vm_compute. reflexivity. }
    iDestruct (uwait_status_reaped r {[γc]} Sc' pidv g Hpne Hm1 with "Hans")
      as (γ' rv xw) "(%Hf & Hesc & _)".
    destruct Hf as (Hr & Hcs' & Hin & _ & Hby).
    (* ONE CHILD, so the generation the reap named is the caller's own. *)
    assert (Hgeq : γ' = γc) by set_solver.
    subst γ'.
    (* ...AND THE NUMBER IT CAME BACK AT IS THAT CHILD'S PID, off the two
       tokens' shared generation ([ChildTok.child_tok_pid]). *)
    iDestruct (exit_tok_pid with "Hesc") as "#Hgp".
    iDestruct (child_tok_pid with "Htok Hgp") as %Hpeq.
    subst pidc.
    (* THE REDEMPTION, at the status the copyout placed *)
    iDestruct (gen_pay with "Htok Hesc") as "HQ".
    assert (Hcs0 : Sc' = (∅ : gset gname)) by (rewrite Hcs'; set_solver).
    rewrite Hcs0. subst r.
    iApply ("Hreap" $! h' g xw with "[%] HQ Hpid Hrun Hch Hbuf").
    exact Hby.
  Qed.

End UkWaitCons.
