(* ===================================================================== *)
(* UserChildren.v -- THE PROCESS'S LIVE CHILDREN, AS A RESOURCE.          *)
(*                                                                        *)
(* The key a user process is resumed at carries the GENERATIONS of its    *)
(* live children ([UexecSlot.uvis_ch], the reading of the kernel's        *)
(* per-slot children cell under <wait_lock>), and [UkRun.urun] binds the  *)
(* set existentially exactly as it binds the image, the break, the        *)
(* descriptor view and the working directory.  A program that never       *)
(* forks therefore never names it.  A program that DOES -- one whose      *)
(* wait(2) has to know that the child it is waiting for is still its      *)
(* child, or that it has no others -- needs a carrier for the claim that  *)
(* its children are exactly [S], and that carrier is this file.           *)
(*                                                                        *)
(* THE SHAPE IS [UserCwd]'s, at a set instead of an inum.  A descriptor   *)
(* table is a ghost map because its slots move independently; a children  *)
(* set moves as a whole (fork adds one generation, wait removes one, exit *)
(* hands the lot to init), so the ghost is one variable split in half:    *)
(*                                                                        *)
(*   uch_auth γs S   the ENGINE's half, inside [UkRun.urun], pinned to    *)
(*                   the very [cs] the trap key is at -- that pinning is  *)
(*                   the whole content of the resource, and it is why the *)
(*                   half has to live in [urun] and not beside it.        *)
(*   uch γs S        the PROGRAM's half, a separable resource a proof     *)
(*                   carries into a subroutine, frames across unrelated   *)
(*                   calls, and hands to the syscall that moves it.       *)
(*                                                                        *)
(* WHY HALVES AND NOT A PERSISTENT PIN.  fork and wait move the set, so   *)
(* the value must be updatable; an update needs the whole variable, so    *)
(* each side holds enough that neither can move it alone.  Every other    *)
(* syscall keeps it ([UsysMemOk.usys_ch_ok] is the identity at every      *)
(* number), so the program's half rides through a call untouched and no   *)
(* leaf but fork's, wait's and exit's mentions it.                        *)
(*                                                                        *)
(* THE GENERATION ITSELF ([UexecSlot.uvis_gen]) HAS NO MIRROR HERE.  A    *)
(* process does not need a resource saying what its own name is: the      *)
(* parties that read it are the exit deposit (which names it as the key's *)
(* own projection) and the escrow's payment law, both of which have the   *)
(* key in hand.                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.  (* [sign_extend'] *)
Require Import RiscvExtras.  (* [sext32_64_moi] & co -- the reaped pid's word *)
Require Import ProcGeom.  (* [PIDMAX] -- kernel/param.h, the reaped pid's range *)
Require Import ChildTok.   (* [exit_tok] / [gen_uniq] -- what a reap answers
                              with beside the set it moved *)
Require Import Xv6Cameras. (* [wchG] -- [init_pid_is]'s class *)
Require Import ZombEv.     (* [zev]: the zombie ledger's events -- the reap's receipt *)
Require Import SlotGen.    (* [init_pid_is] -- the saved pid the reaping arm's
                              second disjunct is stated at (T4(b)) *)
Local Open Scope Z_scope.

Section UserChildren.
  (* [Xv6Cameras.uchG]'s capacity -- the one member of [ghost_varG Σ (gset
     gname)] on the whole-system bundle, so there is no second instance
     path and no need for the [OffGv] pinning idiom *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the ENGINE's half: [UkRun.urun] carries it at the key's [uvis_ch] *)
  Definition uch_auth (γs : gname) (S : gset gname) : iProp Σ :=
    ghost_var_frac γs (1/2) S.

  (* the PROGRAM's half *)
  Definition uch (γs : gname) (S : gset gname) : iProp Σ :=
    ghost_var_frac γs (1/2) S.

  Global Instance uch_auth_timeless γs S : Timeless (uch_auth γs S).
  Proof using . apply _. Qed.
  Global Instance uch_timeless γs S : Timeless (uch γs S).
  Proof using . apply _. Qed.

  (* the fragment READS the engine's half: this is the lemma the whole
     resource exists for, and it is why the authority sits INSIDE [urun]
     rather than beside it -- [cs] is bound by [urun]'s own existential, so
     a program learns it only by agreement. *)
  Lemma uch_agree (γs : gname) (S S' : gset gname) :
    uch_auth γs S -∗ uch γs S' -∗ ⌜ S = S' ⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  (* ...and BOTH halves move it, which is what fork, wait and exit spend. *)
  Lemma uch_update (γs : gname) (S S' S'' : gset gname) :
    uch_auth γs S -∗ uch γs S' ==∗ uch_auth γs S'' ∗ uch γs S''.
  Proof using .
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->.
    iMod (ghost_var_update_2 S'' with "H1 H2") as "[$ $]"; [ | done ].
    rewrite Qp.half_half. reflexivity.
  Qed.

  (* the mint, at the set the key carries: an entry constructor keeps the
     authority in the [urun] it is building and hands the fragment to the
     program. *)
  Lemma uch_alloc (S : gset gname) :
    ⊢ |==> ∃ γs : gname, uch_auth γs S ∗ uch γs S.
  Proof using .
    iMod (ghost_var_alloc S) as (γs) "Hc".
    iEval (rewrite -Qp.half_half) in "Hc".
    iDestruct (ghost_var_split with "Hc") as "[HA HF]".
    iModIntro. iExists γs. iFrame "HA HF".
  Qed.

  (* A FRAGMENT AT A SET THE CARRIER IS NOT READING -- [UserCwd.ucwd_any]'s
     shape.  A program that holds its children only so that it can hand
     them to a call it does not care about the result of carries THIS,
     which has no index and therefore costs its lemma statements one
     resource and no binder.  It is also what the kernel-side program
     constructors weaken the fragment to for a pstate. *)
  Definition uch_any (γs : gname) : iProp Σ :=
    (∃ S : gset gname, uch γs S)%I.

  Global Instance uch_any_timeless γs : Timeless (uch_any γs).
  Proof using . apply _. Qed.

  Lemma uch_any_of (γs : gname) (S : gset gname) : uch γs S -∗ uch_any γs.
  Proof using . iIntros "H". iExists S. iExact "H". Qed.

End UserChildren.

(* ===================================================================== *)
(* A RUNNING PROCESS'S OWN PID, AS A HANDLE (lane TRAP-ROWS-4, B).        *)
(* ===================================================================== *)
(* [UkRun.urun] binds the key's pid EXISTENTIALLY, so a program holding a  *)
(* run has no way to NAME its own pid -- which is the wall that kept       *)
(* wait's reaping arm from being redeemable: the arm says “the reaped      *)
(* generation was yours unless YOU are <init>”, and a caller that cannot   *)
(* say which pid it is cannot take either disjunct.  This is [UserCwd.     *)
(* ucwd]'s twin, one value wide and at the SAME class: the engine's half   *)
(* sits inside [urun] pinned to [uvis_pid], the program's half is what an  *)
(* entry constructor hands over.  It is independently what makes           *)
(* getpid(2)'s answer sayable.                                            *)
(*   OVER [Z] AND NOT [mword 32], and the fragment is at [bv_unsigned      *)
(* pidv]: a new [ghost_varG Σ (mword 32)] would be a NEW CLASS in the U    *)
(* tier, which is the very thing T4(b)'s ruling forbade; [ghost_varG Σ Z]  *)
(* is already there for the break and the working directory.              *)
Section UserPid.
  Context `{!ghost_varG Σ Z}.

  (* the ENGINE's half: [UkRun.urun] carries it at [bv_unsigned (uvis_pid W)] *)
  Definition upid_auth (γp : gname) (p : Z) : iProp Σ :=
    ghost_var_frac γp (1/2) p.

  (* the PROGRAM's half *)
  Definition upid (γp : gname) (p : Z) : iProp Σ :=
    ghost_var_frac γp (1/2) p.

  Global Instance upid_auth_timeless γp p : Timeless (upid_auth γp p).
  Proof using . apply _. Qed.
  Global Instance upid_timeless γp p : Timeless (upid γp p).
  Proof using . apply _. Qed.

  (* the fragment READS the engine's half -- the lemma the resource exists
     for, and why the authority sits INSIDE [urun]. *)
  Lemma upid_agree (γp : gname) (p p' : Z) :
    upid_auth γp p -∗ upid γp p' -∗ ⌜ p = p' ⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  (* NO UPDATE LAW.  A process's pid never changes: allocproc chooses it
     once and exec does not move it ([UexecSlot.uvis_pid] is fixed across
     every row of [UsysMemOk]).  A [ucwd_update] twin would be a licence
     nothing needs. *)

  (* the mint, at the pid the key carries: an entry constructor keeps the
     authority in the [urun] it is building and hands the fragment over. *)
  Lemma upid_alloc (p : Z) :
    ⊢ |==> ∃ γp : gname, upid_auth γp p ∗ upid γp p.
  Proof using .
    iMod (ghost_var_alloc p) as (γp) "Hc".
    iEval (rewrite -Qp.half_half) in "Hc".
    iDestruct (ghost_var_split with "Hc") as "[HA HF]".
    iModIntro. iExists γp. iFrame "HA HF".
  Qed.

  Definition upid_any (γp : gname) : iProp Σ := (∃ p : Z, upid γp p)%I.

  Global Instance upid_any_timeless γp : Timeless (upid_any γp).
  Proof using . apply _. Qed.

  Lemma upid_any_of (γp : gname) (p : Z) : upid γp p -∗ upid_any γp.
  Proof using . iIntros "H". iExists p. iExact "H". Qed.

End UserPid.

(* ===================================================================== *)
(* WHAT A REAP DOES TO THE READING, as the one PURE row every party from  *)
(* kwait to the trap loop relays: AT MOST ONE generation leaves it -- the *)
(* one that was reaped, which [WaitInv.children_inv_reap] takes out of    *)
(* both columns of the wait-lock invariant -- and every failing arm       *)
(* leaves it alone, because the C returns before [pp->parent = 0].  WHICH *)
(* generation left, and the escrow that redeems it, are [wait_ans] below; *)
(* this is that answer's pure shadow, for the relays that only need to    *)
(* know the reading moved.  Outside the section: it names no ghost and no *)
(* class.                                                                 *)
(* ===================================================================== *)
Definition ch_reaped (cs cs' : gset gname) : Prop :=
  cs' = cs \/ exists γ' : gname, cs' = cs ∖ {[γ']}.

Lemma ch_reaped_refl (cs : gset gname) : ch_reaped cs cs.
Proof. left. reflexivity. Qed.

Lemma ch_reaped_del (cs : gset gname) (γ' : gname) : ch_reaped cs (cs ∖ {[γ']}).
Proof. right. exists γ'. reflexivity. Qed.

(* ===================================================================== *)
(* WHAT A WAIT ANSWERS, IN THE TWO ARMS wait() HAS -- the ONE predicate   *)
(* every party from kwait to the program relays.                         *)
(*                                                                       *)
(* IT FAILED and returned -1: the caller has no children at all, or it    *)
(* was killed, or copyout could not place the status.  Nothing was        *)
(* reaped (the C returns before [pp->parent = 0]), so the caller's        *)
(* children reading does not move.  THE -1 ARM CLAIMS NOTHING ABOUT THE   *)
(* SET, and that is forced by the code and not a weakening: two of those  *)
(* three exits happen with children present.                             *)
(*                                                                       *)
(* IT REAPED, and then it returns THAT child's pid and three things ride  *)
(* with it:                                                              *)
(*   the reaped generation leaves the caller's reading                    *)
(*     ([WaitInv.children_inv_reap] takes it out of both columns of the   *)
(*     wait-lock invariant, so the move is [cs ∖ {γ'}] whether the zombie *)
(*     was the caller's own child or an orphan reparented to it);         *)
(*   the ESCROW ([ChildTok.exit_tok]) the zombie's exit parked, at the    *)
(*     status its [p->xstate] cell holds -- which is the very word the    *)
(*     copyout put in the caller's buffer;                                *)
(*   and PID UNIQUENESS over the caller's reading                         *)
(*     ([ChildTok.gen_uniq]): no other child of this caller carries the   *)
(*     returned pid, which is what makes the returned NUMBER name the     *)
(*     generation the escrow is at.  A parent holding                     *)
(*     [ChildTok.child_tok] for a child it forked spends the two together *)
(*     ([ChildTok.gen_uniq_tok] then [ChildTok.gen_pay]).                 *)
(*                                                                       *)
(* THE ARMS ARE DISJOINT AT THE RETURN VALUE: a reaped pid is in          *)
(* [1, PIDMAX], so a caller that reads a nonnegative result knows it is   *)
(* on the second arm without holding anything. *)
(* ===================================================================== *)
(* THE TWO ARMS ARE DISJOINT AT THE RETURN VALUE, as a pure fact about the
   word: [PIDMAX] is 1000, so a pid in [1, PIDMAX] sign-extends to a small
   POSITIVE 64-bit word, while a failing wait returns the all-ones one.
   This is what [SlotGen.gen_halves_at]'s range buys (lane TRAP-ROWS-3,
   T4(c)). *)
Lemma sext32_rng_not_neg1 (w : mword 32) :
  (1 <= bv_unsigned w <= PIDMAX)%Z ->
  (sign_extend' 64 w : mword 64) <> (mword_of_int (-1) : mword 64).
Proof.
  intros Hw Hm1.
  unfold PIDMAX in Hw.
  assert (H31 : (2 ^ 31)%Z = 2147483648) by (vm_compute; reflexivity).
  assert (H64 : (2 ^ 64)%Z = 18446744073709551616) by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ w) as [Hr0 _].
  assert (Hval : bv_unsigned (sign_extend' 64 w : mword 64) = bv_unsigned w).
  { rewrite sext32_64_moi moi64_unsigned. unfold bv_signed.
    assert (Hsw : bv_swrap 32 (bv_unsigned w) = bv_unsigned w).
    { apply bv_swrap_small.
      assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
      rewrite Hhm. lia. }
    rewrite Hsw. apply bvw64_small. rewrite H64. lia. }
  assert (Hm : bv_unsigned (mword_of_int (-1) : mword 64)
               = 18446744073709551615%Z) by (vm_compute; reflexivity).
  rewrite Hm1 Hm in Hval. lia.
Qed.

(* ===================================================================== *)
(* THE CALLER IS <INIT>, AS A GHOST -- AND IT STAYS ON THIS SIDE OF THE   *)
(* PARK (lane TRAP-ROWS-3/4, T4(b)).                                      *)
(* ===================================================================== *)
(* [wchG] IS NOT A CLASS THE U TIER DECLARES, and it never will be: the   *)
(* moment [wait_ans] mentioned a ghost of it, fifty-four files below      *)
(* [UexecRet] would have to carry [Context `{!wchG Σ}].  So the           *)
(* generation-level reading lives HERE, in a section of its own that      *)
(* nothing below the kernel's own relays enters, and [wait_ans] below is  *)
(* stated at PURE [mword 32] parameters instead -- the caller's pid and   *)
(* <init>'s.  kwait converts between the two ([ProofKwait.kw_reap]).      *)
Section GenIsInit.
  Context `{!ctokG Σ}.
  Context `{!wchG Σ}.

  (* ===================================================================
     THE CALLER IS <INIT>, AT THE CALLER'S OWN GENERATION (lane
     TRAP-ROWS-3, T4(b)).
     ===================================================================
     In the C, [reparent] (kernel/proc.c:325) sets [pp->parent = initproc]
     ONLY, so the orphan column of the wait-lock invariant is non-empty at
     <init>'s address and nowhere else ([WaitInv]'s [orph_at_init]
     conjunct).  A reaper that is not <init> therefore reaps out of its OWN
     row, and the reaping arm can say so -- but only under this disjunct,
     because <init> itself really does reap orphans.
       IT IS THE KERNEL'S OWN FORM, and it stops at kwait.  [wait_ans]
     below says the same thing at PURE pids, because the relays between
     kwait and the trap loop carry no [wchG]; [gen_is_init_pid] is the
     step across, taken once, in [ProofKwait.kw_reap], against the
     caller's own [ChildTok.gen_pid]. *)
  Definition gen_is_init (g : gname) : iProp Σ :=
    (∃ p0 : mword 32, init_pid_is p0 ∗ gen_pid g p0)%I.

  Global Instance gen_is_init_persistent g : Persistent (gen_is_init g).
  Proof using . rewrite /gen_is_init. apply _. Qed.

  (* the pid form, for a caller that can name its own pid *)
  Lemma gen_is_init_pid (g : gname) (pidv : mword 32) :
    gen_is_init g -∗ gen_pid g pidv -∗ ∃ p0 : mword 32,
      init_pid_is p0 ∗ ⌜pidv = p0⌝.
  Proof using .
    iIntros "(%p0 & #Hi & #Hp0) Hp".
    iDestruct (gen_pid_agree with "Hp Hp0") as %->.
    iExists p0. iFrame "Hi". done.
  Qed.

  (* ...AND THE REFUTATION A FORKED CHILD SPENDS.  Its fork handed it
     [init_pid_is p0] with [⌜its own pid <> p0⌝] ([UkFork]'s child arm);
     the reaping arm's second disjunct would make its pid <init>'s, and
     the saved pid AGREES with itself. *)
  Lemma gen_is_init_ne (g : gname) (pidv p0 : mword 32) :
    pidv <> p0 ->
    init_pid_is p0 -∗ gen_pid g pidv -∗ gen_is_init g -∗ False.
  Proof using .
    intro Hne. iIntros "#Hi Hp Hg".
    iDestruct (gen_is_init_pid with "Hg Hp") as (p1) "[#Hi1 %Heq]".
    iDestruct (init_pid_is_agree with "Hi Hi1") as %<-.
    exfalso. exact (Hne Heq).
  Qed.

End GenIsInit.

Section WaitAns.
  Context `{!ctokG Σ}.

  (* ...AND THE FAILING ARM CARRIES ITS REASON, at a NULL status pointer
     (lane TRAP-ROWS, T4).  wait() returns -1 on THREE exits, not two:
       * [!havekids] -- the caller's own children column is empty;
       * [killed(p)] -- the caller is dead, and [killed()] hands back this
         incarnation's one-shot;
       * a failing [copyout] of the status word -- which happens with a
         ZOMBIE child present and no shot at all.
     The third is what the row is CONDITIONED on: it is guarded by
     [addr != 0] in the C, and every wait leaf in the tree forces
     [uint a1 = 0] ([UkRunSys.wp_uk_ecall_wait_null] / [_any],
     [UkInit.wp_kinit_wait]), so at a null status pointer it is
     unreachable and the other two are the whole story.
     [nullst] IS THE GUARD, not a claim: a caller that passed a real
     pointer gets the landed row back and nothing more.
     BOTH INFORMATIVE DISJUNCTS ARE PERSISTENT, so a caller reads the
     reason off without spending the arm. *)
  (* THE REASON ITSELF, named once: the -1 arm's second conjunct, and the
     only thing the three failing tails have to produce. *)
  Definition wait_why (cs : gset gname) (gn : gname) (nullst : bool) : iProp Σ :=
    (⌜nullst = false⌝ ∨ ⌜cs = (∅ : gset gname)⌝ ∨ kill_shot gn)%I.

  Global Instance wait_why_persistent (cs : gset gname) (gn : gname) (b : bool) :
    Persistent (wait_why cs gn b).
  Proof using . rewrite /wait_why. apply _. Qed.

  (* ...AND THE REAPING ARM SAYS THE RETURNED PID IS A REAL PID (lane
     TRAP-ROWS-3, T4(c)).  [rv] is the ZOMBIE's [p->pid], read off its own
     block, and every block's registration now carries the range
     <allocpid> hands out ([SlotGen.gen_halves_at]).  It is what makes the
     TWO ARMS DISJOINT AT THE RETURN VALUE -- the header above has claimed
     that since the row was written, and until now nothing proved it: the
     word the reap leaves in a0 is [sign_extend' 64 rv], and refuting
     [= -1] needs the upper bound as well as the nonzero.  A caller that
     sees -1 is therefore on the FAILING arm and may read its reason. *)
  (* ...AND WHOSE CHILD THE REAPED ZOMBIE WAS (lane TRAP-ROWS-3/4, T4(b)).
     [pidv] is the CALLER'S OWN pid and [ip] is <init>'s; the reaping arm
     says the generation it took out of the set was in the caller's own
     column -- unless the caller IS <init>, which is the one process that
     reaps orphans ([reparent], kernel/proc.c:325, hands every orphan to
     <initproc> and to no one else).  Without it a caller that never reads
     the returned pid -- sh's [wait(0)] does not -- cannot tell whether it
     reaped its own child or someone's orphan, and so cannot redeem its
     [ChildTok.child_tok].
       TWO PURE [mword 32] PARAMETERS AND NOT A GHOST.  A ghost reading
     ([gen_is_init] above) would put [Xv6Cameras.wchG] on every file that
     relays this row, which is the whole U tier; a NUMBER rides the relays
     the way [nullst] already does and costs them nothing.  kwait is where
     the two meet: it holds the caller's registration and the sealed pid,
     and hands this arm the equation ([ProofKwait.kw_reap]).  Both
     disjuncts are PURE, hence persistent. *)
  (* AT THE LITERAL 1 (lane TRAP-ROWS-4, B1b).  <init>'s pid is not a
     parameter any more: the C carves [int nextpid = 1], userinit's
     allocproc is the FIRST allocation in the boot order and <started> is
     published after it, so <init>'s pid IS 1 and both sides of this row
     name the same number.  [ip] used to ride here beside [pidv] because
     neither side could name the other's; with the literal there is
     nothing left to tie. *)
  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst
     ∨ ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']} /\ (1 <= bv_unsigned rv <= PIDMAX)%Z⌝ ∗
         ⌜γ' ∈ cs \/ pidv = (mword_of_int 1 : mword 32)⌝ ∗
         exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.

  (* the pure row, which is all the twenty-odd relays between kwait and the
     program ever look at *)
  Lemma wait_ans_reaped (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) :
    wait_ans rv xs cs cs' gn nullst pidv -∗ ⌜ch_reaped cs cs'⌝.
  Proof using .
    iIntros "[[[_ %He] _] | (%γ' & [%He _] & _ & _ & _)]"; iPureIntro.
    - left. exact He.
    - right. exists γ'. exact He.
  Qed.

  (* ...AND THE ARM A -1 RETURN IS ON.  [PIDMAX] is 1000, so a reaped pid
     sign-extends to a small positive word and never to the -1 a failing
     wait returns: at [r = -1] the reaping arm is unreachable and what is
     left is the failing arm, with its reason.  This is the whole point of
     the range on the registration, and it is what
     [SpecUsertrap.ut_live_out]'s wait clause is proved from. *)
  (* AT A -1 RETURN THE WHOLE ANSWER IS PERSISTENT, which is what lets
     usertrap's +0xa6 block read the reason off the syscall channel and put
     the channel back -- the [Hrwhy] idiom the console read already uses
     ([SpecFileread.console_receipt_m1_why]). *)
  Lemma wait_ans_m1 (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) :
    (sign_extend' 64 rv : mword 64) = (mword_of_int (-1) : mword 64) ->
    wait_ans rv xs cs cs' gn nullst pidv -∗
    ⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst.
  Proof using .
    intro Hm1. iIntros "[[%Hf #Hwhy] | (%γ' & [_ %Hrng] & _ & _ & _)]".
    - iSplitR; [ iPureIntro; exact Hf | ]. iExact "Hwhy".
    - exfalso. exact (sext32_rng_not_neg1 rv Hrng Hm1).
  Qed.

  (* the failing arm, for the three exits that reap nothing.  Each supplies
     its OWN reason: the childless exit the empty column, the killed exit
     the one-shot, the copyout exit the guard's refutation. *)
  Lemma wait_ans_neg (xs : Z) (cs : gset gname) (gn : gname) (nullst : bool)
      (pidv : mword 32) :
    wait_why cs gn nullst -∗
    wait_ans (mword_of_int (-1) : mword 32) xs cs cs gn nullst pidv.
  Proof using .
    iIntros "Hwhy". iLeft. iSplitR; [ iPureIntro; split; reflexivity | ].
    iExact "Hwhy".
  Qed.

  (* ...and the three ways to build that reason *)
  Lemma wait_why_notnull (cs : gset gname) (gn : gname) (nullst : bool) :
    nullst = false -> ⊢ wait_why cs gn nullst.
  Proof using . intros ->. rewrite /wait_why. by iLeft. Qed.

  Lemma wait_why_empty (cs : gset gname) (gn : gname) (nullst : bool) :
    cs = (∅ : gset gname) -> ⊢ wait_why cs gn nullst.
  Proof using . intro He. rewrite /wait_why. iRight. by iLeft. Qed.

  Lemma wait_why_shot (cs : gset gname) (gn : gname) (nullst : bool) :
    kill_shot gn -∗ wait_why cs gn nullst.
  Proof using . iIntros "H". rewrite /wait_why. iRight. iRight. iExact "H". Qed.

End WaitAns.

(* ===================================================================== *)
(* THE SAME ANSWER, AT THE GENERATION -- kwait's OWN FORM (lane           *)
(* TRAP-ROWS-3/4, T4(b)).                                                 *)
(* ===================================================================== *)
(* What the reaper can PRODUCE is a ghost: the orphan column of the        *)
(* wait-lock invariant hands it [WaitInv.init_ident], and against its own  *)
(* block's slot-generation quarter that says “the generation I am running  *)
(* as is <init>'s”.  What the answer has to TRAVEL as is a number, because *)
(* the relays below the syscall boundary carry no [wchG].                  *)
(*   So kwait's eleven internal block lemmas are stated at THIS form and   *)
(* the step across is taken ONCE, at [wp_kwait_sconf]'s own exit, where    *)
(* [SlotGen.init_pid_is] (kwait's contract premise) and the caller's       *)
(* [ChildTok.gen_pid] (off its block) are both in hand --                  *)
(* [wait_ans_of_gen].                                                      *)
(* ===================================================================== *)
(* THE ZOMBIE LEDGER'S GHOST (NI-LEDGER-REST, design ni-zombie-ledger.md  *)
(* D2): a mono-list of [ZombEv.zev] at the canonical                     *)
(* [Xv6Cameras.wzl_name].  The authority rides <wait_lock>'s payload      *)
(* ([WaitInv.wait_res_at]'s last conjunct); kexit appends [ZExit] at its  *)
(* ZOMBIE store and kwait [ZReap] at its reap, both under the lock.  No   *)
(* tie (ruling R2): the zombie state lives in the per-slot locks, so      *)
(* [zombies_of h] is the zombie set by construction of the two proofs.   *)
(* HERE and not in [WaitInv] because the reap's receipt is part of        *)
(* [wait_ans_led] below, and [WaitInv] imports this file.                 *)
(* ===================================================================== *)
Section ZombLedger.
  Context `{!wchG Σ}.

  Definition zomb_led_auth (h : list zev) : iProp Σ :=
    own wzl_name (●ML (h : list (leibnizO zev))).
  Definition zomb_led_lb (h : list zev) : iProp Σ :=
    own wzl_name (◯ML (h : list (leibnizO zev))).

  Global Instance zomb_led_lb_persistent h : Persistent (zomb_led_lb h).
  Proof using . rewrite /zomb_led_lb. apply _. Qed.
  Global Instance zomb_led_lb_timeless h : Timeless (zomb_led_lb h).
  Proof using . rewrite /zomb_led_lb. apply _. Qed.
  Global Instance zomb_led_auth_timeless h : Timeless (zomb_led_auth h).
  Proof using . rewrite /zomb_led_auth. apply _. Qed.

  Lemma zomb_led_auth_lb h : zomb_led_auth h -∗ zomb_led_auth h ∗ zomb_led_lb h.
  Proof using .
    rewrite /zomb_led_auth /zomb_led_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (h : list (leibnizO zev))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma zomb_led_lb_prefix h h' : zomb_led_auth h -∗ zomb_led_lb h' -∗ ⌜h' `prefix_of` h⌝.
  Proof using .
    rewrite /zomb_led_auth /zomb_led_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* two lower bounds of the one ledger are comparable *)
  Lemma zomb_led_lb_lb h h' :
    zomb_led_lb h -∗ zomb_led_lb h' -∗ ⌜h `prefix_of` h' \/ h' `prefix_of` h⌝.
  Proof using .
    rewrite /zomb_led_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    by iPureIntro.
  Qed.

  Lemma zomb_led_auth_grow h e :
    zomb_led_auth h ==∗ zomb_led_auth (h ++ [e]) ∗ zomb_led_lb (h ++ [e]).
  Proof using .
    rewrite /zomb_led_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((h ++ [e]) : list (leibnizO zev))) with "Ha") as "Ha".
    { apply mono_list_update. by exists [e]. }
    iModIntro. iApply (zomb_led_auth_lb with "Ha").
  Qed.

  (* the receipt an exit or a reap hands back: event [e] was appended right
     after history [h].  The name is canonical, so it carries none. *)
  Definition zomb_receipt (h : list zev) (e : zev) : iProp Σ :=
    zomb_led_lb (h ++ [e]).
  Global Instance zomb_receipt_persistent h e : Persistent (zomb_receipt h e).
  Proof using . rewrite /zomb_receipt. apply _. Qed.
  Global Instance zomb_receipt_timeless h e : Timeless (zomb_receipt h e).
  Proof using . rewrite /zomb_receipt. apply _. Qed.

  (* THE TWO GHOST STEPS: kexit's at its ZOMBIE store (actor: the exiting
     process's own proc word; the status it exits with), kwait's at its
     reap (actor: the reaper; the reaped child's pid). *)
  Lemma zomb_exit h (act : mword 64) (pid : mword 32) (xs : Z) :
    zomb_led_auth h ==∗
    zomb_led_auth (h ++ [ZExit act pid xs]) ∗ zomb_receipt h (ZExit act pid xs).
  Proof using . apply zomb_led_auth_grow. Qed.

  Lemma zomb_reap h (act : mword 64) (pid : mword 32) :
    zomb_led_auth h ==∗
    zomb_led_auth (h ++ [ZReap act pid]) ∗ zomb_receipt h (ZReap act pid).
  Proof using . apply zomb_led_auth_grow. Qed.

End ZombLedger.

Section WaitAnsGen.
  Context `{!ctokG Σ}.
  Context `{!wchG Σ}.

  Definition wait_ans_gen (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst
     ∨ ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']} /\ (1 <= bv_unsigned rv <= PIDMAX)%Z⌝ ∗
         (⌜γ' ∈ cs⌝ ∨ gen_is_init gn) ∗
         exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.

  (* THE ANSWER WITH THE REAP'S RECEIPT (design ni-zombie-ledger.md D4):
     [wait_ans] verbatim, with the zombie ledger's receipt of the reap --
     [ZReap act rv], appended by the reaper [act] -- as the reaping arm's
     first conjunct.  kwait's led twin [SpecKwait.wp_kwait_led_sconf_body]
     answers this; [wait_ans_led_post] is the step back to the landed row. *)
  Definition wait_ans_led (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) (act : mword 64) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst
     ∨ (∃ h, zomb_receipt h (ZReap act rv)) ∗
       ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']} /\ (1 <= bv_unsigned rv <= PIDMAX)%Z⌝ ∗
         ⌜γ' ∈ cs \/ pidv = (mword_of_int 1 : mword 32)⌝ ∗
         exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.

  Lemma wait_ans_led_post (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) (act : mword 64) :
    wait_ans_led rv xs cs cs' gn nullst pidv act -∗
    wait_ans rv xs cs cs' gn nullst pidv.
  Proof using .
    iIntros "[Hneg | [_ Hr]]"; [ iLeft; iExact "Hneg" | iRight; iExact "Hr" ].
  Qed.

  (* ...and the way in: the landed row, plus the receipt wherever a pid came
     back.  The -1 answer is never in [1, PIDMAX], so the reaping arm of
     [wait_ans] always finds the receipt's arm of the side row. *)
  Lemma wait_ans_led_of (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidv : mword 32) (act : mword 64) :
    wait_ans rv xs cs cs' gn nullst pidv -∗
    (⌜rv = (mword_of_int (-1) : mword 32)⌝ ∨ ∃ h, zomb_receipt h (ZReap act rv)) -∗
    wait_ans_led rv xs cs cs' gn nullst pidv act.
  Proof using .
    iIntros "[Hneg | (%γ' & [%Hc %Hrng] & Hr)] Hz"; [ iLeft; iExact "Hneg" | ].
    iDestruct "Hz" as "[%Hm1 | Hz]".
    - exfalso. subst rv. unfold PIDMAX in Hrng.
      assert (Hv : bv_unsigned (mword_of_int (-1) : mword 32) = 4294967295%Z)
        by (vm_compute; reflexivity).
      rewrite Hv in Hrng. lia.
    - iRight. iFrame "Hz". iExists γ'. iFrame "Hr". by iPureIntro.
  Qed.

  (* the failing arm, exactly as [wait_ans_neg] *)
  Lemma wait_ans_gen_neg (xs : Z) (cs : gset gname) (gn : gname)
      (nullst : bool) :
    wait_why cs gn nullst -∗
    wait_ans_gen (mword_of_int (-1) : mword 32) xs cs cs gn nullst.
  Proof using .
    iIntros "Hwhy". iLeft. iSplitR; [ iPureIntro; split; reflexivity | ].
    iExact "Hwhy".
  Qed.

  (* THE ONE STEP ACROSS, and it is two agreements: the caller's own
     registration says which pid its generation was given, and the sealed
     pid says which pid <init> was given. *)
  Lemma wait_ans_of_gen (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) (pidme : mword 32) :
    gen_pid gn pidme -∗ init_pid_is (mword_of_int 1 : mword 32) -∗
    wait_ans_gen rv xs cs cs' gn nullst -∗
    wait_ans rv xs cs cs' gn nullst pidme.
  Proof using .
    iIntros "#Hgp #Hi [Hneg | (%γ' & %Hrng & Hoci & Hesc & Huniq)]".
    - iLeft. iExact "Hneg".
    - iRight. iExists γ'. iSplitR; [ iPureIntro; exact Hrng | ].
      iSplitR "Hesc Huniq"; [ | iFrame "Hesc Huniq" ].
      iDestruct "Hoci" as "[%Hin | #Hgi]"; [ by iPureIntro; left | ].
      iDestruct (gen_is_init_pid with "Hgi Hgp") as (p1) "[#Hi1 %Heq]".
      iDestruct (init_pid_is_agree with "Hi Hi1") as %<-.
      iPureIntro. right. exact Heq.
  Qed.

End WaitAnsGen.
