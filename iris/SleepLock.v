(* SleepLock.v -- the separation-logic sleeplock (kernel/sleeplock.c),
   mirroring the spinlock layer in WpLock.v one level up:

     sleeplocked_q γ q slk pid
                     -- WHAT IT MEANS TO HOLD THE SLEEPLOCK AT [slk]: the
                        ownership token carrying the FRACTION its holder
                        deposited, AND the lock's [pid] field, at [pid]
     sleeplocked γ slk pid
                     -- the same with the fraction forgotten; what a client
                        that does not track holders says
     sl_res_gen       -- the resource protected by the INNER spinlock:
                        ∃ v, locked word ↦₄ v ∗
                          (v = 0 ∗ sl_free_hold γ slk ∗ R
                           ∨ v ≠ 0 ∗ ∃ q, sl_hauth γ q ∗ H q)
     is_sleeplock_gen -- the sleeplock's name + the inner spinlock (is_lock,
                        named "sleep lock") protecting it  (persistent)

   When the sleeplock word is 0 (free) the inner critical section holds the
   token together with the pid field (pinned 0: both initsleeplock and
   releasesleep write it back to 0), and the protected resource R;
   acquiresleep takes both out and re-closes with the "held" disjunct, so the
   HOLDER of a sleeplock carries [sleeplocked_q γ q slk pid ∗ R] -- the pid
   field rides with the holder exactly like the spinlock's cpu word rides with
   the caller.  The held disjunct records the word's non-zeroness in the shape
   the c.beqz/c.bnez tests consume.

   THE pid FIELD IS INSIDE THE TOKEN, and that is the point of the pairing
   rather than an implementation detail.  It is written exactly twice (to
   [myproc()->pid] by acquiresleep, back to 0 by releasesleep), read by
   holdingsleep and by nobody else, and it moves between the free arm and the
   holder in lockstep with the ghost.  As a separate row it was threaded by
   every client from the buffer cache up to sys_unlink, each of which had to
   name which pid was in it and hand it back beside the token; there is no
   state in which one travels without the other.  [sleeplocked_q_pid] is the
   accessor the two stores use.

   ==================================================================== *)
(*  THE HOLDER DEPOSIT [H], AND WHAT IT BUYS: A NON-BLOCKING acquiresleep.

   The held disjunct used to be PURE ([⌜v ≠ 0⌝] and nothing else), and that
   is exactly why no caller could ever prove a sleeplock FREE.  Anything a
   would-be acquirer can learn about the lock it learns by opening the inner
   spinlock, and a purely pure held arm says only "the word is nonzero",
   which is not refutable from outside.

   THE REFUTATION HAS TO COST THE ACQUIRER SOMETHING, and that is forced, not
   a design choice.  Suppose the held arm's resources could be manufactured
   from the free arm's alone.  A client's evidence [P] that the lock is free
   must satisfy [P ∗ (held arm) ⊢ False]; but [P] is a frame for the acquire's
   ghost step, and a frame-preserving update from the free arm to the held arm
   would then carry [P] across it -- so [P ∗ (held arm)] is consistent after
   all.  The acquirer must therefore bring a resource of its OWN and leave it
   in the lock: [H q], the DEPOSIT.

   So [sl_res_gen] is indexed by [H : Qp -> iProp Σ] and acquiresleep's
   contract consumes [H q] where releasesleep's hands it back.  Two
   instantiations exist:

     [sl_untracked] (= fun _ => emp) -- the ordinary sleeplock.  Nothing is
        deposited, nothing can be refuted, no caller pays anything, and
        [is_sleeplock] / [sl_res] / [new_sleeplock] are its shorthands, so
        every existing client reads exactly as before.

     [slh_tok γ] -- the TRACKED sleeplock.  [slh_tok γ q] is a q-share of the
        "somebody may hold this sleeplock" right, [slh_auth γ t] is the total
        outstanding, and [slh_auth γ None] -- the AUTHORITATIVE ZERO -- says
        no share exists anywhere, hence no deposit, hence the held arm is
        refuted and the lock is FREE.  That is the premise the non-blocking
        acquiresleep takes in place of a lock-order bound
        (claude-notes/projects/iput-acquiresleep.md).

   WHY THE SHARE IS A FRACTION rather than a whole token: one inode reference
   can be shared by many [struct file]s, all of which may race for the inode's
   sleeplock, so the right to attempt the lock has to split along with the
   reference.  [ufrac] (unbounded fractions) rather than [frac] because the
   total is a sum over however many references exist and is not capped at 1.

   WHY THE DEPOSITED FRACTION IS PINNED: the holder's token carries [q] and
   agrees with the [sl_hauth] authority that rides with the deposit, so a
   releaser recovers EXACTLY the share it put in.  Handing back "some"
   fraction would leave a client whose reference is itself split unable to
   rebuild its own share.

   struct sleeplock layout (sleeplock.h, offsets from the disassembly):
   locked@0 (4B), lk@8 (24B inner spinlock: word@8 name@16 cpu@24),
   name@32 (8B), pid@40 (4B). *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth ufrac updates local_updates.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Local Open Scope Z_scope.

Section SleepLock.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{XI : CurCtx}.

  (* ---- geometry, in the EXACT instruction address forms so the cells
     unify with the leaf and call specs without rewriting:
     [sl_lk] is the [addi a0+8] form (the &lk->lk argument every inner
     acquire/release receives); [sl_lkcpu] is acquire/release/holding's
     [a_cpu] form instantiated at lk0 = sl_lk slk; [sl_name_field]/[sl_pid]
     are the sd/sw/lw store-address forms. *)
  Definition sl_lk (slk : mword 64) : mword 64 :=
    add_vec slk (sign_extend' 64 (mword_of_int 8 : mword 12)).
  Definition sl_lkcpu (slk : mword 64) : mword 64 :=
    add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12)).
  Definition sl_name_field (slk : mword 64) : mword 64 :=
    add_vec slk (sign_extend' 64 (mword_of_int 32 : mword 12)).
  Definition sl_pid (slk : mword 64) : mword 64 :=
    add_vec slk (sign_extend' 64 (mword_of_int 40 : mword 12)).

  (* the sleeplock's own name field (+32), mirroring [lock_name]: written
     once by initsleeplock and then discarded, so persistent. *)
  (* RAW (context-free), for the same reason as [WpLock.lock_name]: name
     metadata inside the persistent handle must not drag a context in. *)
  Definition sl_name (slk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64,
       word_pointsto (sl_name_field slk) DfracDiscarded p ∗ p ↦ₛ□ s)%I.

  Global Instance sl_name_persistent slk s : Persistent (sl_name slk s).
  Proof. apply _. Qed.

  (* ===================================================================== *)
  (*  THE GHOST STATE ([Xv6Cameras.slhUR], under the sleeplock's own gname).    *)
  (* ===================================================================== *)

  (* the holder's exclusive GHOST token, carrying the fraction it deposited.
     Deliberately NOT the spinlock's [locked], which is keyed by the holding
     HART -- a sleeplock is held by a PROCESS (its pid rides in [sl_pid]),
     across context switches and possibly harts.

     INTERNAL.  What a holder carries is [sleeplocked_q] below, which is this
     PLUS the pid field; the bare token exists only so that the three ghost
     laws (exclusivity, agreement, re-targeting) can be stated where they
     belong -- over the ghost -- and lifted once. *)
  Definition sl_htok (γ : gname) (q : Qp) : iProp Σ :=
    own γ ((◯E (q : leibnizO Qp), ε) : slhUR).

  (* the authority that pins it, and which rides with the DEPOSIT inside the
     lock, so that opening the held arm as the holder proves the deposited
     fraction is the holder's own. *)
  Definition sl_hauth (γ : gname) (q : Qp) : iProp Σ :=
    own γ ((●E (q : leibnizO Qp), ε) : slhUR).

  (* "somebody may hold this sleeplock", a q-share of it *)
  Definition slh_tok (γ : gname) (q : Qp) : iProp Σ :=
    own γ ((ε, ◯ (Some q : optionUR ufracR)) : slhUR).

  (* the total outstanding; [None] is the AUTHORITATIVE ZERO *)
  Definition slh_auth (γ : gname) (t : option Qp) : iProp Σ :=
    own γ ((ε, ● (t : optionUR ufracR)) : slhUR).

  (* ===================================================================== *)
  (*  WHAT IT MEANS TO HOLD A SLEEPLOCK: THE TOKEN *AND* THE pid FIELD.

     [lk->pid] is not a resource a holder should have to manage.  It is
     written exactly twice -- to [myproc()->pid] by acquiresleep and back to
     0 by releasesleep -- it is readable by holdingsleep and by nobody else,
     and it moves between the lock's free arm and the holder in lockstep
     with the ghost token.  Carrying it separately meant every client from
     the buffer cache to sys_unlink threaded a second row that says nothing
     it did not already know, and had to be reminded which pid was in it.

     So it lives here.  [sleeplocked_q γ q slk pid] is "I hold the sleeplock
     at [slk], I deposited [q], and its pid field says [pid]" -- one row.
     [sleeplocked_q_pid] is the accessor the two stores use.

     WHY TWO EXTRA ARGUMENTS AND NOT ONE.  [pid] is the interesting one, but
     [sl_pid] is an ADDRESS computed from the lock's own, and nothing ties
     the gname to the address: [is_sleeplock_gen] relates them, but it is
     persistent and a holder need not have it in hand.  Tying them would
     mean a second persistent agreement ghost minted at construction, to
     save an argument every use site already has in scope. *)
  Definition sleeplocked_q (γ : gname) (q : Qp) (slk : mword 64)
      (pid : mword 32) : iProp Σ :=
    (sl_htok γ q ∗ sl_pid slk ↦₄ pid)%I.

  (* the holder token with the fraction forgotten: what [sl_res]'s clients
     that do not track holders (every untracked sleeplock) carry. *)
  Definition sleeplocked (γ : gname) (slk : mword 64) (pid : mword 32) : iProp Σ :=
    (∃ q : Qp, sleeplocked_q γ q slk pid)%I.

  (* THE FIELD, OPENED FOR A STORE AND CLOSED AT THE NEW VALUE.  acquiresleep
     stores [myproc()->pid] into it and releasesleep stores 0; both are
     ordinary store leaves, so both want the bare cell for one instruction. *)
  Lemma sleeplocked_q_pid γ q slk pid :
    sleeplocked_q γ q slk pid -∗
    sl_pid slk ↦₄ pid ∗
    (∀ pid' : mword 32, sl_pid slk ↦₄ pid' -∗ sleeplocked_q γ q slk pid').
  Proof.
    iIntros "[Htok $]". iIntros (pid') "Hpid". iFrame "Htok Hpid".
  Qed.

  Lemma sleeplocked_pid γ slk pid :
    sleeplocked γ slk pid -∗
    sl_pid slk ↦₄ pid ∗
    (∀ pid' : mword 32, sl_pid slk ↦₄ pid' -∗ sleeplocked γ slk pid').
  Proof.
    iIntros "[%q Hq]". iDestruct (sleeplocked_q_pid with "Hq") as "[$ Hback]".
    iIntros (pid') "Hpid". iExists q. iApply ("Hback" with "Hpid").
  Qed.

  Global Instance sl_htok_timeless γ q : Timeless (sl_htok γ q).
  Proof. apply _. Qed.
  Global Instance sleeplocked_q_timeless γ q slk pid :
    Timeless (sleeplocked_q γ q slk pid).
  Proof. apply _. Qed.
  Global Instance sl_hauth_timeless γ q : Timeless (sl_hauth γ q).
  Proof. apply _. Qed.
  Global Instance slh_tok_timeless γ q : Timeless (slh_tok γ q).
  Proof. apply _. Qed.
  Global Instance slh_auth_timeless γ t : Timeless (slh_auth γ t).
  Proof. apply _. Qed.
  Global Instance sleeplocked_timeless γ slk pid : Timeless (sleeplocked γ slk pid).
  Proof. apply _. Qed.

  (* ---- the excl_auth half: exclusivity and agreement ------------------ *)

  Lemma sl_htok_exclusive γ q q' :
    sl_htok γ q -∗ sl_htok γ q' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    destruct Hv as [Hv1 _].
    destruct (proj1 (excl_auth_frag_op_valid _ _) Hv1).
  Qed.

  Lemma sleeplocked_q_exclusive γ q q' slk slk' pid pid' :
    sleeplocked_q γ q slk pid -∗ sleeplocked_q γ q' slk' pid' -∗ False.
  Proof.
    iIntros "[H1 _] [H2 _]". iApply (sl_htok_exclusive with "H1 H2").
  Qed.

  Lemma sleeplocked_exclusive γ slk slk' pid pid' :
    sleeplocked γ slk pid -∗ sleeplocked γ slk' pid' -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct "H1" as (q) "H1". iDestruct "H2" as (q') "H2".
    iApply (sleeplocked_q_exclusive with "H1 H2").
  Qed.

  (* THE PINNING LAW: the deposit's authority agrees with the holder's token,
     so a releaser recovers exactly the fraction it deposited. *)
  Lemma sl_hauth_agree γ q q' :
    sl_hauth γ q -∗ sl_htok γ q' -∗ ⌜q = q'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    destruct Hv as [Hv1 _].
    iPureIntro. exact (excl_auth_agree_L _ _ Hv1).
  Qed.

  (* re-targeting: whoever holds BOTH halves may set the fraction, which is
     what an acquirer does with the junk fraction it finds in the free arm. *)
  Lemma sl_hauth_update γ q q' :
    sl_hauth γ q -∗ sl_htok γ q ==∗ sl_hauth γ q' ∗ sl_htok γ q'.
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _ ((●E (q' : leibnizO Qp) ⋅ ◯E (q' : leibnizO Qp), ε) : slhUR)
            with "Ha Hf") as "H".
    { rewrite -pair_op left_id.
      apply prod_update; simpl; [ apply excl_auth_update | done ]. }
    iModIntro. rewrite pair_op_1 own_op. iDestruct "H" as "[$ $]".
  Qed.

  (* ...and the two lifted to what a holder actually carries. *)
  Lemma sl_hauth_agree_q γ q q' slk pid :
    sl_hauth γ q -∗ sleeplocked_q γ q' slk pid -∗ ⌜q = q'⌝.
  Proof. iIntros "Ha [Ht _]". iApply (sl_hauth_agree with "Ha Ht"). Qed.

  (* ---- the counting half: shares, the zero, and the two ghost steps ---- *)

  Lemma slh_tok_split γ p q :
    slh_tok γ (p + q)%Qp ⊣⊢ slh_tok γ p ∗ slh_tok γ q.
  Proof.
    rewrite /slh_tok -own_op. f_equiv.
    rewrite -pair_op left_id -auth_frag_op -Some_op. done.
  Qed.

  Lemma slh_tok_join γ p q :
    slh_tok γ p -∗ slh_tok γ q -∗ slh_tok γ (p + q)%Qp.
  Proof. iIntros "H1 H2". iApply slh_tok_split. iFrame. Qed.

  (* THE AUTHORITATIVE ZERO REFUTES EVERY SHARE.  This is the whole point of
     the counting half: a client presenting [slh_auth γ None] has proved that
     nobody anywhere holds a deposit for this sleeplock. *)
  Lemma slh_auth_none_no_tok γ q :
    slh_auth γ None -∗ slh_tok γ q -∗ False.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    destruct Hv as [_ Hv2]. simpl in Hv2.
    apply auth_both_valid_discrete in Hv2 as [Hincl _].
    apply option_included in Hincl as [Hbad | (a & b & _ & Hbad & _)]; by inversion Hbad.
  Qed.

  (* and the general bound, for a client that keeps a running total *)
  Lemma slh_auth_tok_le γ t q :
    slh_auth γ t -∗ slh_tok γ q -∗ ⌜∃ t', t = Some t' /\ (q ≤ t')%Qp⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    destruct Hv as [_ Hv2]. simpl in Hv2.
    apply auth_both_valid_discrete in Hv2 as [Hincl _].
    apply option_included in Hincl as [Hbad | (a & b & Ha & Hb & Hle)];
      [ by inversion Hbad |].
    apply (inj Some) in Ha. subst a. subst t.
    iPureIntro. exists b. split; [ reflexivity |].
    destruct Hle as [Heq | [z Hz]].
    - rewrite Heq. reflexivity.
    - rewrite Hz. apply Qp.le_add_l.
  Qed.

  Lemma slh_mint_none γ q :
    slh_auth γ None ==∗ slh_auth γ (Some q) ∗ slh_tok γ q.
  Proof.
    iIntros "Ha".
    iMod (own_update _ _ ((ε, ● (Some q : optionUR ufracR) ⋅ ◯ (Some q : optionUR ufracR)) : slhUR)
            with "Ha") as "H".
    { apply prod_update; simpl; [ done |].
      apply (auth_update_alloc _ (Some q : optionUR ufracR) (Some q : optionUR ufracR)).
      apply (alloc_option_local_update (q : ufracR) None). done. }
    iModIntro. rewrite pair_op_2 own_op. iDestruct "H" as "[$ $]".
  Qed.

  Lemma slh_mint γ t q :
    slh_auth γ (Some t) ==∗ slh_auth γ (Some (t + q)%Qp) ∗ slh_tok γ q.
  Proof.
    iIntros "Ha".
    iMod (own_update _ _
            ((ε, ● (Some (t + q)%Qp : optionUR ufracR) ⋅ ◯ (Some q : optionUR ufracR)) : slhUR)
            with "Ha") as "H".
    { apply prod_update; simpl; [ done |].
      apply (auth_update_alloc _ (Some (t + q)%Qp : optionUR ufracR) (Some q : optionUR ufracR)).
      apply local_update_unital_discrete. intros z _ Heq.
      rewrite left_id in Heq. split; [ done |].
      rewrite -Heq -Some_op. by rewrite (comm Qp.add t q). }
    iModIntro. rewrite pair_op_2 own_op. iDestruct "H" as "[$ $]".
  Qed.

  (* the two returns: a share comes back, and the LAST one restores the
     authoritative zero -- which is what a client does before asking for the
     non-blocking acquiresleep. *)
  Lemma slh_return γ t q :
    slh_auth γ (Some (t + q)%Qp) -∗ slh_tok γ q ==∗ slh_auth γ (Some t).
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _ ((ε, ● (Some t : optionUR ufracR)) : slhUR)
            with "Ha Hf") as "H".
    { rewrite -pair_op left_id.
      apply prod_update; simpl; [ done |].
      apply (auth_update_dealloc _ _ (Some t : optionUR ufracR)).
      apply local_update_unital_discrete. intros z _ Heq.
      split; [ done |]. rewrite left_id.
      destruct z as [z|].
      - rewrite -Some_op in Heq. apply (inj Some) in Heq.
        assert (Ht : t = z).
        { apply (inj (fun x => (x + q)%Qp)). rewrite Heq. apply (comm Qp.add). }
        by rewrite Ht.
      - rewrite right_id in Heq. apply (inj Some) in Heq. exfalso.
        rewrite (comm Qp.add t q) in Heq. exact (Qp.add_id_free q t Heq). }
    iModIntro. done.
  Qed.

  Lemma slh_return_last γ q :
    slh_auth γ (Some q) -∗ slh_tok γ q ==∗ slh_auth γ None.
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _ ((ε, ● (None : optionUR ufracR)) : slhUR)
            with "Ha Hf") as "H".
    { rewrite -pair_op left_id.
      apply prod_update; simpl; [ done |].
      apply (auth_update_dealloc _ _ (None : optionUR ufracR)).
      apply local_update_unital_discrete. intros z _ Heq.
      split; [ done |]. rewrite left_id.
      destruct z as [z|]; [| done ].
      exfalso. rewrite -Some_op in Heq. apply (inj Some) in Heq.
      symmetry in Heq. exact (Qp.add_id_free q z Heq). }
    iModIntro. done.
  Qed.

  (* ===================================================================== *)
  (*  THE RESOURCE THE INNER SPINLOCK PROTECTS.                            *)
  (* ===================================================================== *)

  (* the free arm's ghost pair: the holder token and its authority, both idle.
     The fraction is junk while free -- an acquirer re-targets it to its own
     ([sl_free_retarget]). *)
  Definition sl_free_tok (γ : gname) : iProp Σ :=
    (∃ q : Qp, sl_htok γ q ∗ sl_hauth γ q)%I.

  (* THE FREE ARM'S HOLDER-SHAPED FORM: the idle token pair AND the pid field
     pinned at 0, which is what an acquirer walks away with (re-targeted, and
     then stored into).  [sl_free_tok] itself stays GHOST-ONLY on purpose --
     [IcacheBoot.v] allocates all fifty inode-sleeplock gnames before a single
     lock address exists, so nothing address-shaped may be in it. *)
  Definition sl_free_hold (γ : gname) (slk : mword 64) : iProp Σ :=
    (∃ q : Qp, sleeplocked_q γ q slk (mword_of_int 0 : mword 32) ∗
               sl_hauth γ q)%I.

  Lemma sl_free_hold_intro γ slk :
    sl_free_tok γ -∗ sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_free_hold γ slk.
  Proof.
    iIntros "[%q [Ht Ha]] Hpid". iExists q. iFrame "Ha Ht Hpid".
  Qed.

  (* the held arm's DEPOSIT: the acquirer's share of [H], with the authority
     that says which fraction it was. *)
  Definition sl_dep (γ : gname) (H : Qp -> iProp Σ) : iProp Σ :=
    (∃ q : Qp, sl_hauth γ q ∗ H q)%I.

  (* what an untracked sleeplock deposits: nothing. *)
  Definition sl_untracked : Qp -> iProp Σ := fun _ => emp%I.

  Definition sl_res_gen (γ : gname) (slk : mword 64) (R : iProp Σ)
      (H : Qp -> iProp Σ) : iProp Σ :=
    (∃ v : mword 32,
       slk ↦₄ v ∗
       (⌜v = (mword_of_int 0 : mword 32)⌝ ∗ sl_free_hold γ slk ∗ R
        ∨ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ ∗ sl_dep γ H))%I.

  Definition sl_res (γ : gname) (slk : mword 64) (R : iProp Σ) : iProp Σ :=
    sl_res_gen γ slk R sl_untracked.

  (* the whole sleeplock: its name plus the inner spinlock -- named
     "sleep lock", the literal initsleeplock passes to initlock -- over
     [sl_res_gen].  Persistent: every user shares it. *)
  Definition is_sleeplock_gen (γl γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) (H : Qp -> iProp Σ) : iProp Σ :=
    (sl_name slk s ∗
     is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R H }>)%I.

  Definition is_sleeplock (γl γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) : iProp Σ :=
    is_sleeplock_gen γl γ slk s R sl_untracked.

  (* the TRACKED sleeplock: the deposit is a share of the "may hold" right,
     so [slh_auth γ None] refutes the held arm.  This is the shape the
     non-blocking acquiresleep is stated over. *)
  Definition is_sleeplock_tok (γl γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) : iProp Σ :=
    is_sleeplock_gen γl γ slk s R (slh_tok γ).

  Global Instance is_sleeplock_gen_persistent γl γ slk s R H :
    Persistent (is_sleeplock_gen γl γ slk s R H).
  Proof. apply _. Qed.
  Global Instance is_sleeplock_persistent γl γ slk s R :
    Persistent (is_sleeplock γl γ slk s R).
  Proof. apply _. Qed.
  Global Instance is_sleeplock_tok_persistent γl γ slk s R :
    Persistent (is_sleeplock_tok γl γ slk s R).
  Proof. apply _. Qed.

  Lemma is_sleeplock_gen_name γl γ slk s R H :
    is_sleeplock_gen γl γ slk s R H -∗ sl_name slk s.
  Proof. iIntros "[$ _]". Qed.
  Lemma is_sleeplock_gen_lock γl γ slk s R H :
    is_sleeplock_gen γl γ slk s R H -∗
    is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R H }>.
  Proof. iIntros "[_ $]". Qed.
  Lemma is_sleeplock_gen_intro γl γ slk s R H :
    sl_name slk s -∗
    is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R H }> -∗
    is_sleeplock_gen γl γ slk s R H.
  Proof. iIntros "#Hn #Hl". by iFrame "Hn Hl". Qed.

  Lemma is_sleeplock_name γl γ slk s R :
    is_sleeplock γl γ slk s R -∗ sl_name slk s.
  Proof. apply is_sleeplock_gen_name. Qed.
  Lemma is_sleeplock_lock γl γ slk s R :
    is_sleeplock γl γ slk s R -∗
    is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res γ slk R }>.
  Proof. apply is_sleeplock_gen_lock. Qed.
  Lemma is_sleeplock_intro γl γ slk s R :
    sl_name slk s -∗
    is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res γ slk R }> -∗
    is_sleeplock γl γ slk s R.
  Proof. apply is_sleeplock_gen_intro. Qed.

  (* ---- opening/closing [sl_res_gen] inside the inner critical section -- *)

  (* as the HOLDER (token in hand): the free disjunct is refuted by token
     exclusivity, leaving the held shape (word cell + non-zeroness) and the
     deposit, which the holder must put back when it re-closes. *)
  Lemma sl_res_open_held γ slk R H pid :
    sl_res_gen γ slk R H -∗ sleeplocked γ slk pid -∗
    sleeplocked γ slk pid ∗ sl_dep γ H ∗
    (∃ v : mword 32,
       slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝).
  Proof.
    iIntros "Hres Htok".
    iDestruct "Hres" as (v) "[Hw [(_ & Hfree & _) | [%Hnz Hdep]]]".
    { iExFalso. iDestruct "Hfree" as (q) "[Htok' _]".
      iDestruct "Htok" as (q') "Htok".
      iApply (sleeplocked_q_exclusive with "Htok Htok'"). }
    iFrame "Htok Hdep". iExists v. by iFrame "Hw".
  Qed.

  (* the PRECISE form: the deposit's authority agrees with the holder's own
     fraction, so what comes out is exactly [H q] for the holder's [q].  This
     is what releasesleep needs -- see the header on why "some fraction" will
     not do. *)
  Lemma sl_res_open_held_q γ slk R H q pid :
    sl_res_gen γ slk R H -∗ sleeplocked_q γ q slk pid -∗
    sleeplocked_q γ q slk pid ∗ sl_hauth γ q ∗ H q ∗
    (∃ v : mword 32,
       slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝).
  Proof.
    iIntros "Hres Htok".
    iDestruct "Hres" as (v) "[Hw [(_ & Hfree & _) | [%Hnz Hdep]]]".
    { iExFalso. iDestruct "Hfree" as (q0) "[Htok' _]".
      iApply (sleeplocked_q_exclusive with "Htok Htok'"). }
    iDestruct "Hdep" as (q0) "[Hha HH]".
    iDestruct (sl_hauth_agree_q with "Hha Htok") as %<-.
    iFrame "Htok Hha HH". iExists v. by iFrame "Hw".
  Qed.

  (* re-close in the held state (acquiresleep after its [locked := 1] store;
     releasesleep/holdingsleep before touching the word). *)
  Lemma sl_res_close_held γ slk R H (v : mword 32) :
    neq_vec (sign_extend' 64 v) zero_reg = true ->
    slk ↦₄ v -∗ sl_dep γ H -∗ sl_res_gen γ slk R H.
  Proof. iIntros (Hnz) "Hw Hdep". iExists v. iFrame "Hw". iRight. by iFrame. Qed.

  Lemma sl_res_close_held_q γ slk R H (v : mword 32) (q : Qp) :
    neq_vec (sign_extend' 64 v) zero_reg = true ->
    slk ↦₄ v -∗ sl_hauth γ q -∗ H q -∗ sl_res_gen γ slk R H.
  Proof.
    iIntros (Hnz) "Hw Hha HH".
    iApply (sl_res_close_held with "Hw"); [ exact Hnz |]. iExists q. iFrame.
  Qed.

  (* close in the free state (releasesleep after its two zero stores). *)
  (* close in the free state (releasesleep after its two zero stores).  The
     pid field is no longer a separate argument: releasesleep's store into it
     lands through [sleeplocked_q_pid], so what arrives here is the holder
     token AT VALUE 0, which is exactly the free arm's shape. *)
  Lemma sl_res_close_free γ slk R H (q : Qp) :
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sleeplocked_q γ q slk (mword_of_int 0 : mword 32) -∗
    sl_hauth γ q -∗
    R -∗
    sl_res_gen γ slk R H.
  Proof.
    iIntros "Hw Htok Hha HR". iExists (mword_of_int 0 : mword 32).
    iFrame "Hw". iLeft. iFrame "HR". iSplitR; [ done |]. iExists q. iFrame.
  Qed.

  (* the acquirer's ghost step: the free arm's junk fraction becomes the
     acquirer's own, so that the deposit it is about to make is pinned to the
     token it walks away with. *)
  Lemma sl_free_retarget γ slk (q : Qp) :
    sl_free_hold γ slk ==∗
    sleeplocked_q γ q slk (mword_of_int 0 : mword 32) ∗ sl_hauth γ q.
  Proof.
    iIntros "Hfree". iDestruct "Hfree" as (q0) "[[Htok Hpid] Hha]".
    iMod (sl_hauth_update γ q0 q with "Hha Htok") as "[$ Ht]".
    iModIntro. iFrame "Ht Hpid".
  Qed.

  (* ---- construction (the "newsleeplock" ghost step): what a caller does
     with initsleeplock's postcondition -- the freshly zeroed fields, the
     two persistent names and the resource become a sleeplock.  The counting
     authority starts at the AUTHORITATIVE ZERO, which is what a tracked
     client keeps and hands out shares from. *)
  (* ---- ALLOCATING THE GHOST BEFORE THE LOCK.

     [new_sleeplock_gen] allocates the gname itself, which is right for a
     caller that builds one lock and names it afterwards.  A client whose
     OTHER resources have to mention the gname cannot use it: the icache's
     [iref_tok k q] carries [slh_tok (icfg_isl k) q], so [icfg_isl] has to
     exist -- and be fixed in the ambient config -- before any inode
     sleeplock is built (claude-notes/projects/iput-acquiresleep.md, step 4).

     So the ghost is separable: allocate it, put the names where they belong,
     and build each lock AT the gname it was given.  [sl_free_tok γ] is
     exactly what an unbuilt lock's free arm wants, which is why it is the
     thing handed over. *)
  Lemma slh_ghost_alloc : ⊢ |==> ∃ γ : gname, sl_free_tok γ ∗ slh_auth γ None.
  Proof.
    iMod (own_alloc (((●E (1%Qp : leibnizO Qp), ε) : slhUR)
                     ⋅ ((◯E (1%Qp : leibnizO Qp), ε) : slhUR)
                     ⋅ ((ε, ● (None : optionUR ufracR)) : slhUR))) as (γ) "Hg".
    { rewrite -!pair_op !left_id !right_id. apply pair_valid.
      split; [ by apply excl_auth_valid | by apply auth_auth_valid ]. }
    iDestruct "Hg" as "[[Hha Htok] Hauth]".
    iModIntro. iExists γ. iFrame "Hauth". iExists 1%Qp. iFrame.
  Qed.

  (* A6.67: the honest creator deposit (A6.66) takes the running token and
     hands it straight back. *)
  Lemma new_sleeplock_gen_at `{CID : RiscvLang.CpuId} E (γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) (H : Qp -> iProp Σ) :
    sl_free_tok γ -∗
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_name slk s -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    own_context cur_ctx -∗
    R ={E}=∗ own_context cur_ctx ∗ ∃ γl : gname, is_sleeplock_gen γl γ slk s R H.
  Proof.
    iIntros "Hfree #Hlnm #Hsnm Hlkw Hcpu Hw Hpid Hrun HR".
    iDestruct (sl_free_hold_intro with "Hfree Hpid") as (q0) "[Htok Hha]".
    iMod (newlock E (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R H }>
            with "Hlnm Hrun Hlkw Hcpu [Hw Htok Hha HR]") as "[Hrun Hlk]".
    { iApply (sl_res_close_free with "Hw Htok Hha HR"). }
    iDestruct "Hlk" as (γl) "#Hlk".
    iModIntro. iFrame "Hrun". iExists γl.
    iApply (is_sleeplock_gen_intro with "Hsnm Hlk").
  Qed.

  (* A6.67: the honest creator deposit (A6.66) takes the running token and
     hands it straight back. *)
  Lemma new_sleeplock_gen `{CID : RiscvLang.CpuId} E (slk : mword 64) (s : string) (R : iProp Σ)
      (H : gname -> Qp -> iProp Σ) :
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_name slk s -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    own_context cur_ctx -∗
    R ={E}=∗ own_context cur_ctx ∗ ∃ γl γ : gname, is_sleeplock_gen γl γ slk s R (H γ) ∗ slh_auth γ None.
  Proof.
    iIntros "#Hlnm #Hsnm Hlkw Hcpu Hw Hpid Hrun HR".
    iMod (own_alloc (((●E (1%Qp : leibnizO Qp), ε) : slhUR)
                     ⋅ ((◯E (1%Qp : leibnizO Qp), ε) : slhUR)
                     ⋅ ((ε, ● (None : optionUR ufracR)) : slhUR))) as (γ) "Hg".
    { rewrite -!pair_op !left_id !right_id. apply pair_valid.
      split; [ by apply excl_auth_valid | by apply auth_auth_valid ]. }
    iDestruct "Hg" as "[[Hha Htok] Hauth]".
    iMod (newlock E (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R (H γ) }>
            with "Hlnm Hrun Hlkw Hcpu [Hw Htok Hha Hpid HR]") as "[Hrun Hlk]".
    { iApply (sl_res_close_free with "Hw [Htok Hpid] Hha HR").
      iFrame "Htok Hpid". }
    iDestruct "Hlk" as (γl) "#Hlk".
    iModIntro. iFrame "Hrun". iExists γl, γ. iFrame "Hauth".
    iApply (is_sleeplock_gen_intro with "Hsnm Hlk").
  Qed.

  (* A6.67: the honest creator deposit (A6.66) takes the running token and
     hands it straight back. *)
  Lemma new_sleeplock `{CID : RiscvLang.CpuId} E (slk : mword 64) (s : string) (R : iProp Σ) :
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_name slk s -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    own_context cur_ctx -∗
    R ={E}=∗ own_context cur_ctx ∗ ∃ γl γ : gname, is_sleeplock γl γ slk s R.
  Proof.
    iIntros "#Hlnm #Hsnm Hlkw Hcpu Hw Hpid Hrun HR".
    iMod (new_sleeplock_gen E slk s R (fun _ => sl_untracked)
            with "Hlnm Hsnm Hlkw Hcpu Hw Hpid Hrun HR") as "[Hrun Hgen]".
    iDestruct "Hgen" as (γl γ) "[#Hsl _]".
    iModIntro. iFrame "Hrun". iExists γl, γ. iExact "Hsl".
  Qed.

  (* ---- the two ends of initsleeplock, bundled.

     A caller that initializes ONE sleeplock names the six struct fields and
     the six results individually (as [SpecInitsleeplock.v] does).  A caller
     that initializes an ARRAY of them -- binit over bcache.buf[], iinit over
     itable.inode[] -- must not: its pre/postcondition would be a big-sep of
     six-field tuples with six existentially quantified contents each.  So the
     two ends get names: [sl_raw slk] is an uninitialized sleeplock (all six
     cells, contents arbitrary) and [sl_fresh slk s] is initsleeplock's result
     (the four zeroed cells plus the two persistent names).  [sl_fresh] is
     exactly [new_sleeplock]'s premises minus the resource, so a caller turns
     an array of them into an array of sleeplocks one [sl_fresh_new] at a
     time. *)
  Definition sl_raw (slk : mword 64) : iProp Σ :=
    (∃ (vlocked vlk vpid : mword 32) (vlkname vcpu vname : mword 64),
       slk ↦₄ vlocked ∗
       sl_lk slk ↦₄ vlk ∗
       lock_name_field (sl_lk slk) ↦₈ vlkname ∗
       sl_lkcpu slk ↦₈ vcpu ∗
       sl_name_field slk ↦₈ vname ∗
       sl_pid slk ↦₄ vpid)%I.

  Definition sl_fresh (slk : mword 64) (s : string) : iProp Σ :=
    (slk ↦₄ (mword_of_int 0 : mword 32) ∗
     sl_lk slk ↦₄ (mword_of_int 0 : mword 32) ∗
     lock_name (sl_lk slk) "sleep lock"%string ∗
     sl_lkcpu slk ↦₈ (zero_reg : mword 64) ∗
     sl_name slk s ∗
     sl_pid slk ↦₄ (mword_of_int 0 : mword 32))%I.

  (* the ghost step from initsleeplock's output to a usable sleeplock: the cpu
     word of the inner spinlock goes INTO [lock_inv] (WpLock.v owns both lock
     words). *)
  Lemma sl_fresh_new_gen `{CID : RiscvLang.CpuId} E (slk : mword 64) (s : string)
      (R : iProp Σ) (H : gname -> Qp -> iProp Σ) :
    sl_fresh slk s -∗ own_context cur_ctx -∗ R ={E}=∗ own_context cur_ctx ∗
    ∃ γl γ : gname, is_sleeplock_gen γl γ slk s R (H γ) ∗ slh_auth γ None.
  Proof.
    iIntros "(Hw & Hlkw & #Hlnm & Hcpu & #Hsnm & Hpid) Hrun HR".
    iApply (new_sleeplock_gen E slk s R H with "Hlnm Hsnm Hlkw Hcpu Hw Hpid Hrun HR").
  Qed.

  Lemma sl_fresh_new `{CID : RiscvLang.CpuId} E (slk : mword 64) (s : string)
      (R : iProp Σ) :
    sl_fresh slk s -∗ own_context cur_ctx -∗ R ={E}=∗ own_context cur_ctx ∗
    ∃ γl γ : gname, is_sleeplock γl γ slk s R.
  Proof.
    iIntros "(Hw & Hlkw & #Hlnm & Hcpu & #Hsnm & Hpid) Hrun HR".
    iApply (new_sleeplock E slk s R with "Hlnm Hsnm Hlkw Hcpu Hw Hpid Hrun HR").
  Qed.

  (* [sl_fresh_new_gen] at a PRE-ALLOCATED gname -- what an array
     initializer (iinit over itable.inode[]) uses when the gnames had to be
     fixed before the locks were built.  See [new_sleeplock_gen_at]. *)
  Lemma sl_fresh_new_gen_at `{CID : RiscvLang.CpuId} E (γ : gname)
      (slk : mword 64) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) :
    sl_free_tok γ -∗ sl_fresh slk s -∗ own_context cur_ctx -∗ R ={E}=∗
    own_context cur_ctx ∗ ∃ γl : gname, is_sleeplock_gen γl γ slk s R H.
  Proof.
    iIntros "Hfree (Hw & Hlkw & #Hlnm & Hcpu & #Hsnm & Hpid) Hrun HR".
    iApply (new_sleeplock_gen_at E γ slk s R H
              with "Hfree Hlnm Hsnm Hlkw Hcpu Hw Hpid Hrun HR").
  Qed.

  (* the TRACKED end: the caller keeps the authoritative zero and hands out
     shares from it.  [slh_auth γ None] in hand is exactly the evidence the
     non-blocking acquiresleep asks for. *)
  Lemma sl_fresh_new_tok `{CID : RiscvLang.CpuId} E (slk : mword 64)
      (s : string) (R : iProp Σ) :
    sl_fresh slk s -∗ own_context cur_ctx -∗ R ={E}=∗ own_context cur_ctx ∗
    ∃ γl γ : gname, is_sleeplock_tok γl γ slk s R ∗ slh_auth γ None.
  Proof.
    iIntros "Hf Hrun HR".
    iApply (sl_fresh_new_gen E slk s R slh_tok with "Hf Hrun HR").
  Qed.

End SleepLock.
