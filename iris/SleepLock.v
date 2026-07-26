(* SleepLock.v -- the separation-logic sleeplock (kernel/sleeplock.c),
   mirroring the spinlock layer in WpLock.v one level up:

     sleeplocked γ   -- the (exclusive, ghost) sleeplock-ownership token
     sl_res          -- the resource protected by the INNER spinlock:
                        ∃ v, locked word ↦₄ v ∗
                             (v = 0 ∗ sleeplocked γ ∗ pid ↦₄ 0 ∗ R  ∨  v ≠ 0)
     is_sleeplock    -- the sleeplock's name + the inner spinlock (is_lock,
                        named "sleep lock") protecting sl_res  (persistent)

   When the sleeplock word is 0 (free) the inner critical section holds the
   token, the pid field (pinned 0: both initsleeplock and releasesleep write
   it back to 0) and the protected resource R; acquiresleep takes all three
   out and re-closes with the "held" disjunct, so the HOLDER of a sleeplock
   carries [sleeplocked γ ∗ sl_pid slk ↦₄ pid ∗ R] -- the pid field rides
   with the holder exactly like the spinlock's cpu word rides with the
   caller.  The held disjunct records the word's non-zeroness in the shape
   the c.beqz/c.bnez tests consume.

   struct sleeplock layout (sleeplock.h, offsets from the disassembly):
   locked@0 (4B), lk@8 (24B inner spinlock: word@8 name@16 cpu@24),
   name@32 (8B), pid@40 (4B). *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto.
Require Import WpLock.
Local Open Scope Z_scope.

Section SleepLock.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* ---- geometry, in the EXACT instruction address forms so the cells
     unify with the leaf and call specs without rewriting:
     [sl_lk] is the [addi s2,a0,8] form (the &lk->lk argument every inner
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
  Definition sl_name (slk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64, sl_name_field slk ↦₈□ p ∗ p ↦ₛ□ s)%I.

  Global Instance sl_name_persistent slk s : Persistent (sl_name slk s).
  Proof. apply _. Qed.

  (* the holder's exclusive token (same ghost as the spinlock's [locked],
     under its own gname). *)
  Definition sleeplocked (γ : gname) : iProp Σ := locked γ.

  Lemma sleeplocked_exclusive γ : sleeplocked γ -∗ sleeplocked γ -∗ False.
  Proof. apply locked_exclusive. Qed.

  Global Instance sleeplocked_timeless γ : Timeless (sleeplocked γ).
  Proof. apply _. Qed.

  (* the resource protected by the inner spinlock. *)
  Definition sl_res (γ : gname) (slk : mword 64) (R : iProp Σ) : iProp Σ :=
    (∃ v : mword 32,
       slk ↦₄ v ∗
       (⌜v = (mword_of_int 0 : mword 32)⌝ ∗ sleeplocked γ ∗
          sl_pid slk ↦₄ (mword_of_int 0 : mword 32) ∗ R
        ∨ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I.

  (* the whole sleeplock: its name plus the inner spinlock -- named
     "sleep lock", the literal initsleeplock passes to initlock -- over
     [sl_res].  Persistent: every user shares it. *)
  Definition is_sleeplock (γl γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) : iProp Σ :=
    (sl_name slk s ∗
     is_lock γl (sl_lk slk) "sleep lock"%string (sl_res γ slk R))%I.

  Global Instance is_sleeplock_persistent γl γ slk s R :
    Persistent (is_sleeplock γl γ slk s R).
  Proof. apply _. Qed.

  Lemma is_sleeplock_name γl γ slk s R :
    is_sleeplock γl γ slk s R -∗ sl_name slk s.
  Proof. iIntros "[$ _]". Qed.
  Lemma is_sleeplock_lock γl γ slk s R :
    is_sleeplock γl γ slk s R -∗
    is_lock γl (sl_lk slk) "sleep lock"%string (sl_res γ slk R).
  Proof. iIntros "[_ $]". Qed.
  Lemma is_sleeplock_intro γl γ slk s R :
    sl_name slk s -∗
    is_lock γl (sl_lk slk) "sleep lock"%string (sl_res γ slk R) -∗
    is_sleeplock γl γ slk s R.
  Proof. iIntros "#Hn #Hl". by iFrame "Hn Hl". Qed.

  (* ---- opening/closing [sl_res] inside the inner critical section ---- *)

  (* as the HOLDER (token in hand): the free disjunct is refuted by token
     exclusivity, leaving the held shape (word cell + non-zeroness). *)
  Lemma sl_res_open_held γ slk R :
    sl_res γ slk R -∗ sleeplocked γ -∗
    sleeplocked γ ∗
    (∃ v : mword 32,
       slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝).
  Proof.
    iIntros "Hres Htok". iDestruct "Hres" as (v) "[Hw [(_ & Htok' & _)|%Hnz]]".
    { iExFalso. iApply (sleeplocked_exclusive with "Htok Htok'"). }
    iFrame "Htok". iExists v. by iFrame "Hw".
  Qed.

  (* re-close in the held state (acquiresleep after its [locked := 1] store;
     releasesleep/holdingsleep before touching the word). *)
  Lemma sl_res_close_held γ slk R (v : mword 32) :
    neq_vec (sign_extend' 64 v) zero_reg = true ->
    slk ↦₄ v -∗ sl_res γ slk R.
  Proof. iIntros (Hnz) "Hw". iExists v. iFrame "Hw". by iRight. Qed.

  (* close in the free state (releasesleep after its two zero stores). *)
  Lemma sl_res_close_free γ slk R :
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sleeplocked γ -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    R -∗
    sl_res γ slk R.
  Proof.
    iIntros "Hw Htok Hpid HR". iExists (mword_of_int 0 : mword 32).
    iFrame "Hw". iLeft. iFrame "Htok Hpid HR". done.
  Qed.

  (* ---- construction (the "newsleeplock" ghost step): what a caller does
     with initsleeplock's postcondition -- the freshly zeroed fields, the
     two persistent names and the resource become a sleeplock. *)
  Lemma new_sleeplock E (slk : mword 64) (s : string) (R : iProp Σ) :
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_name slk s -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    R ={E}=∗
    ∃ γl γ : gname, is_sleeplock γl γ slk s R.
  Proof.
    iIntros "#Hlnm #Hsnm Hlkw Hw Hpid HR".
    iMod (own_alloc (Excl () : exclR unitO)) as (γ) "Htok"; [done|].
    iMod (own_alloc (Excl () : exclR unitO)) as (γl) "Htokl"; [done|].
    iMod (inv_alloc lockN E (lock_inv γl (sl_lk slk) (sl_res γ slk R))
            with "[Hlkw Htokl Hw Htok Hpid HR]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32). rewrite /lock_word.
      iFrame "Hlkw". iLeft. iSplit; [done|]. iFrame "Htokl".
      iApply (sl_res_close_free with "Hw Htok Hpid HR"). }
    iModIntro. iExists γl, γ.
    iApply (is_sleeplock_intro with "Hsnm").
    iApply (is_lock_intro with "Hlnm Hinv").
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
     word of the inner spinlock is NOT part of [lock_inv], so it comes back out
     for the caller to thread on (acquire/release want it). *)
  Lemma sl_fresh_new E (slk : mword 64) (s : string) (R : iProp Σ) :
    sl_fresh slk s -∗ R ={E}=∗
    (∃ γl γ : gname, is_sleeplock γl γ slk s R) ∗ sl_lkcpu slk ↦₈ (zero_reg : mword 64).
  Proof.
    iIntros "(Hw & Hlkw & #Hlnm & Hcpu & #Hsnm & Hpid) HR".
    iMod (new_sleeplock E slk s R with "Hlnm Hsnm Hlkw Hw Hpid HR") as "Hsl".
    iModIntro. iFrame "Hsl Hcpu".
  Qed.

End SleepLock.
