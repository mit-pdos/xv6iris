(* WpLockAt.v -- [newlock] AT A PRE-ALLOCATED gname.

   [WpLock.newlock] and [WpLock.newlock_delayed] both mint the lock-state
   gname themselves and return it existentially.  A client whose OTHER
   resources have to MENTION that gname cannot use either form: the gname has
   to be fixed before the resource can be stated, and an ambient
   configuration field cannot be an existential
   (claude-notes/projects/fs-cfg-boot.md, "THE PRINCIPLE").

   So the ghost step is separable, exactly as [SleepLock.slh_ghost_alloc] /
   [SleepLock.new_sleeplock_gen_at] separate the sleeplock's:

     lock_ghost_alloc  -- pick the gname (a plain [bupd]: no mask, no
                          physical premise, so it runs in a boot fupd before
                          any lock address exists)
     lock_free_tok γ   -- what an UNBUILT lock's free arm wants: the state
                          authority and its fragment, both at [None]
     newlock_at        -- [newlock] minus that one [own_alloc]

   A leaf file: nothing existing changes, and [newlock_delayed] stays for the
   callers that do want a fresh name. *)
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Export WpLock.
Local Open Scope Z_scope.

Section LockAt.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* the free arm's ghost pair.  GHOST-ONLY on purpose (SleepLock's
     [sl_free_tok] makes the same choice and says why): a client that mints
     these at boot has no lock address yet. *)
  Definition lock_free_tok (γ : gname) : iProp Σ :=
    (lock_auth γ None ∗ lock_frag γ None)%I.

  Global Instance lock_free_tok_timeless γ : Timeless (lock_free_tok γ).
  Proof. apply _. Qed.

  Lemma lock_free_tok_exclusive γ : lock_free_tok γ -∗ lock_free_tok γ -∗ False.
  Proof.
    iIntros "[_ H1] [_ H2]". iApply (lock_frag_exclusive with "H1 H2").
  Qed.

  Lemma lock_ghost_alloc : ⊢ |==> ∃ γ : gname, lock_free_tok γ.
  Proof.
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ.
    rewrite /lock_free_tok /lock_auth /lock_frag. iFrame "Ha Hf".
  Qed.

  (* [WpLock.newlock] with its [own_alloc] taken out: a free physical lock
     (word 0, cpu word 0), its name, its resource and the pre-minted ghost
     pair become THE lock at the gname the caller already published. *)
  Lemma newlock_at E (γ : gname) (lk : mword 64) (s : string) (R : iProp Σ) :
    lock_free_tok γ -∗
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R ={E}=∗ is_lock γ lk s R.
  Proof.
    iIntros "[Ha Hf] #Hnm Hword Hcpu HR".
    iMod (inv_alloc lockN E (lock_inv γ lk s R)
            with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32), None.
      rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End LockAt.
