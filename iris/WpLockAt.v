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
Require Import RiscvPtsto.
Require Export WpLock.
Require Import TsoCtx.
Local Open Scope Z_scope.

Section LockAt.
  Context `{!riscvGS Σ, !lockG Σ}.
  (* §0.35': the handle is context-relative; the T-leg binds the index in
     this section too. *)
  Context `{XI : TsoCtx.CurCtx}.

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
    iMod (own_alloc (((●E (None : leibnizO lock_state), ●E (0%nat : leibnizO nat))
                      ⋅ (◯E (None : leibnizO lock_state), ◯E (0%nat : leibnizO nat)))
                     : lockUR)) as (γ) "H"; [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ.
    rewrite /lock_free_tok /lock_auth /lock_frag.
    iSplitL "Ha"; by iExists 0%nat.
  Qed.

  (* [WpLock.newlock] with its [own_alloc] taken out: a free physical lock
     (word 0, cpu word 0), its name, its resource and the pre-minted ghost
     pair become THE lock at the gname the caller already published. *)
  (* [tso-flip WpLockAt.v]: the seventh creator, and it pays the same cascade
     as the newlock family -- the running token in, deposited, straight back
     out.  A6.105: the floor travels bundled with the cell, so it is unbundled
     here and handed to [is_lock_intro], which is where the handle's floor
     lives. *)
  (* the seventh creator.  PROPAGATED SHAPE: the [lk_cpu_ready] owner cell
     and the lambda payload are the T-leg's, because they travel to every
     caller.  INTERNAL: the mint is the M-leg's SC form -- no running token,
     the transport quarantined in [lock_pay_intro]'s one shim use.  A6.105:
     the floor travels bundled with the cell, so it is unbundled here and
     handed to [is_lock_intro], which is where the handle's floor lives. *)
  Lemma newlock_at E (γ : gname) (lk : mword 64)
      (s : string) (R : TsoCtx.CtxId -> iProp Σ) `{!TsoCtx.CtxMorph R} :
    lock_free_tok γ -∗
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_ready lk -∗
    R TsoCtx.cur_ctx ={E}=∗ is_lock γ lk s R.
  Proof.
    iIntros "[Ha Hf] #Hnm Hword Hready HR".
    rewrite /WpLock.lk_cpu_ready /WpLock.lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (lock_pay_intro_sc R with "HR") as "HR".
    iDestruct "Ha" as (B) "Ha".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo)
            with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iApply bi.later_intro. iExists (mword_of_int 0 : mword 32), None, B.
      rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

End LockAt.
