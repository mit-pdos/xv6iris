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
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Local Open Scope Z_scope.

Section LockAt.
  Context `{!riscvGS Σ, !lockG Σ}.
  (* the creator deposits the payload at its own context; see WpLock.v *)
  Context `{XI : CurCtx}.

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
  (* A6.67: the free arm is the parked record, so this creator DEPOSITS.
     [own_context] in and straight back out -- the honest mint's price
     (A6.66), paid once here for all seven [newlock_at] callers. *)
  Lemma newlock_at `{CID : RiscvLang.CpuId} E (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) `{!CtxMorph R} :
    lock_free_tok γ -∗
    lock_name lk s -∗
    own_context cur_ctx -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_fresh lk -∗
    R cur_ctx ={E}=∗ own_context cur_ctx ∗ is_lock γ lk s R.
  Proof.
    iIntros "[Ha Hf] #Hnm Hrun Hword Hcpu HR".
    iMod (lock_pay_intro R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iDestruct (WpLock.lk_addr_claim_of4 lk (DfracOwn 1) (mword_of_int 0 : mword 32)
                 with "Hword") as "#Hc4".
    iDestruct "Hcpu" as "[#Hc8 Hcell]".
    iMod (inv_alloc lockN E (lock_inv γ lk s R)
            with "[Hword Hcell Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv. iFrame "Hc4 Hc8".
      iExists (mword_of_int 0 : mword 32), None.
      iDestruct (lock_word_intro with "Hword") as "Hword".
      rewrite lk_cpu_res_free. iFrame "Hword Ha".
      iSplitL "Hcell"; [ iExact "Hcell" | ].
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End LockAt.
