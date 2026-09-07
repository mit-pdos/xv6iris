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
    iMod (own_alloc ((((●E (None : leibnizO lock_state)),
                       (●E (0%nat : leibnizO nat)))
                      ⋅ ((◯E (None : leibnizO lock_state)),
                         (◯E (0%nat : leibnizO nat)))) : lockUR)) as (γ) "H";
      [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ.
    rewrite /lock_free_tok /lock_auth /lock_frag. iFrame "Ha Hf".
  Qed.

  (* [WpLock.newlock] with its [own_alloc] taken out: a free physical lock
     (word 0, cpu word 0), its name, its resource and the pre-minted ghost
     pair become THE lock at the gname the caller already published. *)
  (* the free arm is the lock's stamped context, so this creator mints it
     ([lock_pay_born]); [own_context] in and straight back out. *)
  (* TWO LOGS (relaxed-ww.md §2.4, "Birth"; §2.14): the record's
     publication is fence-bound, so the construction runs at a fence on the
     creator's hart and sees of it the creator's FLUSHED token (RULING C,
     the owner's, decides how the born record travels there). *)
  Lemma newlock_at `{CID : RiscvLang.CpuId} E (Df : nat) (γ : gname)
      (lk : mword 64) (s : string) (R : CtxId → iProp Σ) `{!CtxMorph R} :
    lock_free_tok γ -∗
    lock_name lk s -∗
    own_context_flushed cur_ctx Df -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_ready lk -∗
    R cur_ctx ={E}=∗ own_context_flushed cur_ctx Df ∗ is_lock γ lk s R.
  Proof.
    iIntros "[Ha Hf] #Hnm Hrun Hword Hready HR".
    (* A6.105: the floor travels bundled with the cell; unbundle it here and
       hand it to [is_lock_intro], which is where the handle's floor lives. *)
    rewrite /WpLock.lk_cpu_ready /WpLock.lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (lock_pay_born_id E Df R with "Hrun HR") as "(Hrun & HR)".
    iFrame "Hrun".
    iDestruct (WpLock.lk_addr_claim_of4 lk (DfracOwn 1) (mword_of_int 0 : mword 32)
                 with "Hword") as "#Hc4".
    iDestruct "Hcpu" as "[#Hc8 Hcell]".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo)
            with "[Hword Hcell Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv. iFrame "Hc4 Hc8".
      (* A6.119: the pre-allocated token's position is whatever it was
         allocated at; a FREE lock's word arm does not mention it. *)
      iDestruct "Ha" as (B0) "Ha".
      iExists (mword_of_int 0 : mword 32), None, B0.
      iDestruct (lock_word_intro with "Hword") as "Hword".
      rewrite lk_cpu_res_free. iFrame "Hword Ha".
      iSplitL "Hcell"; [ iExact "Hcell" | ].
      iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ iExact "Hf" | iExact "HR" ]. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

  (* BOX v2 boot: [newlock_at] minted WITH the fold ([lock_hook_llb]). *)
  Lemma newlock_at_llb `{CID : RiscvLang.CpuId} E (Df : nat) (γ : gname)
      (lk : mword 64) (s : string)
      (R Rdep : CtxId → iProp Σ) `{!CtxMorph Rdep} (tl : nat) :
    (forall ξ : CtxId, Rdep ξ ∗ TsoCtx.ctx_floor ξ tl ⊢ R ξ) ->
    lock_free_tok γ -∗
    lock_name lk s -∗
    own_context_flushed cur_ctx Df -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_ready lk -∗
    TsoGhost.llb dlen_name tl -∗
    Rdep cur_ctx ={E}=∗ own_context_flushed cur_ctx Df ∗ is_lock γ lk s R.
  Proof.
    iIntros (Hfold) "[Ha Hf] #Hnm Hrun Hword Hready #Hllb HR".
    (* A6.105: the floor travels bundled with the cell; unbundle it here and
       hand it to [is_lock_intro], which is where the handle's floor lives. *)
    rewrite /WpLock.lk_cpu_ready /WpLock.lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (lock_pay_born E Df Rdep R emp with "Hrun HR [Hllb]") as "(Hrun & HR & _)".
    { iApply (lock_hook_llb E Rdep R tl Hfold with "Hllb"). }
    iFrame "Hrun".
    iDestruct (WpLock.lk_addr_claim_of4 lk (DfracOwn 1) (mword_of_int 0 : mword 32)
                 with "Hword") as "#Hc4".
    iDestruct "Hcpu" as "[#Hc8 Hcell]".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo)
            with "[Hword Hcell Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv. iFrame "Hc4 Hc8".
      (* A6.119: the pre-allocated token's position is whatever it was
         allocated at; a FREE lock's word arm does not mention it. *)
      iDestruct "Ha" as (B0) "Ha".
      iExists (mword_of_int 0 : mword 32), None, B0.
      iDestruct (lock_word_intro with "Hword") as "Hword".
      rewrite lk_cpu_res_free. iFrame "Hword Ha".
      iSplitL "Hcell"; [ iExact "Hcell" | ].
      iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ iExact "Hf" | iExact "HR" ]. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

End LockAt.
