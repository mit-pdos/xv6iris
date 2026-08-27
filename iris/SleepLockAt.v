(* SleepLockAt.v -- a sleeplock at BOTH of its pre-allocated gnames.

   [SleepLock.sl_fresh_new_gen_at] fixes the sleeplock's HOLDER gname (the
   [sl_free_tok] it is handed) but still mints the INNER SPINLOCK's gname
   itself, because it goes through [WpLock.newlock]: it returns
   [∃ γl, is_sleeplock_gen γl γ …].  A client whose ambient configuration
   records the whole PAIR -- [BioDefs.bio_names]'s [bn_slk : nat -> gname *
   gname] is exactly that -- cannot use it: [bio_ctx bn V] names
   [(bn_slk bn k).1], so that gname has to exist before the lock is built
   (claude-notes/projects/fs-cfg-boot.md, "THE PRINCIPLE").

   With [WpLockAt.newlock_at] the remaining [own_alloc] comes out too, and the
   pair of free-state tokens is one row: [sl_free_pair]. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto.
Require Export WpLockAt.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Export SleepLock.
Local Open Scope Z_scope.

Section SleepLockAt.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* an UNBUILT sleeplock's two free arms: the inner spinlock's state pair and
     the sleeplock's own idle holder pair.  Ghost-only, like both halves it is
     made of, so a boot fupd can mint an array of these before any lock
     address exists. *)
  Definition sl_free_pair (p : gname * gname) : iProp Σ :=
    (lock_free_tok p.1 ∗ sl_free_tok p.2)%I.

  Lemma sl_pair_ghost_alloc : ⊢ |==> ∃ p : gname * gname, sl_free_pair p.
  Proof.
    iMod lock_ghost_alloc as (γl) "Hl".
    iMod slh_ghost_alloc as (γ) "[Hf _]".
    iModIntro. iExists (γl, γ). rewrite /sl_free_pair /=. iFrame "Hl Hf".
  Qed.

  (* [SleepLock.new_sleeplock_gen_at] with the inner spinlock's gname given
     as well: nothing is minted here, so the conclusion is not existential. *)
  Lemma new_sleeplock_gen_at2 `{XI : CurCtx} E (p : gname * gname) (slk : mword 64)
      (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) :
    sl_free_pair p -∗
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_name slk s -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    R ={E}=∗ is_sleeplock_gen p.1 p.2 slk s R H.
  Proof.
    iIntros "[Hlfree Hfree] #Hlnm #Hsnm Hlkw Hcpu Hw Hpid HR".
    iDestruct (sl_free_hold_intro with "Hfree Hpid") as (q0) "[Htok Hha]".
    iMod (newlock_at E p.1 (sl_lk slk) "sleep lock"%string (λ ξ : CtxId, sl_res_gen (XI := ξ) p.2 slk R H)
            with "Hlfree Hlnm Hlkw Hcpu [Hw Htok Hha HR]") as "#Hlk".
    { iApply (sl_res_close_free with "Hw Htok Hha HR"). }
    iModIntro. iApply (is_sleeplock_gen_intro with "Hsnm Hlk").
  Qed.

  (* the two forms an array initializer uses: initsleeplock's packaged output
     ([sl_fresh]) against a pre-minted pair. *)
  Lemma sl_fresh_new_gen_at2 `{XI : CurCtx} E (p : gname * gname) (slk : mword 64)
      (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) :
    sl_free_pair p -∗ sl_fresh slk s -∗ R ={E}=∗
    is_sleeplock_gen p.1 p.2 slk s R H.
  Proof.
    iIntros "Hp (Hw & Hlkw & #Hlnm & Hcpu & #Hsnm & Hpid) HR".
    iApply (new_sleeplock_gen_at2 E p slk s R H
              with "Hp Hlnm Hsnm Hlkw Hcpu Hw Hpid HR").
  Qed.

  Lemma sl_fresh_new_at2 `{XI : CurCtx} E (p : gname * gname) (slk : mword 64)
      (s : string) (R : iProp Σ) :
    sl_free_pair p -∗ sl_fresh slk s -∗ R ={E}=∗ is_sleeplock p.1 p.2 slk s R.
  Proof.
    iIntros "Hp Hf HR".
    iApply (sl_fresh_new_gen_at2 E p slk s R sl_untracked with "Hp Hf HR").
  Qed.

End SleepLockAt.
