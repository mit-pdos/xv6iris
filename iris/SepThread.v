(* SepThread.v -- ONE lemma: thread a LINEAR resource through a [big_sepL]
   of update steps.

   WHY IT EXISTS (A6.68).  The honest creator deposit (A6.66/A6.67) makes
   every [WpLock] creator take [TsoCtx.own_context cur_ctx] and hand it
   straight back.  That is free at a single call site, but a BOOT
   initializer builds an ARRAY of locks -- [BioInv.bio_init]'s NBUF buffer
   sleeplocks, [IcacheBoot]'s NINODE inode sleeplocks -- and the existing
   idiom there is [big_sepL_mono] into a list of independent fupds, which
   cannot be given the token: [own_context] is EXCLUSIVE
   ([TsoCtx.own_context_excl]), so the fifty steps must run in SEQUENCE,
   each handing the token to the next.

   That is all this file says, and it says it with no tree dependencies at
   all: for any [BiFUpd PROP], a per-element step that BORROWS [Res] and
   returns it folds over the list, borrowing [Res] once.  Stated generically
   in [Res] rather than at [own_context] on purpose -- the same shape is what
   any exclusive boot authority (a supply, an allocator's count) would want,
   and a generic statement cannot drift from the kit. *)
From Stdlib Require Import List.
From stdpp Require Import coPset.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Section SepThread.
  Context {PROP : bi} `{!BiFUpd PROP}.

  (* BORROW-AND-RETURN over a list.  [Phi] in, [Psi] out, [Res] threaded: the
     conclusion returns [Res] exactly as the caller lent it, so no
     postcondition downstream of the loop changes shape. *)
  Lemma big_sepL_fupd_thread {A : Type} (E : coPset) (Res : PROP)
      (Phi Psi : nat -> A -> PROP) (l : list A) :
    Res -∗
    ([∗ list] k↦x ∈ l, Res -∗ Phi k x ={E}=∗ Res ∗ Psi k x) -∗
    ([∗ list] k↦x ∈ l, Phi k x) ={E}=∗
    Res ∗ [∗ list] k↦x ∈ l, Psi k x.
  Proof.
    revert Phi Psi.
    induction l as [|x l IH]; iIntros (Phi Psi) "HRes Hstep HPhi".
    { iModIntro. iFrame "HRes". done. }
    rewrite !big_sepL_cons.
    iDestruct "Hstep" as "[Hh Ht]". iDestruct "HPhi" as "[Hx Hl]".
    iMod ("Hh" with "HRes Hx") as "[HRes Hy]".
    iMod (IH (fun k y => Phi (S k) y) (fun k y => Psi (S k) y)
            with "HRes Ht Hl") as "[HRes Hrest]".
    iModIntro. iFrame "HRes Hy Hrest".
  Qed.

End SepThread.
