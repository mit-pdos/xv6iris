(* CtxRecord.v -- THE PARKED-RECORD IDIOM, as a two-line definition.

   An [inv] over a ξ-INDEXED body is the one shape [TsoCtx.CtxMorph] cannot
   cross: an invariant body is not updatable, so no transport exists and
   none can be written (tso-port.md §0.12′).  The M1 flip left exactly two
   such invariants that must serve MORE THAN ONE context --
   [BioInv.buf_escrow] (the buffer cache's escrow, opened by every hart that
   breads or brelses) and [StartedInv.started_inv (main_deposit ...)] (the
   boot hart's deposit, read by all eight harts at eight distinct
   [own_context_boot] identities) -- and ONE ruling covers both
   (tso-absorb-memo.md).

   THE RULING.  Put the ξ-indexed facts at a context of the RECORD's own and
   park that context's token beside them; a reader claims the facts at ITS
   context with [TsoCtx.ctx_absorb], against the hart-local pair
   [hart_view_lb K ∗ ⌜T ≤ K⌝] that [ctx_resume] already consumes, and hands
   the token straight back AT THE SAME STAMP -- which is what makes the claim
   REPEATABLE.  A writer pays facts in with [TsoCtx.ctx_deposit], which
   raises the stamp.

   TWO SHAPES, AND WHY THIS FILE HOLDS ONLY THE SECOND.  The escrow can
   ∃-CLOSE its context inside its own invariant ([BioInv.buf_escrow]): its
   whole access is one invariant open, so the witness never has to be
   recovered at a second open.  [started_inv]'s cannot -- it hands its
   payload out under a [▷] that is stripped one instruction later, by the
   acquire fence at main+0x18, and by then the token is back inside the
   invariant and a re-open yields a FRESH witness that nothing ties to the
   payload's.  So that record's context is NAMED: [BootShared.boot_shared_alloc]
   mints one [ξd] and returns it, [SpecMainSecondary.main_deposit] states its
   rows at [ξd], and the token rides in the one-line invariant below --
   PERSISTENT, hence shareable by all eight harts, and TIMELESS, hence out
   from under [iInv]'s [▷] with one [">"].
   (tso-absorb-memo.md §5, the second owner decision.)

   Kept in its own file, below every consumer, for the reason
   [StartedInv.v] is: [SpecMain.v] and [SpecMainSecondary.v] both need it and
   neither may drag the other in. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoCtx.

Section CtxRecord.
  Context `{!riscvGS Σ}.

  Definition ctxrecN : namespace := nroot .@ "ctxrec".

  (* THE RECORD'S TOKEN, shared.  [ctx_parked ξd T] is EXCLUSIVE, so an
     absorber takes it out and must put it back -- which [TsoCtx.ctx_absorb]
     does, at the same [T].  The stamp is ∃-bound because [ctx_deposit]
     raises it: what a reader needs is not the value but the pair
     [ctx_parked ξd T ∗ ⌜T ≤ K⌝] against its own hart view, and [T] comes
     out of this ∃ at the open. *)
  Definition ctx_parked_inv (xid : CtxId) : iProp Σ :=
    inv ctxrecN (∃ T : nat, ctx_parked xid T).

  Global Instance ctx_parked_inv_persistent xid :
    Persistent (ctx_parked_inv xid).
  Proof. apply _. Qed.

  (* TIMELESS, and it is load-bearing: the absorb runs at a SECOND open,
     after the acquire fence, and the token has to come out from under
     [iInv]'s [▷] with no step to spend.  [TsoCtx.ctx_parked_timeless] plus
     [nat]'s inhabitance is the whole proof. *)
  Global Instance ctx_parked_inv_body_timeless xid :
    Timeless (∃ T : nat, ctx_parked xid T).
  Proof. apply _. Qed.

  Lemma ctx_parked_inv_alloc (E : coPset) (xid : CtxId) (T : nat) :
    ctx_parked xid T ={E}=∗ ctx_parked_inv xid.
  Proof.
    iIntros "Hpk". iApply inv_alloc. iNext. iExists T. iExact "Hpk".
  Qed.

End CtxRecord.
