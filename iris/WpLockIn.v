(* WpLockIn.v -- THE INPUT-SIDE FINISHER (tso-port.md §0.42′; tso-machine-flip.md
   A6.127 §6): a release whose payload is ALREADY PARKED.

   [WpLock.lock_finisher]'s prelude is [own_context cur_ctx -∗ R cur_ctx ==∗
   own_context cur_ctx ∗ Pay]: release takes the payload at the caller's own
   context and the closing finisher deposits it into a fresh parked context
   ([lock_pay_intro]).  A release that CREATES a parked-thread record cannot
   state [R cur_ctx]: the record's link ([SchedCtx.proc_ctx]) is a floor on
   the PARK BOX the record came with, and no running context's bound covers
   a fresh park.  What such a release holds is [lock_pay R] outright -- the
   box IS the lock's context.  So the prelude here takes only the running
   token, and the caller has closed over its own material.  The ordinary
   finisher is the special case ([lock_finisher_to_in]).

   WHY ITS OWN FILE: [WpLock.v] sits under 684 files; this is thirty lines
   off its public definitions ([TsoCtxAbsorbLb] / [TsoCtxPark] precedent).

   ON MAIN (main-tso-readiness.md Amendment 9): this file is tso-flip r51's
   text; the one deviation is [lock_finisher_close_body]'s proof tail, which
   is main's [WpLock.lock_finisher_close] tail because main's [lock_inv] has
   no [lock_word_fresh] / [lk_cpu_fresh] ledger pieces (A6.89, below the
   seal). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6G.
Require Import TsoCtx.
Require Import WpLock.
Local Open Scope Z_scope.

Section LockIn.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  Definition lock_finisher_in `{CID : CpuId} (γ : gname) (lk : mword 64)
      (s : string) (R : CtxId → iProp Σ) (D Out : iProp Σ)
      (E : coPset) : iProp Σ :=
    (∃ Pay : iProp Σ,
       (own_context cur_ctx ==∗ own_context cur_ctx ∗ Pay) ∗
       lock_finisher_body γ lk s R D Out E Pay)%I.

  (* the ordinary finisher, with its payload in hand, is an input-side one *)
  Lemma lock_finisher_to_in `{CID : CpuId} γ lk s R D Out E :
    R cur_ctx -∗ lock_finisher γ lk s R D Out E -∗ lock_finisher_in γ lk s R D Out E.
  Proof.
    iIntros "HR (%Pay & Hpre & Hbody)". iExists Pay. iFrame "Hbody".
    iIntros "Hrun". iApply ("Hpre" with "Hrun HR").
  Qed.

  (* the closing body alone: what [WpLock.lock_finisher_close] proves after
     its prelude, factored so a pre-parked payload can use it *)
  Lemma lock_finisher_close_body γ lk s R D E :
    ⊢ lock_finisher_body γ lk s R D emp E (lock_pay R).
  Proof.
    iIntros (lo) "[Hclose _] Hauth Hfrag Hword Hcpu _ HR".
    iDestruct "Hauth" as (B) "Hauth".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iApply bi.later_intro. iExists (mword_of_int 0 : mword 32), None, B.
    rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed.

  (* THE CLOSING FINISHER FOR A PRE-PARKED PAYLOAD: the caller hands the free
     arm's record itself.  No [CtxMorph R] is needed -- nothing is morphed. *)
  Lemma lock_finisher_close_in `{CID : CpuId} γ lk s R D E :
    (own_context cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R) -∗
    lock_finisher_in γ lk s R D emp E.
  Proof.
    iIntros "Hpre". iExists (lock_pay R). iFrame "Hpre".
    iApply lock_finisher_close_body.
  Qed.

  (* ...and the plainest form: the record in hand, no token consulted *)
  Lemma lock_finisher_close_pay `{CID : CpuId} γ lk s R D E :
    lock_pay R -∗ lock_finisher_in γ lk s R D emp E.
  Proof.
    iIntros "Hpay". iApply lock_finisher_close_in. iIntros "Hrun". iModIntro. iFrame.
  Qed.

End LockIn.
