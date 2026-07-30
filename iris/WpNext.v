(* WpNext.v -- the continuation of every S-mode step.

   An instruction executed with interrupts ENABLED can be trapped, the thread
   yielded, and execution resumed on a DIFFERENT hart.  So a step's
   continuation quantifies the hart -- and, because the binder is named [CID],
   every resource written inside [K] is automatically about the hart we RESUME
   on, with no annotation and no change to any resource's spelling.  That
   includes the SIE ghost: it is the hart's CANONICAL name ([sie_name], hence
   [IntrDefs.sie_gname]), so rebinding [CID] rebinds the ghost too and no
   separate ghost binder is needed.

   With interrupts DISABLED no trap is taken, so the hart is pinned.  That is
   the [b = false] implication, and it is what lets push_off'd code read [tp]
   once and keep using the answer ([push_off(); c = mycpu(); c->noff++]).
   [wp_next_off] collapses the whole thing away, so an interrupts-off (or
   M-mode) contract is stated exactly as it is today, with no binder at all.

   THIS FILE IS THE ONLY PLACE THAT NAMES THE HART WE CAME FROM -- and it must
   therefore live outside any section that fixes [CpuId], because Rocq refuses
   to rebind a SECTION variable's name ("CID is already used"), which is
   exactly the shadowing every consumer relies on. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import RiscvLang.

Section WpNext.
  Context {Σ : gFunctors}.

  Definition wp_next `{CID0 : CpuId} (b : bool)
      (K : forall (CID : CpuId), iProp Σ) : iProp Σ :=
    (∀ CID : CpuId,
       ⌜ b = false -> (CID : CPU) = (CID0 : CPU) ⌝ -∗ K CID)%I.

  (* Always available, at ANY [b]: proving the hart-generic form discharges the
     step's obligation.  (The converse needs [b = false].) *)
  Lemma wp_next_intro `{CID0 : CpuId} (b : bool) K :
    (∀ CID : CpuId, K CID) -∗ wp_next b K.
  Proof. iIntros "H" (CID _). iApply "H". Qed.

  (* Interrupts off: the hart is the one we started with (and hence so is its
     canonical SIE ghost), so the continuation is stated with no binder --
     today's spelling exactly. *)
  Lemma wp_next_off `{CID0 : CpuId} K :
    wp_next false K ⊣⊢ K CID0.
  Proof.
    iSplit.
    - iIntros "H". iApply ("H" $! CID0). iPureIntro. done.
    - iIntros "H" (CID Hs). pose proof (Hs eq_refl) as Hc.
      rewrite (_ : CID = CID0); [ iExact "H" | exact Hc ].
  Qed.

  (* Chaining: the conditional equalities compose, which is what lets a
     [b]-GENERIC whole-function proof thread one implication per instruction
     and still discharge its own continuation at the end -- with no case split
     on [b] anywhere. *)
  Lemma wp_next_trans `{CID0 : CpuId} (b : bool)
      (CID1 : CpuId) (CID2 : CpuId) :
    (b = false -> (CID1 : CPU) = (CID0 : CPU)) ->
    (b = false -> (CID2 : CPU) = (CID1 : CPU)) ->
    (b = false -> (CID2 : CPU) = (CID0 : CPU)).
  Proof.
    intros H1 H2 Hb. pose proof (H1 Hb) as Ha. pose proof (H2 Hb) as Hc.
    by rewrite Hc.
  Qed.
End WpNext.

(* THE CONSUMER-SIDE DISCHARGE.  A straight-line stretch accumulates one
   conditional equality per instruction; this closes the function's own
   [wp_next] obligation from however many are in context, at any [b], with no
   case split.  Plain [eapply wp_next_trans; eassumption] does NOT do it -- the
   hypotheses arrive spelled [@cpu_id CIDk] while the lemma is stated at the
   bare binder -- so chain them by congruence instead.  (Note there is NO
   [split] here: since the SIE ghost went canonical the per-step fact is a
   bare equation, not a conjunction, and a [split] on an equation is
   [constructor 1] = [eq_refl] and would fail on the first chained step.) *)
Ltac wp_next_chain :=
  let Hb := fresh "Hb" in
  intros Hb;
  repeat match goal with
         | H : _ = false -> _ = _ |- _ => specialize (H Hb)
         end;
  solve [ congruence
        | repeat match goal with
                 | H : ?a = ?b |- ?a = ?c => rewrite H; clear H
                 end; reflexivity ].
