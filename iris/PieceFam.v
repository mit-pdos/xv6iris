(* PieceFam.v -- THE ONE-SHOT PIECE'S FAMILY PAIR: a receipt beside a
   refund, in one record.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-4
   (the AU bundles), claude-notes/projects/app-echo.md ("REFUNDS, RULED").

   ==== WHAT A ONE-SHOT PIECE COSTS ITS CALLER =========================

   A syscall's caller-supplied input is a [∗] of independent ONE-SHOT
   pieces -- a commit, an undo leg, a slot wand.  Each piece is handed in
   as [AU ∧ R]: the caller proves the fupd and its REFUND [R] from the
   same context, the kernel eliminates to the fupd when it fires the piece
   and hands the whole conjunction back otherwise, so a caller that did
   not get its fire eliminates to [R] and recovers what it invested.  A
   FIRED piece returns its investment through the RECEIPT it chose
   instead, which is why the two travel together.

   [pfam Σ A] is that pair: [pf_recv] is the receipt family (its type [A]
   is the piece's own -- [aview -> Z -> anode -> iProp Σ] for an
   observation, [aview -> Z -> fname -> Z -> iProp Σ] for an entry write,
   [uvis -> iProp Σ] for exec's slot) and [pf_refund] is the refund.  The
   [∧] itself is spelled AT THE ASSEMBLY, once, as [pf_at] below: a bundle
   is a [∗] of [pf_at]s and every arm that returns a piece unfired returns
   the same [pf_at].  THE PIECE DEFINITIONS THEMSELVES ARE UNTOUCHED --
   they take a bare receipt family, which is what makes each of them still
   statable, satisfiable and pinnable on its own.

   ==== WHY A RECORD AND NOT TWO ARGUMENTS =============================

   One [R] per piece is the ruling, and the pieces are many: create fires
   five, sys_open six.  Spelled flat, [SYSOPEN]'s family list runs to
   fourteen and [CREATE]'s to twelve.  Paired, every list stays at the
   length it has today, the pairing is 1:1 with the pieces BY
   CONSTRUCTION (there is exactly one receipt family per piece in every
   syscall), and the TYPE says which families belong to a one-shot piece:
   a [pfam] is a piece's, a bare function is a CURSOR's.  The walk's
   [P]/[Pmiss] and the write chain's [Q] stay bare for precisely that
   reason -- a sequenced piece already carries its refund as its cursor
   and owes no second one.

   ==== THE TRIVIAL PAIR ===============================================

   A caller that answers for no abstract state hands every piece the
   trivial refund, and [pfam_triv Φ] is the pair that does: the caller's
   receipt beside [True].  The receipt stays explicit ON PURPOSE -- a
   class resolving the constant-[True] function structurally on the type
   was tried and refused: its arrow instance fires on an OPEN [A], so
   [iApply] against a goal whose family is still an evar guesses a type
   and then declines to unify (durable-notes, "A class used as an INDEX").
   Spelling the receipt costs one [fun _ _ => True%I] and has no
   elaboration failure mode.

   ==== REDUCING A LITERAL PAIR ========================================

   [cbn [pf_recv pf_refund]] is the house move for a goal holding a
   projection of a pair the proof just built ([pfam_triv Φ], [MkPfam S Rs],
   [FsAbsReadFire.arf_pin_fam]): a bare [/=] there is [simpl] over a
   syscall-altitude goal and overflows the stack rather than reducing the
   two fields.

   ==== THE TRANSPORT ==================================================

   [refund_mono] is what moves a piece under the conjunction: a mover
   stated on the AU side alone ([FsAbsCreateFire.acre_commit_at_gen_ext]
   is the one this file exists for) lifts to the pair because [iProp] is
   AFFINE -- [iSplit] hands the whole context to both conjuncts, so the
   refund branch may simply drop the mover. *)

From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.

(* ===================================================================== *)
(*  1.  THE PAIR                                                          *)
(* ===================================================================== *)

Record pfam (Σ : gFunctors) (A : Type) : Type :=
  MkPfam { pf_recv : A ; pf_refund : iProp Σ }.

Global Arguments MkPfam {Σ A} _ _.
Global Arguments pf_recv {Σ A} _.
Global Arguments pf_refund {Σ A} _.

(* ===================================================================== *)
(*  1b.  THE PIECE AS THE CALLER HANDS IT IN                              *)
(* ===================================================================== *)

(* [pf_at AU F] is the one-shot piece [AU] at the family [F], CONJOINED
   with [F]'s refund -- the [AU ∧ R] of the ruling, with the pair supplying
   both halves.  Every bundle is a [∗] of these and every arm that returns
   a piece unfired returns one; a fire opens it with [refund_au].

   [AU] is the piece with its receipt slot ABSTRACTED, which for every
   commit is simply the piece applied to all its other arguments
   ([pf_at (dlookup_commit_at Γ appE) Fex]) and for exec's slot wand -- whose
   payload is not its last argument -- a one-binder lambda.  Writing it this
   way is also what keeps a discharger's goal readable: [AU] determines the
   receipt type, so nothing needs a type ascription. *)
Definition pf_at {Σ : gFunctors} {A : Type}
    (AU : A -> iProp Σ) (F : pfam Σ A) : iProp Σ :=
  (AU F.(pf_recv) ∧ F.(pf_refund))%I.

(* ===================================================================== *)
(*  2.  THE TRIVIAL PAIR                                                  *)
(* ===================================================================== *)

Definition pfam_triv {Σ : gFunctors} {A : Type} (Φ : A) : pfam Σ A :=
  MkPfam Φ True%I.

(* ===================================================================== *)
(*  3.  THE TRANSPORT UNDER THE CONJUNCTION                               *)
(* ===================================================================== *)

Section Refund.
  Context {Σ : gFunctors}.
  Implicit Types A R : iProp Σ.

  (* A mover on the AU side lifts to the pair.  [iProp] is affine, so the
     refund branch drops the mover and the two branches share the context
     the [∧] hands each of them. *)
  Lemma refund_mono (A A' R : iProp Σ) :
    (A -∗ A') -∗ (A ∧ R) -∗ (A' ∧ R).
  Proof.
    iIntros "HW H". iSplit.
    - iDestruct "H" as "[H _]". iApply ("HW" with "H").
    - iDestruct "H" as "[_ H]". iExact "H".
  Qed.

  (* ...and the entailment-shaped mover, where the wand has no resources
     of its own (the common case: a definitional weakening). *)
  Lemma refund_mono_ent (A A' R : iProp Σ) :
    (A ⊢ A') -> (A ∧ R) ⊢ (A' ∧ R).
  Proof.
    intros HA. iIntros "H". iSplit.
    - iDestruct "H" as "[H _]". iApply (HA with "H").
    - iDestruct "H" as "[_ H]". iExact "H".
  Qed.

  (* the elimination the fire lemmas open with, named so a proof reads as
     "the piece is spent" rather than as an anonymous projection *)
  Lemma refund_au (A R : iProp Σ) : (A ∧ R) ⊢ A.
  Proof. iIntros "[$ _]". Qed.

  Lemma refund_ref (A R : iProp Σ) : (A ∧ R) ⊢ R.
  Proof. iIntros "[_ $]". Qed.

  (* ...at [pf_at]: what a FIRE takes, and what a caller that did not get
     its fire eliminates the returned piece to *)
  Lemma pf_at_au {A : Type} (AU : A -> iProp Σ) (F : pfam Σ A) :
    pf_at AU F ⊢ AU F.(pf_recv).
  Proof. rewrite /pf_at. iIntros "[$ _]". Qed.

  Lemma pf_at_refund {A : Type} (AU : A -> iProp Σ) (F : pfam Σ A) :
    pf_at AU F ⊢ F.(pf_refund).
  Proof. rewrite /pf_at. iIntros "[_ $]". Qed.

  (* the intro a discharger uses: prove the AU and the refund from the
     same context, which is the ruling's own sentence *)
  Lemma pf_at_intro {A : Type} (AU : A -> iProp Σ) (F : pfam Σ A) :
    AU F.(pf_recv) ∧ F.(pf_refund) ⊢ pf_at AU F.
  Proof. by rewrite /pf_at. Qed.

  (* the discharger's shape at the TRIVIAL PAIR: prove the AU at the
     trivial receipt and the refund is [True].  Every [fsabs_*] and every
     [_unit] bundle goes through this, so no proof reduces the record. *)
  Lemma pf_at_triv {A : Type} (Φ : A) (AU : A -> iProp Σ) :
    AU Φ ⊢ pf_at AU (pfam_triv Φ).
  Proof.
    rewrite /pf_at /pfam_triv /=. iIntros "H". iSplit; [iExact "H" | done].
  Qed.

  (* the mover, at [pf_at]: [refund_mono] with the pair's halves supplied.
     The same family throughout -- a mover restates the AU, never the pair
     ([FsAbsCreateFire.acre_commit_at_gen_ext] is the worked instance). *)
  Lemma pf_at_mono {A : Type} (AU AU' : A -> iProp Σ) (F : pfam Σ A) :
    (AU F.(pf_recv) -∗ AU' F.(pf_recv)) -∗ pf_at AU F -∗ pf_at AU' F.
  Proof.
    rewrite /pf_at. iIntros "HW H". iApply (refund_mono with "HW H").
  Qed.

  (* ...and between TWO pairs that share a refund, which is what a receipt
     ENRICHMENT is: the wrapper stays on the [pf_recv] side, so the two
     refunds are the same term and the equation is [eq_refl]
     ([SpecSysMknod.mkr_fam] is the worked instance). *)
  Lemma pf_at_mono_pair {A B : Type} (AU : A -> iProp Σ) (AU' : B -> iProp Σ)
      (F : pfam Σ A) (G : pfam Σ B) :
    F.(pf_refund) = G.(pf_refund) ->
    (AU F.(pf_recv) -∗ AU' G.(pf_recv)) -∗ pf_at AU F -∗ pf_at AU' G.
  Proof.
    intros HR. rewrite /pf_at HR. iIntros "HW H".
    iApply (refund_mono with "HW H").
  Qed.
End Refund.
