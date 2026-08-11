(** * WeakLockPayload.v — a WORKED lock payload, to check the claim.

    THE QUESTION.  [WeakObj] says a lock payload should be written as a
    [vProp] and lifted by [monPred_at] / [wobj].  A real payload is not one
    byte: it is a list of items, each owning memory, nested a few
    definitions deep, mixed with pure facts and ghost state.  Does writing
    THAT as a [vProp] cost anything — in particular, does [big_sepL] need
    redefining, or the payload need reshaping?

    THE ANSWER, checked below rather than asserted: no.  [big_sepL] and
    friends are defined generically over [PROP : bi] in [iris/bi/big_op.v],
    and [WeakView.vProp] is a [bi], so the combinators and their whole
    lemma library apply unchanged.  Iris additionally ships
    [monPred_at_big_sepL] / [monPred_at_big_sepM] (from
    [monPred_at_monoid_sep_homomorphism]) and [big_sepL_objective] /
    [big_sepM_objective].

    THE DIFF FROM THE SC TWIN of the same payload is exactly two tokens per
    definition:

      SC     [Definition items (l : list item) : iProp Σ :=]
             [  ([∗ list] x ∈ l, it_a x ↦ₘ it_v x)%I.]
      WEAK   [Definition items (l : list item) : vProp Σ :=]
             [  ([∗ list] x ∈ l, it_a x ↦w it_v x)%I.]

    the type ascription and the arrow.  [[∗ list]] and [%I] are unchanged
    because [bi_scope] resolves at whichever [bi] is expected.  Genuine
    [iProp]s (ghost state) gain [⎡ ⎤] — [G] below stands for any of them.

    WHAT THE DECOMPOSITION LEMMAS BELOW SHOW.  They are DERIVED, not
    written: [table_obj] pushes [wobj] through three levels of nesting, a
    [big_sepL], two pure facts and an embedding, using only the structural
    laws.  Note that a client does not normally need them at all — the
    boundary lemmas apply to the whole payload — but they are what makes
    "no per-definition transport lemma" checkable rather than a claim. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import auth numbers functions dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map mono_nat.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakCtx WeakPtPub.

(** One entry of the protected structure: an address and the byte it holds.
    Deliberately plain — the point is the SHAPE of the predicate over a
    list of these, not the entry. *)
Record item := Item { it_a : Z; it_v : bv 8 }.

Section payload.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{CID : CpuId}.
  Context (ξ : CtxId).

  (** Any ghost resource the payload also owns.  Kept abstract so the
      example says something about ALL of them rather than one. *)
  Context (G : iProp Σ).

  (* ------------------------------------------------------------------ *)
  (** ** 1. The payload, written the way the SC one would be *)

  (** Level 1: one item.  A pure well-formedness fact next to the memory —
      the ordinary mix. *)
  Definition item_inv (x : item) : vProp Σ :=
    (⌜(0 < it_a x)%Z⌝ ∗ it_a x ↦w it_v x)%I.

  (** Level 2: the list.  THIS IS THE LINE THE QUESTION WAS ABOUT — an
      ordinary [big_sepL], at [vProp], with no redefinition anywhere. *)
  Definition items_inv (l : list item) : vProp Σ :=
    ([∗ list] x ∈ l, item_inv x)%I.

  (** Level 3: the whole thing — a global pure invariant, some ghost state
      that is already an [iProp], and the list. *)
  Definition table_inv (l : list item) : vProp Σ :=
    (⌜NoDup (it_a <$> l)⌝ ∗ ⎡ G ⎤ ∗ items_inv l)%I.

  (* ------------------------------------------------------------------ *)
  (** ** 2. THE BOUNDARY — what a lock spec actually applies.

      Both are the generic lemma at [R := table_inv l].  Neither mentions
      the list, the nesting, or a byte; neither grows if the payload does.

      Since the move to [WeakCtx], both take the CONTEXT's authority rather
      than a hart's, which is what makes them usable on either side of a
      migration: the [ξ] here is the same [ξ] on the resuming hart. *)

  Lemma table_acquire V T l :
    (∀ a, (T ≤ flr V a)%nat) ->
    ctx_auth ξ V -∗ monPred_at (table_inv l) (view_scl T) -∗
    ctx_auth ξ V ∗ cobj ξ (table_inv l).
  Proof. apply cobj_acquire. Qed.

  Lemma table_release V T l :
    (∀ a, (flr V a ≤ T)%nat) ->
    ctx_auth ξ V -∗ cobj ξ (table_inv l) -∗
    ctx_auth ξ V ∗ monPred_at (table_inv l) (view_scl T).
  Proof. apply cobj_release. Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The decomposition, DERIVED.

      Every step is a structural law from [WeakCtx]; no lemma here is
      specific to this payload's shape. *)

  Lemma item_obj x :
    cobj ξ (item_inv x) ⊣⊢ ⌜(0 < it_a x)%Z⌝ ∗ cobj ξ (it_a x ↦w it_v x).
  Proof. by rewrite /item_inv cobj_sep cobj_pure. Qed.

  Lemma items_obj l :
    cobj ξ (items_inv l) ⊣⊢
      [∗ list] x ∈ l, (⌜(0 < it_a x)%Z⌝ ∗ cobj ξ (it_a x ↦w it_v x)).
  Proof.
    rewrite /items_inv cobj_big_sepL.
    apply big_sepL_proper => k x _. apply item_obj.
  Qed.

  Lemma table_obj l :
    cobj ξ (table_inv l) ⊣⊢
      ⌜NoDup (it_a <$> l)⌝ ∗ G ∗
      [∗ list] x ∈ l, (⌜(0 < it_a x)%Z⌝ ∗ cobj ξ (it_a x ↦w it_v x)).
  Proof.
    by rewrite /table_inv !cobj_sep cobj_pure cobj_embed items_obj.
  Qed.

  (** The same payload as the INVARIANT sees it, for contrast: the frozen
      form is [wpt_pub T] per byte, hart-free and absolute.  Deriving this
      is also one rewrite — but note nobody has to: the invariant stores
      [monPred_at (table_inv l) (view_scl T)] and never looks inside. *)
  Lemma table_pub T l :
    monPred_at (table_inv l) (view_scl T) ⊣⊢
      ⌜NoDup (it_a <$> l)⌝ ∗ G ∗
      [∗ list] x ∈ l, (⌜(0 < it_a x)%Z⌝ ∗ wpt_pub T (it_a x) (DfracOwn 1) (it_v x)).
  Proof.
    rewrite /table_inv !monPred_at_sep monPred_at_pure monPred_at_embed.
    rewrite /items_inv monPred_at_big_sepL.
    do 2 f_equiv. apply big_sepL_proper => k x _.
    rewrite /item_inv monPred_at_sep monPred_at_pure wpt_pub_frozen //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. And the round trip, on this payload.

      What a client of the spinlock sees: the structure goes in objectively
      and comes back objectively, and the two weak-memory side conditions
      are the lock's business, not the client's. *)
  Lemma table_round_trip V T l :
    (∀ a, (flr V a ≤ T)%nat) ->
    (∀ a, (T ≤ flr V a)%nat) ->
    ctx_auth ξ V -∗ cobj ξ (table_inv l) -∗
    ctx_auth ξ V ∗ cobj ξ (table_inv l).
  Proof.
    iIntros (HT Hacq) "Hauth HR".
    iDestruct (table_release with "Hauth HR") as "[Hauth Hpub]"; [exact HT|].
    by iApply (table_acquire with "Hauth Hpub").
  Qed.

End payload.
