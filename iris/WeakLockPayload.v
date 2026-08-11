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
Require Import WeakViewMono WeakPtOwn WeakPtPub WeakObj.

(** One entry of the protected structure: an address and the byte it holds.
    Deliberately plain — the point is the SHAPE of the predicate over a
    list of these, not the entry. *)
Record item := Item { it_a : Z; it_v : bv 8 }.

Section payload.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{CID : CpuId}.

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
      This is the whole claim of [WeakObj], at a payload with real
      structure. *)

  Lemma table_acquire T l :
    vrNew_lb T -∗ monPred_at (table_inv l) (view_scl T) -∗ wobj (table_inv l).
  Proof. apply wobj_acquire. Qed.

  Lemma table_release ws T l :
    (∀ a, (flr (ws_view ws) a ≤ T)%nat) ->
    ws_auth (weak_view_name cpu_id) ws -∗ wobj (table_inv l) -∗
    ws_auth (weak_view_name cpu_id) ws ∗ monPred_at (table_inv l) (view_scl T).
  Proof. apply wobj_release. Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The decomposition, DERIVED.

      A client that has acquired holds [wobj (table_inv l)] and normally
      peels only the item it touches.  But the full decomposition is
      available, and every step of it is a structural law from [WeakObj] —
      no lemma here is specific to this payload's shape. *)

  Lemma item_obj x :
    wobj (item_inv x) ⊣⊢ ⌜(0 < it_a x)%Z⌝ ∗ it_a x ↦o it_v x.
  Proof. by rewrite /item_inv wobj_sep wobj_pure wpt_own_wobj. Qed.

  (** [wobj] through the [big_sepL]: one rewrite. *)
  Lemma items_obj l :
    wobj (items_inv l) ⊣⊢
      [∗ list] x ∈ l, (⌜(0 < it_a x)%Z⌝ ∗ it_a x ↦o it_v x).
  Proof.
    rewrite /items_inv wobj_big_sepL.
    apply big_sepL_proper => k x _. apply item_obj.
  Qed.

  (** ... and through all three levels at once.  Compare what this would
      have cost with [wpt_pub]: a second copy of all three definitions,
      each carrying a [T]. *)
  Lemma table_obj l :
    wobj (table_inv l) ⊣⊢
      ⌜NoDup (it_a <$> l)⌝ ∗ G ∗
      [∗ list] x ∈ l, (⌜(0 < it_a x)%Z⌝ ∗ it_a x ↦o it_v x).
  Proof.
    by rewrite /table_inv !wobj_sep wobj_pure wobj_embed items_obj.
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
  Lemma table_round_trip ws T l :
    (∀ a, (flr (ws_view ws) a ≤ T)%nat) ->
    (T ≤ w_vrNew ws)%nat ->
    ws_auth (weak_view_name cpu_id) ws -∗ wobj (table_inv l) -∗
    ws_auth (weak_view_name cpu_id) ws ∗ wobj (table_inv l).
  Proof.
    iIntros (HT Hacq) "Hauth HR".
    iDestruct (table_release with "Hauth HR") as "[Hauth Hpub]"; [exact HT|].
    iDestruct (vrNew_lb_get _ _ Hacq with "Hauth") as "#Hlb".
    iFrame "Hauth". by iApply (table_acquire with "Hlb Hpub").
  Qed.

End payload.
