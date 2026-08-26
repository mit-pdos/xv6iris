(* FsStateLink.v -- the TYPE REGISTER: link counts and inode types in ONE RA.

   Design of record: claude-notes/design/fs-state.md section 6.5 (lane G5),
   which supersedes section 2's plain counting RA and lanes G2/G3's separate
   parent register.

   THE RA.  Per inum, at [γlink Γ], one [authUR (gmultisetUR ity)] with

       ity := TFile | TDir (p : Z)

   ([TFile] covers T_FILE and T_DEVICE; [TDir p] carries the directory's
   PARENT).  The AUTHORITY is a UNIFORM multiset -- [link_reps n ty], i.e.
   [n] copies of one [ty] -- and lives in the inode region beside the
   record, tied to it ([InodeRegion.ireg_lnk]): [n] is the record's
   [nlink] plus one for a LIVE DIRECTORY (the ["."] the kernel does not
   count), and [ty] is [TDir _] exactly at [T_DIR].  The FRAGMENTS are
   singletons [{[+ ty +]}], one per counted dirent, and they ride in the
   naming directory's checked-out payload ([FsStateInode.ent_toks]).

   THE LAW is ONE lemma with TWO readings ([link_auth_toks_le]):

       link_auth Γ i n ty ∗ link_toks Γ i Q
         ⊢  size Q ≤ n   ∧   ∀ x ∈ Q, x = ty

   the COUNT (what the free path and [IgetLic]'s licence (a) read: at
   [n = 0] no entry points here) and the AGREEMENT (what rmdir's (D1)
   reads: a fragment's element IS the target's current type, so a
   directory's ["."] fragment names its parent).  Both fall out of
   [auth_both_valid_discrete] plus [gmultiset_included], and there is no
   local-update chain over a wide [prodUR] anywhere.

   RETYPING IS FREE AT MULTIPLICITY ZERO and impossible above it: at
   [n = 0] the authority is [● ∅] whatever [ty] is, so
   [link_auth Γ i 0 ty] and [link_auth Γ i 0 ty'] are the SAME
   proposition ([link_auth_zero_retype]) -- which is exactly the kernel's
   two type writes (ialloc's claim, iput's free deposit), both at
   [nlink = 0].  Above zero a frame [◯ {[ty]}] survives every update, so
   no retype is a frame-preserving one.

   THE CAMERA AND ITS CAPACITY CLASS LIVE IN [Xv6Cameras.v] ([fsLinkUR],
   [fsLinkG], and the type [ity] itself), since this file's [linkUR] name
   is already the inode cache's ledger camera; [fsLinkG] is an
   [Xv6G.xv6G] MEMBER because a checked-out payload carries its
   directory's fragments and the inode region parks the per-inum
   authority.  The standing rule applies -- this file sits BELOW the
   bundle, so it binds the member and not [xv6G]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap gmultiset numbers updates local_updates.
From iris.base_logic.lib Require Import iprop own.
Require Export FsStateDefs.
Require Import Xv6Cameras.  (* [ity] / [fsLinkUR] / [fsLinkG] -- must be IMPORTed *)

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The uniform multiset                                           *)
(* ------------------------------------------------------------------ *)

(* [n] copies of one type value -- the ONLY shape an authority ever takes,
   which is what makes the agreement reading available. *)
Definition link_reps (n : nat) (ty : ity) : gmultiset ity :=
  n *: ({[+ ty +]} : gmultiset ity).

Lemma link_reps_0 ty : link_reps 0 ty = ∅.
Proof. rewrite /link_reps gmultiset_scalar_mul_0 //. Qed.

Lemma link_reps_S n ty : link_reps (S n) ty = {[+ ty +]} ⊎ link_reps n ty.
Proof. rewrite /link_reps gmultiset_scalar_mul_S_l //. Qed.

Lemma link_reps_1 ty : link_reps 1 ty = {[+ ty +]}.
Proof. rewrite /link_reps gmultiset_scalar_mul_1 //. Qed.

Lemma link_reps_size n ty : size (link_reps n ty) = n.
Proof.
  rewrite /link_reps gmultiset_size_scalar_mul gmultiset_size_singleton. lia.
Qed.

Lemma link_reps_add n m ty :
  link_reps (n + m) ty = link_reps n ty ⊎ link_reps m ty.
Proof.
  induction n as [| n IH]; [rewrite link_reps_0; multiset_solver |].
  replace (S n + m)%nat with (S (n + m))%nat by lia.
  rewrite !link_reps_S IH. multiset_solver.
Qed.

Lemma link_reps_elem_of n ty x : x ∈ link_reps n ty -> x = ty.
Proof.
  rewrite /link_reps gmultiset_elem_of_scalar_mul.
  intros [_ Hx]. by apply gmultiset_elem_of_singleton in Hx.
Qed.

(* the two readings of [Q ⊆ link_reps n ty], which is what validity gives *)
Lemma link_reps_sub_size (Q : gmultiset ity) n ty :
  Q ⊆ link_reps n ty -> (size Q <= n)%nat.
Proof.
  intros Hsub. apply gmultiset_subseteq_size in Hsub.
  rewrite link_reps_size in Hsub. lia.
Qed.

Lemma link_reps_sub_elem (Q : gmultiset ity) n ty x :
  Q ⊆ link_reps n ty -> x ∈ Q -> x = ty.
Proof.
  intros Hsub Hx.
  exact (link_reps_elem_of n ty x (gmultiset_elem_of_subseteq _ _ _ Hx Hsub)).
Qed.

Section Link.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types Q : gmultiset ity.

  (* ---------------------------------------------------------------- *)
  (*  2.  The two shapes                                               *)
  (* ---------------------------------------------------------------- *)

  Definition link_auth_elem (i : Z) (n : nat) (ty : ity) : fsLinkUR :=
    {[ i := (● (link_reps n ty) : fsLinkElemUR) ]}.
  Definition link_toks_elem (i : Z) (Q : gmultiset ity) : fsLinkUR :=
    {[ i := (◯ Q : fsLinkElemUR) ]}.
  Definition link_tok_elem (i : Z) (ty : ity) : fsLinkUR :=
    link_toks_elem i {[+ ty +]}.

  (* "inum [i]'s register stands at multiplicity [n] and type [ty]".
     Parked in the inode region beside the record. *)
  Definition link_auth Γ (i : Z) (n : nat) (ty : ity) : iProp Σ :=
    own (γlink Γ) (link_auth_elem i n ty).

  (* a whole PILE of fragments at one key, as one resource *)
  Definition link_toks Γ (i : Z) (Q : gmultiset ity) : iProp Σ :=
    own (γlink Γ) (link_toks_elem i Q).

  (* "one counted directory entry points at inum [i], and [i]'s type is
     [ty]".  Held inside the naming directory's [ent_toks]. *)
  Definition link_tok Γ (i : Z) (ty : ity) : iProp Σ :=
    link_toks Γ i {[+ ty +]}.

  Global Instance link_auth_timeless Γ i n ty : Timeless (link_auth Γ i n ty).
  Proof. rewrite /link_auth. apply _. Qed.
  Global Instance link_toks_timeless Γ i Q : Timeless (link_toks Γ i Q).
  Proof. rewrite /link_toks. apply _. Qed.
  Global Instance link_tok_timeless Γ i ty : Timeless (link_tok Γ i ty).
  Proof. rewrite /link_tok. apply _. Qed.

  (* AT MULTIPLICITY ZERO THE TYPE IS NOT THERE AT ALL: the two type
     writes the kernel does (ialloc's claim, iput's free deposit) are this
     equality, not an update. *)
  Lemma link_auth_zero_retype Γ i ty ty' :
    link_auth Γ i 0 ty ⊣⊢ link_auth Γ i 0 ty'.
  Proof. rewrite /link_auth /link_auth_elem !link_reps_0 //. Qed.

  Lemma link_toks_split Γ i Q1 Q2 :
    link_toks Γ i (Q1 ⊎ Q2) ⊣⊢ link_toks Γ i Q1 ∗ link_toks Γ i Q2.
  Proof.
    rewrite /link_toks /link_toks_elem -own_op singleton_op.
    by rewrite -auth_frag_op.
  Qed.

  Lemma link_toks_one Γ i ty : link_toks Γ i {[+ ty +]} ⊣⊢ link_tok Γ i ty.
  Proof. done. Qed.

  Lemma link_toks_reps_S Γ i n ty :
    link_toks Γ i (link_reps (S n) ty)
    ⊣⊢ link_tok Γ i ty ∗ link_toks Γ i (link_reps n ty).
  Proof. rewrite link_reps_S link_toks_split //. Qed.

  (* take a PREFIX of a pile and drop the rest (the ambient logic is
     affine, so a surplus fragment is thrown away rather than carried) *)
  Lemma link_toks_le_split Γ i n k ty :
    (k <= n)%nat ->
    link_toks Γ i (link_reps n ty)
    ⊢ link_toks Γ i (link_reps k ty) ∗ link_toks Γ i (link_reps (n - k) ty).
  Proof.
    intros Hle.
    assert (Hn : n = (k + (n - k))%nat) by lia.
    rewrite {1}Hn link_reps_add link_toks_split. done.
  Qed.

  (* ...and the LIST form, which is the shape the boot's ticket routing
     takes ([FsCfgBoot.big_sepS_tick_route] walks a pile as a [big_sepL]).
     One direction only, and no consumer wants the other. *)
  Lemma link_toks_list_at Γ i k ty j :
    link_toks Γ i (link_reps k ty) ⊢ [∗ list] _ ∈ seq j k, link_tok Γ i ty.
  Proof.
    revert j. induction k as [| k IH]; intros j; [iIntros "_"; done |].
    replace (seq j (S k)) with (j :: seq (S j) k) by reflexivity.
    rewrite big_sepL_cons link_toks_reps_S. iIntros "[$ Ht]".
    iApply (IH (S j) with "Ht").
  Qed.

  Lemma link_toks_list Γ i k ty :
    link_toks Γ i (link_reps k ty) ⊢ [∗ list] _ ∈ seq 0 k, link_tok Γ i ty.
  Proof. exact (link_toks_list_at Γ i k ty 0). Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  THE LAW -- both readings at once                             *)
  (* ---------------------------------------------------------------- *)

  Lemma link_auth_toks_valid Γ i n ty Q :
    link_auth Γ i n ty -∗ link_toks Γ i Q -∗ ⌜Q ⊆ link_reps n ty⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    rewrite /link_auth_elem /link_toks_elem singleton_op in Hv.
    apply singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hle _].
    by apply gmultiset_included in Hle.
  Qed.

  Lemma link_auth_toks_le Γ i n ty Q :
    link_auth Γ i n ty -∗ link_toks Γ i Q -∗
    ⌜(size Q <= n)%nat /\ forall x, x ∈ Q -> x = ty⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_toks_valid with "Ha Hf") as %Hsub.
    iPureIntro. split.
    - exact (link_reps_sub_size Q n ty Hsub).
    - intros x Hx. exact (link_reps_sub_elem Q n ty x Hsub Hx).
  Qed.

  (* THE COUNT reading, at a pile of [k] *)
  Lemma link_auth_reps_le Γ i n ty k ty' :
    link_auth Γ i n ty -∗ link_toks Γ i (link_reps k ty') -∗ ⌜(k <= n)%nat⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_toks_le with "Ha Hf") as %[Hle _].
    iPureIntro. rewrite link_reps_size in Hle. lia.
  Qed.

  (* THE AGREEMENT reading, at ONE fragment: its element IS the target's
     current type, and the multiplicity is at least one. *)
  Lemma link_auth_tok_agree Γ i n ty ty' :
    link_auth Γ i n ty -∗ link_tok Γ i ty' -∗ ⌜ty' = ty /\ (1 <= n)%nat⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_toks_le with "Ha Hf") as %[Hle Hall].
    iPureIntro. rewrite gmultiset_size_singleton in Hle.
    split; [| lia].
    apply Hall, gmultiset_elem_of_singleton. reflexivity.
  Qed.

  (* the [n = 0] reading the free path uses: no entry points here *)
  Lemma link_auth_zero_no_tok Γ i ty ty' :
    link_auth Γ i 0 ty -∗ link_tok Γ i ty' -∗ False.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_tok_agree with "Ha Hf") as %[_ Hle]. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4.  The two moves                                                *)
  (* ---------------------------------------------------------------- *)

  (* mint a fragment from the authority, raising the multiplicity by one
     (create / link / mkdir, and a directory's own ["."]) *)
  Lemma link_mint Γ i n ty :
    link_auth Γ i n ty ==∗ link_auth Γ i (S n) ty ∗ link_tok Γ i ty.
  Proof.
    iIntros "Ha".
    iAssert (|==> own (γlink Γ) (link_auth_elem i (S n) ty
                                 ⋅ link_tok_elem i ty))%I
      with "[Ha]" as ">H".
    { iApply (own_update with "Ha").
      rewrite /link_auth_elem /link_tok_elem /link_toks_elem singleton_op.
      apply singleton_update.
      rewrite link_reps_S.
      apply auth_update_alloc, gmultiset_local_update. multiset_solver. }
    iModIntro. rewrite own_op. iDestruct "H" as "[$ $]".
  Qed.

  (* ...and give one back, lowering the multiplicity by one (unlink /
     rmdir / iput) *)
  Lemma link_return Γ i n ty ty' :
    link_auth Γ i (S n) ty -∗ link_tok Γ i ty' ==∗ link_auth Γ i n ty.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_tok_agree with "Ha Hf") as %[-> _].
    iAssert (own (γlink Γ) (link_auth_elem i (S n) ty ⋅ link_tok_elem i ty))%I
      with "[Ha Hf]" as "H".
    { rewrite own_op. iFrame. }
    iApply (own_update with "H").
    rewrite /link_auth_elem /link_tok_elem /link_toks_elem singleton_op.
    apply singleton_update.
    rewrite link_reps_S.
    apply auth_update_dealloc, gmultiset_local_update. multiset_solver.
  Qed.

  (* AN EMPTY PILE IS NOT [emp] -- it is [own _ {[i := auth-frag-empty]}],
     which is the AUTHORITY's own unit factor.  Splitting it off is the
     [k = 0] corner every [k]-at-a-time mover below has. *)
  Lemma link_toks_elem_empty i :
    link_toks_elem i (∅ : gmultiset ity) = {[ i := (ε : fsLinkElemUR) ]}.
  Proof. reflexivity. Qed.

  Lemma link_auth_elem_frag_empty i n ty :
    link_auth_elem i n ty ≡ link_auth_elem i n ty ⋅ link_toks_elem i ∅.
  Proof.
    rewrite link_toks_elem_empty /link_auth_elem singleton_op right_id //.
  Qed.

  Lemma link_toks_empty Γ i n ty :
    link_auth Γ i n ty ⊣⊢ link_auth Γ i n ty ∗ link_toks Γ i ∅.
  Proof.
    rewrite /link_auth /link_toks -own_op.
    by rewrite -link_auth_elem_frag_empty.
  Qed.

  (* the [k]-at-a-time forms, for the movers that cross the DIRECTORY
     boundary (a live directory's multiplicity is [nlink + 1]) *)
  Lemma link_mint_reps Γ i n k ty :
    link_auth Γ i n ty ==∗
    link_auth Γ i (n + k) ty ∗ link_toks Γ i (link_reps k ty).
  Proof.
    iIntros "Ha".
    iInduction k as [| k IH] "IH" forall (n).
    { iModIntro. rewrite link_reps_0 Nat.add_0_r.
      by iApply link_toks_empty. }
    iMod (link_mint with "Ha") as "[Ha Ht]".
    iMod ("IH" with "Ha") as "[Ha Hts]".
    iModIntro. replace (n + S k)%nat with (S n + k)%nat by lia.
    iFrame "Ha". rewrite link_reps_S link_toks_split. iFrame.
  Qed.

  (* THE RETURN TAKES A PILE AT ANY VALUE: at [k = 0] there is nothing to
     return, and above it the agreement law forces the caller's value to be
     the authority's. *)
  Lemma link_return_reps Γ i n k ty ty' :
    link_auth Γ i (n + k) ty -∗ link_toks Γ i (link_reps k ty') ==∗
    link_auth Γ i n ty.
  Proof.
    iIntros "Ha Ht".
    destruct k as [| k'].
    { rewrite Nat.add_0_r. by iFrame. }
    iAssert (⌜ty' = ty⌝)%I with "[Ha Ht]" as %->.
    { rewrite link_reps_S link_toks_split. iDestruct "Ht" as "[Ht _]".
      iDestruct (link_auth_tok_agree with "Ha Ht") as %[-> _]. done. }
    iClear "%".
    iInduction (S k') as [| k IH] "IH" forall (n).
    { rewrite Nat.add_0_r. by iFrame. }
    rewrite link_reps_S link_toks_split.
    iDestruct "Ht" as "[Ht Hts]".
    replace (n + S k)%nat with (S (n + k))%nat by lia.
    iMod (link_return with "Ha Ht") as "Ha".
    iApply ("IH" with "Ha Hts").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  Allocation of a whole family                                 *)
  (*                                                                   *)
  (*  [γlink] is ONE gname for the whole file system, so a fresh        *)
  (*  instance's authorities and fragments are allocated together, in   *)
  (*  one step, from one element.                                      *)
  (* ---------------------------------------------------------------- *)

  Lemma link_family_alloc (M : fsLinkUR) :
    ✓ M -> ⊢ |==> ∃ g : gname, own g M.
  Proof. intros HM. iMod (own_alloc M) as (g) "H"; [done |]. by iExists g. Qed.

  (* ---------------------------------------------------------------- *)
  (*  5b. THE FULL ELEMENT: an authority with all its fragments AT HOME *)
  (*                                                                    *)
  (*  The shape the BOOT allocates: one authority per inum, standing at  *)
  (*  the record's own multiplicity, together with exactly that many     *)
  (*  fragments.  Nothing is outstanding, so its VALIDITY is free -- no  *)
  (*  image sweep is spent at boot.                                     *)
  (* ---------------------------------------------------------------- *)

  Definition link_full_elem (i : Z) (n : nat) (ty : ity) : fsLinkUR :=
    link_auth_elem i n ty ⋅ link_toks_elem i (link_reps n ty).

  Lemma link_full_elem_singleton i n ty :
    link_full_elem i n ty
    ≡ {[ i := (● (link_reps n ty) ⋅ ◯ (link_reps n ty) : fsLinkElemUR) ]}.
  Proof.
    rewrite /link_full_elem /link_auth_elem /link_toks_elem singleton_op //.
  Qed.

  Lemma link_full_elem_valid i n ty : ✓ link_full_elem i n ty.
  Proof.
    rewrite link_full_elem_singleton. apply singleton_valid.
    apply auth_both_valid_discrete. split; [| done].
    apply gmultiset_included. done.
  Qed.

  Lemma link_full_split Γ i n ty :
    own (γlink Γ) (link_full_elem i n ty)
    ⊣⊢ link_auth Γ i n ty ∗ link_toks Γ i (link_reps n ty).
  Proof. rewrite /link_full_elem own_op //. Qed.

  Lemma link_auth_of_elem Γ i n ty :
    own (γlink Γ) (link_auth_elem i n ty) ⊣⊢ link_auth Γ i n ty.
  Proof. done. Qed.

  Lemma link_toks_of_elem Γ i Q :
    own (γlink Γ) (link_toks_elem i Q) ⊣⊢ link_toks Γ i Q.
  Proof. done. Qed.

End Link.

(* ------------------------------------------------------------------ *)
(*  6.  Generic gathering: many [own]s into one                        *)
(*                                                                     *)
(*  [big_opM_own_1] distributes one [own] of a big-op into a [big_sepM] *)
(*  of [own]s; the converse needs the map to be non-empty, so it is     *)
(*  stated here with an ACCUMULATOR instead, which is what every use    *)
(*  site actually has (an authority to gather the fragments into, or    *)
(*  one element chosen out of a non-empty map).                        *)
(*                                                                     *)
(*  The [_opt] forms carry the [emp]/[ε] split that the tokenless       *)
(*  entries (an orphan's dot records; the root's [".."]) need: an entry *)
(*  that owns nothing contributes the unit.                            *)
(* ------------------------------------------------------------------ *)

Section Gather.
  Context {Σ : gFunctors} {A : ucmra} `{!inG Σ A}.

  Lemma own_gather_list {B} (γ : gname) (f : B -> A) (l : list B) (x : A) :
    own γ x -∗ ([∗ list] y ∈ l, own γ (f y)) -∗
    own γ (x ⋅ [^op list] y ∈ l, f y).
  Proof.
    revert x. induction l as [| y l IH]; intros x.
    - iIntros "Hx _". rewrite big_opL_nil right_id //.
    - rewrite big_sepL_cons big_opL_cons.
      iIntros "Hx [Hy Hl]".
      iDestruct (own_op with "[$Hx $Hy]") as "Hxy".
      iDestruct (IH (x ⋅ f y) with "Hxy Hl") as "H".
      rewrite -assoc //.
  Qed.

  Lemma own_gather_list_opt {B} (γ : gname) (f : B -> A) (p : B -> bool)
      (l : list B) (x : A) :
    own γ x -∗ ([∗ list] y ∈ l, if p y then emp else own γ (f y)) -∗
    own γ (x ⋅ [^op list] y ∈ l, (if p y then ε else f y)).
  Proof.
    revert x. induction l as [| y l IH]; intros x.
    - iIntros "Hx _". rewrite big_opL_nil right_id //.
    - rewrite big_sepL_cons big_opL_cons.
      iIntros "Hx [Hy Hl]".
      destruct (p y) eqn:Hp.
      + iDestruct (IH x with "Hx Hl") as "H".
        rewrite (left_id ε op) //.
      + iDestruct (own_op with "[$Hx $Hy]") as "Hxy".
        iDestruct (IH (x ⋅ f y) with "Hxy Hl") as "H".
        rewrite -assoc //.
  Qed.

  Lemma own_gather_map {K V} `{Countable K} (γ : gname) (f : K -> V -> A)
      (m : gmap K V) (x : A) :
    own γ x -∗ ([∗ map] k ↦ v ∈ m, own γ (f k v)) -∗
    own γ (x ⋅ [^op map] k ↦ v ∈ m, f k v).
  Proof.
    revert x. induction m as [| k v m Hk IH] using map_ind; intros x.
    - iIntros "Hx _". by rewrite big_opM_empty right_id.
    - iIntros "Hx Hm".
      rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
      iDestruct (own_op with "[$Hx $Hv]") as "Hxv".
      iDestruct (IH (x ⋅ f k v) with "Hxv Hm") as "H".
      rewrite big_opM_insert // -assoc //.
  Qed.

  Lemma own_gather_map_opt {K V} `{Countable K} (γ : gname) (f : K -> V -> A)
      (p : K -> V -> bool) (m : gmap K V) (x : A) :
    own γ x -∗
    ([∗ map] k ↦ v ∈ m, if p k v then emp else own γ (f k v)) -∗
    own γ (x ⋅ [^op map] k ↦ v ∈ m, (if p k v then ε else f k v)).
  Proof.
    revert x. induction m as [| k v m Hk IH] using map_ind; intros x.
    - iIntros "Hx _". by rewrite big_opM_empty right_id.
    - iIntros "Hx Hm".
      rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
      rewrite big_opM_insert //.
      destruct (p k v) eqn:Hp.
      + iDestruct (IH x with "Hx Hm") as "H".
        rewrite (left_id ε op) //.
      + iDestruct (own_op with "[$Hx $Hv]") as "Hxv".
        iDestruct (IH (x ⋅ f k v) with "Hxv Hm") as "H".
        rewrite -assoc //.
  Qed.

  (* the distribution direction of the [_opt] map form *)
  Lemma own_scatter_map_opt {K V} `{Countable K} (γ : gname) (f : K -> V -> A)
      (p : K -> V -> bool) (m : gmap K V) :
    own γ ([^op map] k ↦ v ∈ m, (if p k v then ε else f k v)) ⊢
    [∗ map] k ↦ v ∈ m, (if p k v then emp else own γ (f k v)).
  Proof.
    iIntros "H".
    iDestruct (big_opM_own_1 with "H") as "H".
    iApply (big_sepM_mono with "H"). intros k v _; simpl.
    destruct (p k v); [| done].
    iIntros "_". done.
  Qed.

End Gather.

(* ------------------------------------------------------------------ *)
(*  7.  THE LAW, in its big-op form                                    *)
(*                                                                     *)
(*  The shape a directory's [∗] over its entries actually presents: a   *)
(*  LIST of fragments, each at the same key.  Needs the gathering of    *)
(*  section 6, hence a section of its own.                             *)
(* ------------------------------------------------------------------ *)

Section LinkLaw.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma link_toks_elem_add i Q1 Q2 :
    link_toks_elem i Q1 ⋅ link_toks_elem i Q2 ≡ link_toks_elem i (Q1 ⊎ Q2).
  Proof. rewrite /link_toks_elem singleton_op -auth_frag_op //. Qed.

  Lemma tok_elem_list i ty (l : list unit) :
    (0 < length l)%nat ->
    ([^op list] _ ∈ l, link_tok_elem i ty)
    ≡ link_toks_elem i (link_reps (length l) ty).
  Proof.
    induction l as [| u l IH]; [simpl; lia |].
    intros _. rewrite big_opL_cons.
    destruct l as [| v l'].
    - rewrite big_opL_nil right_id /link_tok_elem.
      simpl. rewrite link_reps_1 //.
    - assert (Hl : (0 < length (v :: l'))%nat) by (simpl; lia).
      rewrite (IH Hl) /link_tok_elem link_toks_elem_add.
      replace (length (u :: v :: l')) with (S (length (v :: l')))%nat
        by reflexivity.
      rewrite link_reps_S //.
  Qed.

  Lemma link_auth_tok_list Γ i n ty ty' (l : list unit) :
    link_auth Γ i n ty -∗ ([∗ list] _ ∈ l, link_tok Γ i ty') -∗
    ⌜(length l <= n)%nat⌝.
  Proof.
    destruct l as [| u l].
    - iIntros "_ _". iPureIntro. simpl. lia.
    - iIntros "Ha Hl".
      iDestruct (own_gather_list (A := fsLinkUR) (γlink Γ)
                   (fun _ : unit => link_tok_elem i ty') (u :: l)
                   (link_auth_elem i n ty) with "Ha Hl") as "H".
      iDestruct (own_valid with "H") as %Hv.
      iPureIntro.
      assert (Hpos : (0 < length (u :: l))%nat) by (simpl; lia).
      rewrite (tok_elem_list i ty' (u :: l) Hpos) in Hv.
      rewrite /link_auth_elem /link_toks_elem singleton_op in Hv.
      apply singleton_valid in Hv.
      apply auth_both_valid_discrete in Hv as [Hle _].
      apply gmultiset_included in Hle.
      apply link_reps_sub_size in Hle.
      rewrite link_reps_size in Hle. lia.
  Qed.

End LinkLaw.
