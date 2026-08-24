(* FsStateLink.v -- the link-counting resource algebra.

   Design of record: claude-notes/design/fs-state.md section 2, "Links are a
   counting RA, not an equation".

   [inode_owned Γ i n] holds [link_auth Γ i (nlink n)]; every directory entry
   other than "." (and, in the ORPHAN form, other than "..") holds one
   [link_tok Γ target].  The RA's own law gives

       link_auth Γ i n ∗ (k tokens at i)  ⊢  k ≤ n

   and THAT is the direction safety uses: at [nlink = 0] no entry points at
   the inode, so it may be freed.  The other direction (no under-count) would
   only rule out an unfreeable file -- a leak, not a corruption -- and is not
   stated anywhere.

   THE RA, AND WHY.  One [own] at the family gname [γlink Γ], over

       fsLinkUR := gmapUR Z (authR natUR)

   i.e. ONE auth-of-nat PER INUM, keyed by the inum, in a single ghost map
   element.  Two reasons for this shape over the alternatives:

   - [natUR]'s [op] is [+] and its [≼] is [≤] (iris.algebra.numbers), so the
     counting law IS [auth_both_valid_discrete] plus [nat_included] -- no new
     algebra, no local-update chain over a wide [prodUR] (which costs seconds
     per [apply], durable-notes.md).  [k] separate tokens compose to [◯ k]
     because [◯ 1 ⋅ ◯ 1 = ◯ 2].
   - Per-inum auths sit in ONE gmap camera rather than one gname per inum, so
     the whole family is allocated by a single [own_alloc] -- which is exactly
     what [fs_state_mint] needs (it must produce every logged-view auth and
     every token in one step).  A [ghost_map] of counters cannot serve: its
     elements are exclusive, so it cannot express "k tokens".

   THE CAMERA AND ITS CAPACITY CLASS LIVE IN [Xv6Cameras.v] (the camera is
   [fsLinkUR] there, since this file's [linkUR] name is already the inode
   cache's ledger camera), and since durable-disk 2b-inode-4 [fsLinkG] is an
   [Xv6G.xv6G] MEMBER: a checked-out payload carries its directory's tokens
   and the inode region parks the per-inum authority, so the class reaches
   [InodeRegion.ireg_inv] and every payload site.  The standing rule applies
   -- this file sits BELOW the bundle, so it binds the member and not
   [xv6G]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers.
From iris.base_logic.lib Require Import iprop own.
Require Export FsStateDefs.
Require Import Xv6Cameras.  (* [fsLinkUR] / [fsLinkG] -- capacity class, must be IMPORTed *)

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The camera and its capacity class                              *)
(* ------------------------------------------------------------------ *)

Section Link.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ---------------------------------------------------------------- *)
  (*  2.  The two shapes                                               *)
  (* ---------------------------------------------------------------- *)

  Definition link_auth_elem (i : Z) (n : nat) : fsLinkUR := {[ i := ● n ]}.
  Definition link_tok_elem (i : Z) (k : nat) : fsLinkUR := {[ i := ◯ k ]}.

  (* "inum [i]'s on-disk record says [n] links".  Held by [inode_owned]. *)
  Definition link_auth Γ (i : Z) (n : nat) : iProp Σ :=
    own (γlink Γ) (link_auth_elem i n).

  (* [k] tokens at inum [i], as ONE resource. *)
  Definition link_toks Γ (i : Z) (k : nat) : iProp Σ :=
    own (γlink Γ) (link_tok_elem i k).

  (* "one directory entry points at inum [i]".  Held inside [dir_owned]. *)
  Definition link_tok Γ (i : Z) : iProp Σ := link_toks Γ i 1.

  Global Instance link_auth_timeless Γ i n : Timeless (link_auth Γ i n).
  Proof. rewrite /link_auth. apply _. Qed.
  Global Instance link_toks_timeless Γ i k : Timeless (link_toks Γ i k).
  Proof. rewrite /link_toks. apply _. Qed.
  Global Instance link_tok_timeless Γ i : Timeless (link_tok Γ i).
  Proof. rewrite /link_tok. apply _. Qed.

  Lemma link_toks_split Γ i k1 k2 :
    link_toks Γ i (k1 + k2) ⊣⊢ link_toks Γ i k1 ∗ link_toks Γ i k2.
  Proof.
    rewrite /link_toks /link_tok_elem -own_op singleton_op.
    by rewrite -auth_frag_op.
  Qed.

  Lemma link_toks_one Γ i : link_toks Γ i 1 ⊣⊢ link_tok Γ i.
  Proof. done. Qed.

  (* take a PREFIX of a pile and drop the rest (the ambient logic is
     affine, so a surplus token is thrown away rather than carried) *)
  Lemma link_toks_le_split Γ i n k :
    (k <= n)%nat -> link_toks Γ i n ⊢ link_toks Γ i k ∗ link_toks Γ i (n - k).
  Proof.
    intros Hle.
    assert (Hn : n = (k + (n - k))%nat) by lia.
    rewrite {1}Hn link_toks_split. done.
  Qed.

  (* ...and the LIST form, which is the shape the boot's ticket routing
     takes ([FsCfgBoot.big_sepS_tick_route] walks a pile as a [big_sepL]).
     One direction only: at [k = 0] the pile is [own _ {[i := ◯ 0]}], which
     an [emp] cannot rebuild, and no consumer wants that direction. *)
  Lemma link_toks_list_at Γ i k j :
    link_toks Γ i k ⊢ [∗ list] _ ∈ seq j k, link_tok Γ i.
  Proof.
    revert j. induction k as [| k IH]; intros j; [iIntros "_"; done |].
    replace (seq j (S k)) with (j :: seq (S j) k) by reflexivity.
    rewrite big_sepL_cons.
    replace (S k) with (1 + k)%nat by lia.
    rewrite link_toks_split. iIntros "[$ Ht]".
    iApply (IH (S j) with "Ht").
  Qed.

  Lemma link_toks_list Γ i k :
    link_toks Γ i k ⊢ [∗ list] _ ∈ seq 0 k, link_tok Γ i.
  Proof. exact (link_toks_list_at Γ i k 0). Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  THE LAW                                                      *)
  (* ---------------------------------------------------------------- *)

  Lemma link_auth_toks_le Γ i n k :
    link_auth Γ i n -∗ link_toks Γ i k -∗ ⌜(k <= n)%nat⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    rewrite /link_auth_elem /link_tok_elem singleton_op in Hv.
    apply singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hle _].
    by apply nat_included in Hle.
  Qed.

  (* the [nlink = 0] reading the free path uses: no entry points here *)
  Lemma link_auth_zero_no_tok Γ i :
    link_auth Γ i 0 -∗ link_tok Γ i -∗ False.
  Proof.
    iIntros "Ha Hf".
    iDestruct (link_auth_toks_le with "Ha Hf") as %Hle. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4.  The two moves                                                *)
  (* ---------------------------------------------------------------- *)

  (* mint a token from the auth, incrementing n (create/link/mkdir) *)
  Lemma link_mint Γ i n :
    link_auth Γ i n ==∗ link_auth Γ i (S n) ∗ link_tok Γ i.
  Proof.
    iIntros "Ha".
    iAssert (|==> own (γlink Γ) (link_auth_elem i (S n) ⋅ link_tok_elem i 1))%I
      with "[Ha]" as ">H".
    { iApply (own_update with "Ha").
      rewrite /link_auth_elem /link_tok_elem singleton_op.
      apply singleton_update, auth_update_alloc.
      apply (nat_local_update n 0%nat (S n) 1%nat). lia. }
    iModIntro. rewrite own_op. iDestruct "H" as "[$ $]".
  Qed.

  (* return a token to the auth, decrementing n (unlink/iput) *)
  Lemma link_return Γ i n :
    link_auth Γ i (S n) -∗ link_tok Γ i ==∗ link_auth Γ i n.
  Proof.
    iIntros "Ha Hf".
    iAssert (own (γlink Γ) (link_auth_elem i (S n) ⋅ link_tok_elem i 1))%I
      with "[Ha Hf]" as "H".
    { rewrite own_op. iFrame. }
    iApply (own_update with "H").
    rewrite /link_auth_elem /link_tok_elem singleton_op.
    apply singleton_update, auth_update_dealloc.
    apply (nat_local_update (S n) 1%nat n 0%nat). lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  Allocation of a whole family                                 *)
  (*                                                                   *)
  (*  [γlink] is ONE gname for the whole file system, so a fresh        *)
  (*  instance's auths and tokens are allocated together, in one step,  *)
  (*  from one element.  That element's VALIDITY is where the           *)
  (*  "#tokens ≤ nlink" fact comes from at the mint -- it is read off   *)
  (*  the durable instance's own [own] (section 7), never proved.       *)
  (* ---------------------------------------------------------------- *)

  Lemma link_family_alloc (M : fsLinkUR) :
    ✓ M -> ⊢ |==> ∃ g : gname, own g M.
  Proof. intros HM. iMod (own_alloc M) as (g) "H"; [done |]. by iExists g. Qed.

  (* ---------------------------------------------------------------- *)
  (*  5b. THE FULL ELEMENT: an authority with all its tokens AT HOME    *)
  (*                                                                    *)
  (*  The shape the INODE REGION parks (durable-disk 2b-inode-4): one    *)
  (*  auth per inum, standing at the record's own [nlink], together with *)
  (*  exactly that many tokens.  Nothing is outstanding, so its          *)
  (*  VALIDITY is free -- no image sweep is spent at boot.  A directory  *)
  (*  entry's token is drawn out of this pile by [link_mint] at the      *)
  (*  [iupdate] that raises the count and put back by [link_return] at   *)
  (*  the one that lowers it.                                           *)
  (* ---------------------------------------------------------------- *)

  Definition link_full_elem (i : Z) (n : nat) : fsLinkUR :=
    link_auth_elem i n ⋅ link_tok_elem i n.

  Lemma link_full_elem_singleton i n :
    link_full_elem i n = {[ i := (● n ⋅ ◯ n : authR natUR) ]}.
  Proof. rewrite /link_full_elem /link_auth_elem /link_tok_elem singleton_op //. Qed.

  Lemma link_full_elem_valid i n : ✓ link_full_elem i n.
  Proof.
    rewrite link_full_elem_singleton. apply singleton_valid.
    apply auth_both_valid_discrete. split; [apply nat_included; lia | done].
  Qed.

  Lemma link_full_split Γ i n :
    own (γlink Γ) (link_full_elem i n) ⊣⊢ link_auth Γ i n ∗ link_toks Γ i n.
  Proof. rewrite /link_full_elem own_op //. Qed.

  Lemma link_auth_of_elem Γ i n :
    own (γlink Γ) (link_auth_elem i n) ⊣⊢ link_auth Γ i n.
  Proof. done. Qed.

  Lemma link_toks_of_elem Γ i k :
    own (γlink Γ) (link_tok_elem i k) ⊣⊢ link_toks Γ i k.
  Proof. done. Qed.

End Link.

(* ------------------------------------------------------------------ *)
(*  6.  Generic gathering: many [own]s into one                        *)
(*                                                                     *)
(*  [big_opM_own_1] distributes one [own] of a big-op into a [big_sepM] *)
(*  of [own]s; the converse needs the map to be non-empty, so it is     *)
(*  stated here with an ACCUMULATOR instead, which is what every use    *)
(*  site actually has (an auth to gather the tokens into, or one        *)
(*  element chosen out of a non-empty map).                            *)
(*                                                                     *)
(*  The [_opt] forms carry the [emp]/[ε] split that the tokenless       *)
(*  entries ("." always; ".." in the orphan form) need: an entry that   *)
(*  owns nothing contributes the unit.                                 *)
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
(*  [link_auth Γ i n ∗ (k separate tokens at i) ⊢ k ≤ n] -- the shape  *)
(*  a directory's [∗] over its entries actually presents.  Needs the   *)
(*  gathering of section 6, hence a section of its own.                *)
(* ------------------------------------------------------------------ *)

Section LinkLaw.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma link_tok_elem_add i k1 k2 :
    link_tok_elem i k1 ⋅ link_tok_elem i k2 ≡ link_tok_elem i (k1 + k2)%nat.
  Proof. rewrite /link_tok_elem singleton_op -auth_frag_op //. Qed.

  Lemma tok_elem_list i (l : list unit) :
    (0 < length l)%nat ->
    ([^op list] _ ∈ l, link_tok_elem i 1) ≡ link_tok_elem i (length l).
  Proof.
    induction l as [| u l IH]; [simpl; lia |].
    intros _. rewrite big_opL_cons.
    destruct l as [| v l'].
    - rewrite big_opL_nil right_id //.
    - assert (Hl : (0 < length (v :: l'))%nat) by (simpl; lia).
      rewrite (IH Hl) link_tok_elem_add //.
  Qed.

  Lemma link_auth_tok_list Γ i n (l : list unit) :
    link_auth Γ i n -∗ ([∗ list] _ ∈ l, link_tok Γ i) -∗
    ⌜(length l <= n)%nat⌝.
  Proof.
    destruct l as [| u l].
    - iIntros "_ _". iPureIntro. simpl. lia.
    - iIntros "Ha Hl".
      iDestruct (own_gather_list (A := fsLinkUR) (γlink Γ)
                   (fun _ : unit => link_tok_elem i 1) (u :: l)
                   (link_auth_elem i n) with "Ha Hl") as "H".
      iDestruct (own_valid with "H") as %Hv.
      iPureIntro.
      assert (Hpos : (0 < length (u :: l))%nat) by (simpl; lia).
      rewrite (tok_elem_list i (u :: l) Hpos) in Hv.
      rewrite /link_auth_elem /link_tok_elem singleton_op in Hv.
      apply singleton_valid in Hv.
      apply auth_both_valid_discrete in Hv as [Hle _].
      by apply nat_included in Hle.
  Qed.

End LinkLaw.
