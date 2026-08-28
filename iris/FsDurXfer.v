(* ====================================================================== *)
(*  FsDurXfer.v -- THE RESOURCE TRANSPORT (durable-disk lane H;            *)
(*  claude-notes/design/durable-fs-plan.md sections 4 and 5)               *)
(*                                                                        *)
(*  BOTH ENDS OF EVERY TRANSPORT ARE [FsState.fs_state]s, and NOTHING is   *)
(*  ever computed from the abstract state [S] but the state itself.  The   *)
(*  value-first allocator this file replaces took a BYTE MAP plus a pure   *)
(*  disjointness/cut record and CARVED a freshly allocated map by it; the  *)
(*  carve was an artifact of the input TYPE, because a byte map is one     *)
(*  linear resource and the file system is a [∗] of many.                  *)
(*                                                                        *)
(*  WITH AN INSTANCE AS INPUT there is nothing to carve: each object's     *)
(*  fresh elements are minted from THAT OBJECT'S OWN source fragments, so  *)
(*  the [∗] shape is inherited object by object.  The one fact the mint    *)
(*  needs -- that two objects never name one byte -- is not stated, not    *)
(*  maintained and not passed in: it is READ OFF THE SOURCE'S OWN          *)
(*  EXCLUSIVITY inside this file ([phi_runs_disj]; two full fragments at   *)
(*  one address are inconsistent, [FsStateDefs.phi_excl]).                 *)
(*                                                                        *)
(*  THE SHAPE, bottom up:                                                  *)
(*                                                                        *)
(*    1.  A RUN is a (block, offset, bytes) triple; [xr_map] is its flat   *)
(*        byte map and [phi_runs] the [∗] of the runs at a view.           *)
(*    2.  [phi_runs_disj]: the runs' maps are pairwise disjoint, off       *)
(*        [phi_excl] alone.  It is a PURE conclusion, so reading it costs  *)
(*        nothing (the affine [pure_keep] device, one level down).         *)
(*    3.  [phi_runs_union]: with that disjointness the [∗] of the runs IS  *)
(*        the [∗] of ONE map -- in both directions, and Gamma-generically. *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import DiskImg.       (* [diskImgG] -- the fresh byte map's class *)
Require Import BitmapEnc.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import FsImg.
Require Import Xv6Cameras.
Require Import FsDurBytes.    (* the byte-map flattening, and [snap_gamma]
                                 -- the durable family's record, which sits
                                 there because [FsDurRead] needs it too *)
Require Export FsState.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  TWO SHARES THAT EACH EXCEED A HALF (durable-disk lane H4)          *)
(*                                                                        *)
(*  Moved down from [FsCollect], which is where they were first needed and *)
(*  which is ABOVE this file: the share-generic transport of section 5     *)
(*  reads its disjointness at two DIFFERENT objects' shares, and           *)
(*  [dfrac_nvalid_pair] is the whole of that arithmetic.                   *)
(* ====================================================================== *)

(* TWO SHARES THAT EACH EXCEED A HALF CANNOT BOTH FIT INSIDE ONE, twice:
   the strict half (two [DfracOwn]s, whose sum must merely be [<= 1]) and
   the non-strict one (a [DfracBoth] on either side, whose sum must be
   [< 1]).  Both are the same contradiction -- if the sum fitted, each
   share would have to be smaller than the other. *)
Lemma qp_no_pair_lt (q1 q2 : Qp) :
  (1 < q1 + q1)%Qp -> (1 < q2 + q2)%Qp -> (q1 + q2 ≤ 1)%Qp -> False.
Proof.
  intros H1 H2 Hle.
  assert (Ha : (q2 < q1)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q2 q1 q1)).
    exact (Qp.le_lt_trans _ _ _ Hle H1). }
  assert (Hb : (q1 < q2)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q1 q2 q2)).
    rewrite (Qp.add_comm q2 q1).
    exact (Qp.le_lt_trans _ _ _ Hle H2). }
  exact (proj1 (Qp.lt_nge q2 q1) Ha (Qp.lt_le_incl _ _ Hb)).
Qed.

Lemma qp_no_pair_le (q1 q2 : Qp) :
  (1 ≤ q1 + q1)%Qp -> (1 ≤ q2 + q2)%Qp -> (q1 + q2 < 1)%Qp -> False.
Proof.
  intros H1 H2 Hlt.
  assert (Ha : (q2 < q1)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q2 q1 q1)).
    exact (Qp.lt_le_trans _ _ _ Hlt H1). }
  assert (Hb : (q1 < q2)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q1 q2 q2)).
    rewrite (Qp.add_comm q2 q1).
    exact (Qp.lt_le_trans _ _ _ Hlt H2). }
  exact (proj1 (Qp.lt_nge q2 q1) Ha (Qp.lt_le_incl _ _ Hb)).
Qed.

(* A SHARE WHOSE DOUBLE IS INVALID owns more than a half and is not the
   bare discarded knowledge (which doubles to itself). *)
Lemma dfrac_nvalid_shape (dq : dfrac) :
  ~ ✓ (dq ⋅ dq) ->
  exists q : Qp,
    (dq = DfracOwn q /\ (1 < q + q)%Qp)
    \/ (dq = DfracBoth q /\ (1 ≤ q + q)%Qp).
Proof.
  destruct dq as [q | | q]; intros Hn.
  - exists q. left. split; [reflexivity |].
    apply (proj2 (Qp.lt_nge 1 (q + q))). intros Hc. apply Hn.
    rewrite dfrac_op_own. apply dfrac_valid_own. exact Hc.
  - exfalso. apply Hn. rewrite dfrac_op_discarded.
    exact dfrac_valid_discarded.
  - exists q. right. split; [reflexivity |].
    apply (proj2 (Qp.le_ngt 1 (q + q))). intros Hc. apply Hn.
    apply dfrac_valid. cbn. exact Hc.
Qed.

Lemma dfrac_nvalid_pair (dq1 dq2 : dfrac) :
  ~ ✓ (dq1 ⋅ dq1) -> ~ ✓ (dq2 ⋅ dq2) -> ~ ✓ (dq1 ⋅ dq2).
Proof.
  intros H1 H2 Hv.
  destruct (dfrac_nvalid_shape dq1 H1) as (q1 & [[-> Hq1] | [-> Hq1]]);
    destruct (dfrac_nvalid_shape dq2 H2) as (q2 & [[-> Hq2] | [-> Hq2]]).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_lt q1 q2 Hq1 Hq2 Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 (Qp.lt_le_incl _ _ Hq1) Hq2 Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 Hq1 (Qp.lt_le_incl _ _ Hq2) Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 Hq1 Hq2 Hv).
Qed.

(* ...and the one reading of it the collection runs. *)
Lemma dfrac_full_pair (dq : dfrac) : ~ ✓ (DfracOwn 1 ⋅ dq).
Proof. exact (dfrac_full_nvalid dq). Qed.

(* ====================================================================== *)
(*  1.  RUNS                                                               *)
(* ====================================================================== *)

Definition xrun : Type := (Z * Z * list (bv 8))%type.

Definition xr_blk (r : xrun) : Z := r.1.1.
Definition xr_off (r : xrun) : Z := r.1.2.
Definition xr_bs  (r : xrun) : list (bv 8) := r.2.

Definition xr_map (r : xrun) : gmap Z (bv 8) :=
  map_seqZ (xr_blk r * BSIZE_z + xr_off r) (xr_bs r).

Definition xr_union (l : list xrun) : gmap Z (bv 8) :=
  union_list (xr_map <$> l).

(* pairwise disjointness, BY POSITION (a list may repeat an empty run) *)
Definition xr_disj (l : list xrun) : Prop :=
  forall (k j : nat) r1 r2, k <> j ->
    l !! k = Some r1 -> l !! j = Some r2 -> xr_map r1 ##ₘ xr_map r2.

Lemma xr_union_nil : xr_union [] = ∅.
Proof. reflexivity. Qed.

Lemma xr_union_cons (r : xrun) (l : list xrun) :
  xr_union (r :: l) = xr_map r ∪ xr_union l.
Proof. reflexivity. Qed.

Lemma xr_disj_cons (r : xrun) (l : list xrun) :
  xr_disj (r :: l) ->
  xr_disj l /\ (forall j r2, l !! j = Some r2 -> xr_map r ##ₘ xr_map r2).
Proof.
  intros Hd. split.
  - intros k j r1 r2 Hne Hk Hj.
    apply (Hd (S k) (S j) r1 r2 ltac:(lia) Hk Hj).
  - intros j r2 Hj.
    apply (Hd 0%nat (S j) r r2 ltac:(lia) eq_refl Hj).
Qed.

Lemma xr_disj_head (r : xrun) (l : list xrun) :
  xr_disj (r :: l) -> xr_map r ##ₘ xr_union l.
Proof.
  intros Hd. destruct (xr_disj_cons r l Hd) as [_ Hhd].
  clear Hd. revert Hhd. induction l as [| r' l IH]; intros Hhd.
  - rewrite xr_union_nil. apply map_disjoint_empty_r.
  - rewrite xr_union_cons. apply map_disjoint_union_r. split.
    + apply (Hhd 0%nat r' eq_refl).
    + apply IH. intros j r2 Hj. apply (Hhd (S j) r2 Hj).
Qed.

Lemma xr_disj_app (l1 l2 : list xrun) :
  xr_disj (l1 ++ l2) -> xr_disj l1 /\ xr_disj l2.
Proof.
  intros Hd. split.
  - intros k j r1 r2 Hne Hk Hj.
    apply (Hd k j r1 r2 Hne);
      rewrite lookup_app_l //;
      [ apply (lookup_lt_Some _ _ _ Hk) | apply (lookup_lt_Some _ _ _ Hj) ].
  - intros k j r1 r2 Hne Hk Hj.
    apply (Hd (length l1 + k)%nat (length l1 + j)%nat r1 r2 ltac:(lia));
      rewrite lookup_app_r; try lia;
      rewrite Nat.add_comm Nat.add_sub //.
Qed.

Lemma xr_union_app (l1 l2 : list xrun) :
  xr_union (l1 ++ l2) = xr_union l1 ∪ xr_union l2.
Proof.
  induction l1 as [| r l1 IH]; simpl.
  - rewrite xr_union_nil left_id_L //.
  - rewrite !xr_union_cons IH assoc_L //.
Qed.

(* ====================================================================== *)
(*  2.  THE RUNS AT A VIEW, AND THE FLAT MAP                               *)
(* ====================================================================== *)

Section Runs.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  Definition phi_map Γ (M : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ M, fsΦ Γ (DfracOwn 1) a v)%I.

  Definition phi_runs Γ (l : list xrun) : iProp Σ :=
    ([∗ list] r ∈ l, byte_range Γ (xr_blk r) (xr_off r) (xr_bs r))%I.

  Lemma phi_map_of_range Γ (r : xrun) :
    byte_range Γ (xr_blk r) (xr_off r) (xr_bs r) ⊣⊢ phi_map Γ (xr_map r).
  Proof.
    rewrite /phi_map /xr_map big_sepM_map_seqZ_gen /byte_range /byte_range_q //.
  Qed.

  Lemma phi_runs_nil Γ : phi_runs Γ [] ⊣⊢ emp.
  Proof. rewrite /phi_runs big_sepL_nil //. Qed.

  Lemma phi_runs_cons Γ r l :
    phi_runs Γ (r :: l) ⊣⊢ phi_map Γ (xr_map r) ∗ phi_runs Γ l.
  Proof. rewrite /phi_runs big_sepL_cons phi_map_of_range //. Qed.

  Lemma phi_runs_app Γ l1 l2 :
    phi_runs Γ (l1 ++ l2) ⊣⊢ phi_runs Γ l1 ∗ phi_runs Γ l2.
  Proof. rewrite /phi_runs big_sepL_app //. Qed.

  (* ---------------------------------------------------------------- *)
  (*  2a.  DISJOINTNESS IS READ OFF EXCLUSIVITY                        *)
  (* ---------------------------------------------------------------- *)

  Lemma phi_map_disj Γ (Hex : phi_excl Γ) M1 M2 :
    phi_map Γ M1 -∗ phi_map Γ M2 -∗ ⌜M1 ##ₘ M2⌝.
  Proof.
    revert M2. induction M1 as [| a v M1 Ha IH] using map_ind; intros M2.
    - iIntros "_ _". iPureIntro. apply map_disjoint_empty_l.
    - rewrite /phi_map big_sepM_insert; [| exact Ha].
      iIntros "[Hav HM1] HM2".
      destruct (M2 !! a) as [w |] eqn:Hw.
      { iDestruct (big_sepM_lookup _ _ a w Hw with "HM2") as "Haw".
        iDestruct (Hex a v w (DfracOwn 1) (DfracOwn 1) with "[$Hav $Haw]")
          as %Hv.
        exfalso. exact (dfrac_full_nvalid (DfracOwn 1) Hv). }
      iDestruct (IH M2 with "HM1 HM2") as %Hd.
      iPureIntro. apply map_disjoint_insert_l. split; [exact Hw | exact Hd].
  Qed.

  Lemma phi_runs_disj Γ (Hex : phi_excl Γ) l :
    phi_runs Γ l -∗ ⌜xr_disj l⌝.
  Proof.
    induction l as [| r l IH].
    - iIntros "_". iPureIntro.
      intros k j r1 r2 _ Hk. rewrite lookup_nil in Hk. discriminate.
    - rewrite phi_runs_cons. iIntros "[Hr Hl]".
      iAssert (⌜xr_disj l⌝ ∧ phi_runs Γ l)%I with "[Hl]" as "[%Hdl Hl]".
      { iSplit; [iApply (IH with "Hl") | iExact "Hl"]. }
      iAssert (⌜forall j r2, l !! j = Some r2 -> xr_map r ##ₘ xr_map r2⌝)%I
        with "[Hr Hl]" as %Hhd.
      { iIntros (j r2 Hj).
        rewrite /phi_runs (big_sepL_lookup _ _ j r2 Hj) phi_map_of_range.
        iApply (phi_map_disj Γ Hex with "Hr Hl"). }
      iPureIntro. intros k j r1 r2 Hne Hk Hj.
      destruct k as [| k]; destruct j as [| j]; [lia | | |].
      + simpl in Hk. injection Hk as <-. exact (Hhd j r2 Hj).
      + simpl in Hj. injection Hj as <-.
        apply map_disjoint_sym. exact (Hhd k r1 Hk).
      + exact (Hdl k j r1 r2 ltac:(lia) Hk Hj).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2b.  THE FLATTENING, BOTH WAYS                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma phi_runs_union Γ l :
    xr_disj l -> phi_runs Γ l ⊣⊢ phi_map Γ (xr_union l).
  Proof.
    induction l as [| r l IH]; intros Hd.
    - rewrite phi_runs_nil xr_union_nil /phi_map big_sepM_empty //.
    - destruct (xr_disj_cons r l Hd) as [Hdl _].
      rewrite phi_runs_cons (IH Hdl) xr_union_cons /phi_map.
      rewrite big_sepM_union; [done | exact (xr_disj_head r l Hd)].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2c.  THE SOURCE'S OWN AUTHORITY, AND THE OUTPUT'S IDENTITY       *)
  (*                                                                   *)
  (*  (durable-disk lane H3.)  The transport MINTS its fresh map at the *)
  (*  flattening of the SOURCE's runs, so whatever the source's own     *)
  (*  authority says about those bytes is inherited by the output --    *)
  (*  and that inheritance is the whole of the snapshot's IDENTITY      *)
  (*  ([FsDurRead.snap_auth]).  [phi_agree] is the source authority as  *)
  (*  a HYPOTHESIS, stated exactly as [FsStateDefs.phi_excl] is: the    *)
  (*  era's instance satisfies it at its byte authority                 *)
  (*  ([FsBytesGamma.fs_gamma_L], one [ghost_map_lookup]) and the       *)
  (*  snapshot's at its own.  Nothing is computed and no value is       *)
  (*  decoded: the output map is a SUBSET of the source's map, which is *)
  (*  what every byte tie is later read through.                       *)
  (* ---------------------------------------------------------------- *)

  Definition phi_agree Γ (A : iProp Σ) (M : gmap Z (bv 8)) : Prop :=
    forall (dq : dfrac) (a : Z) (v : bv 8),
      (A ∗ fsΦ Γ dq a v) ⊢ ⌜M !! a = Some v⌝.

  Lemma phi_map_in Γ (A : iProp Σ) (M : gmap Z (bv 8))
      (Hag : phi_agree Γ A M) (N : gmap Z (bv 8)) :
    A -∗ phi_map Γ N -∗ ⌜N ⊆ M⌝.
  Proof.
    iIntros "HA HN". rewrite /phi_map.
    iAssert (⌜forall (a : Z) (v : bv 8), N !! a = Some v ->
               M !! a = Some v⌝)%I with "[HA HN]" as %Hpt.
    { rewrite bi.pure_forall. iIntros (a).
      rewrite bi.pure_forall. iIntros (v).
      rewrite bi.pure_impl. iIntros (Ha).
      iDestruct (big_sepM_lookup _ _ a v Ha with "HN") as "Hav".
      iApply (Hag (DfracOwn 1) a v with "[$HA $Hav]"). }
    iPureIntro. by apply map_subseteq_spec.
  Qed.

  Lemma phi_runs_in Γ (A : iProp Σ) (M : gmap Z (bv 8))
      (Hag : phi_agree Γ A M) (l : list xrun) :
    xr_disj l -> A -∗ phi_runs Γ l -∗ ⌜xr_union l ⊆ M⌝.
  Proof.
    intros Hd. rewrite (phi_runs_union Γ l Hd).
    iApply (phi_map_in Γ A M Hag).
  Qed.

End Runs.

(* ====================================================================== *)
(*  2d.  THE RUNS AT MIXED SHARES (durable-disk lane H4)                   *)
(*                                                                        *)
(*  WHAT THE COMMIT'S SOURCE ACTUALLY LOOKS LIKE.  Quiescence does not     *)
(*  hand the commit an [fs_state] at [DfracOwn 1]: a READ-LOCKED inode has *)
(*  given a quarter to its reader and its escrow keeps three quarters      *)
(*  (plan section 4), so each inode's data legs arrive at a share of ITS   *)
(*  OWN, existentially bound, constrained only by "the double is invalid"  *)
(*  ([FsCollect.col_bundle]).  Its RECORD, on the other hand, is always at *)
(*  fraction 1 -- records park region-side and no lock splits them.        *)
(*                                                                        *)
(*  So a run list carries a share PER RUN.  Everything the transport reads *)
(*  off such a list is PURE -- the runs are pairwise disjoint, and their   *)
(*  union sits inside the source's own authority -- and both readings are  *)
(*  share-generic for the same one-line reason: two shares whose doubles   *)
(*  are invalid do not fit inside one byte ([dfrac_nvalid_pair], section   *)
(*  0), and [FsStateDefs.phi_excl] is fraction-aware.                      *)
(*                                                                        *)
(*  THE FULL-SHARE MACHINERY IS NOT DUPLICATED.  [xq_at dq l] is the       *)
(*  one-share list, and [phi_runs_q Γ (xq_at dq l)] IS [phi_runs] at the   *)
(*  CONSTANT-SHARE VIEW [gamma_q Γ dq] -- a [Γ] whose [fsΦ] ignores the    *)
(*  dfrac it is handed and always uses [dq].  Every Γ-generic shape        *)
(*  ([byte_range], [blk_owned], [ind_owned], [inode_phi], the whole runs   *)
(*  correspondence of section 3) therefore reads at a share with no new    *)
(*  lemma at all.                                                         *)
(* ====================================================================== *)

Definition xqrun : Type := (dfrac * xrun)%type.

Definition xq_at (dq : dfrac) (l : list xrun) : list xqrun := pair dq <$> l.

Definition xq_strip (l : list xqrun) : list xrun := snd <$> l.

(* the ONE constraint the collection's shares satisfy *)
Definition xq_ok (l : list xqrun) : Prop :=
  forall (k : nat) (r : xqrun), l !! k = Some r -> ~ ✓ (r.1 ⋅ r.1).

Lemma xq_strip_at (dq : dfrac) (l : list xrun) : xq_strip (xq_at dq l) = l.
Proof.
  rewrite /xq_strip /xq_at -list_fmap_compose.
  rewrite (list_fmap_ext (snd ∘ pair dq) id l); [| done].
  apply list_fmap_id.
Qed.

Lemma xq_strip_cons (r : xqrun) (l : list xqrun) :
  xq_strip (r :: l) = r.2 :: xq_strip l.
Proof. reflexivity. Qed.

Lemma xq_strip_app (l1 l2 : list xqrun) :
  xq_strip (l1 ++ l2) = xq_strip l1 ++ xq_strip l2.
Proof. rewrite /xq_strip fmap_app //. Qed.

Lemma xq_ok_cons (r : xqrun) (l : list xqrun) :
  ~ ✓ (r.1 ⋅ r.1) -> xq_ok l -> xq_ok (r :: l).
Proof.
  intros Hr Hl k x Hk. destruct k as [| k].
  - simpl in Hk. injection Hk as <-. exact Hr.
  - exact (Hl k x Hk).
Qed.

Lemma xq_ok_app (l1 l2 : list xqrun) :
  xq_ok l1 -> xq_ok l2 -> xq_ok (l1 ++ l2).
Proof.
  intros H1 H2 k x Hk.
  destruct (decide (k < length l1)%nat) as [Hlt | Hge].
  - rewrite lookup_app_l in Hk; [| exact Hlt]. exact (H1 k x Hk).
  - rewrite lookup_app_r in Hk; [| lia]. exact (H2 _ x Hk).
Qed.

Lemma xq_ok_at (dq : dfrac) (l : list xrun) :
  ~ ✓ (dq ⋅ dq) -> xq_ok (xq_at dq l).
Proof.
  intros Hdq k x Hk. rewrite /xq_at list_lookup_fmap in Hk.
  apply fmap_Some in Hk as (r & Hr & ->). exact Hdq.
Qed.

Section RunsQ.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  (* [gamma_q] AND ITS FOUR READINGS MOVED DOWN AT EV-X: the constant-share
     view is what [FsState.fs_state]'s dfrac argument is written at, so it
     lives in [FsStateDefs] now ([gamma_q], [gamma_q_byte_range],
     [gamma_q_blk_owned]) and its inode-shaped readings in [FsStateInode]
     ([gamma_q_ind_owned], [gamma_q_inode_dat], [gamma_q_inode_phi],
     [gamma_q_inode_ghost]). *)

  Definition phi_map_q Γ (dq : dfrac) (M : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ M, fsΦ Γ dq a v)%I.

  Definition phi_runs_q Γ (l : list xqrun) : iProp Σ :=
    ([∗ list] r ∈ l,
       byte_range_q Γ r.1 (xr_blk r.2) (xr_off r.2) (xr_bs r.2))%I.

  Lemma phi_map_q_of_range Γ dq (r : xrun) :
    byte_range_q Γ dq (xr_blk r) (xr_off r) (xr_bs r)
    ⊣⊢ phi_map_q Γ dq (xr_map r).
  Proof.
    rewrite /phi_map_q /xr_map big_sepM_map_seqZ_gen /byte_range_q //.
  Qed.

  Lemma phi_runs_q_nil Γ : phi_runs_q Γ [] ⊣⊢ emp.
  Proof. rewrite /phi_runs_q big_sepL_nil //. Qed.

  Lemma phi_runs_q_cons Γ r l :
    phi_runs_q Γ (r :: l)
    ⊣⊢ byte_range_q Γ r.1 (xr_blk r.2) (xr_off r.2) (xr_bs r.2)
        ∗ phi_runs_q Γ l.
  Proof. rewrite /phi_runs_q big_sepL_cons //. Qed.

  Lemma phi_runs_q_app Γ l1 l2 :
    phi_runs_q Γ (l1 ++ l2) ⊣⊢ phi_runs_q Γ l1 ∗ phi_runs_q Γ l2.
  Proof. rewrite /phi_runs_q big_sepL_app //. Qed.

  (* THE ONE-SHARE LIST IS THE CONSTANT-SHARE VIEW'S OWN RUN LIST. *)
  Lemma phi_runs_q_at Γ dq l :
    phi_runs_q Γ (xq_at dq l) ⊣⊢ phi_runs (gamma_q Γ dq) l.
  Proof.
    rewrite /phi_runs_q /xq_at big_sepL_fmap /phi_runs.
    apply big_opL_proper. intros k r _.
    rewrite gamma_q_byte_range //.
  Qed.

  (* ---- the two PURE readings, share-generic ------------------------- *)

  Lemma phi_map_disj_q Γ (Hex : phi_excl Γ) (dq1 dq2 : dfrac) M1 M2 :
    ~ ✓ (dq1 ⋅ dq2) ->
    phi_map_q Γ dq1 M1 -∗ phi_map_q Γ dq2 M2 -∗ ⌜M1 ##ₘ M2⌝.
  Proof.
    intros Hnv. revert M2. induction M1 as [| a v M1 Ha IH] using map_ind;
      intros M2.
    - iIntros "_ _". iPureIntro. apply map_disjoint_empty_l.
    - rewrite /phi_map_q big_sepM_insert; [| exact Ha].
      iIntros "[Hav HM1] HM2".
      destruct (M2 !! a) as [w |] eqn:Hw.
      { iDestruct (big_sepM_lookup _ _ a w Hw with "HM2") as "Haw".
        iDestruct (Hex a v w dq1 dq2 with "[$Hav $Haw]") as %Hv.
        exfalso. exact (Hnv Hv). }
      iDestruct (IH M2 with "HM1 HM2") as %Hd.
      iPureIntro. apply map_disjoint_insert_l. split; [exact Hw | exact Hd].
  Qed.

  Lemma phi_runs_q_disj Γ (Hex : phi_excl Γ) l :
    xq_ok l -> phi_runs_q Γ l -∗ ⌜xr_disj (xq_strip l)⌝.
  Proof.
    induction l as [| r l IH]; intros Hok.
    - iIntros "_". iPureIntro.
      intros k j r1 r2 _ Hk. rewrite lookup_nil in Hk. discriminate.
    - assert (Hr : ~ ✓ (r.1 ⋅ r.1)) by exact (Hok 0%nat r eq_refl).
      assert (Hl : xq_ok l) by (intros k x Hk; exact (Hok (S k) x Hk)).
      rewrite phi_runs_q_cons. iIntros "[Hr Hl]".
      iAssert (⌜xr_disj (xq_strip l)⌝ ∧ phi_runs_q Γ l)%I
        with "[Hl]" as "[%Hdl Hl]".
      { iSplit; [iApply (IH Hl with "Hl") | iExact "Hl"]. }
      iAssert (⌜forall j r2, xq_strip l !! j = Some r2 ->
                 xr_map r.2 ##ₘ xr_map r2⌝)%I with "[Hr Hl]" as %Hhd.
      { iIntros (j r2 Hj).
        rewrite /xq_strip list_lookup_fmap in Hj.
        apply fmap_Some in Hj as (x & Hx & ->).
        rewrite /phi_runs_q (big_sepL_lookup _ _ j x Hx).
        rewrite !phi_map_q_of_range.
        iApply (phi_map_disj_q Γ Hex r.1 x.1 _ _
                  (dfrac_nvalid_pair r.1 x.1 Hr (Hl j x Hx)) with "Hr Hl"). }
      iPureIntro. rewrite xq_strip_cons.
      intros k j r1 r2 Hne Hk Hj.
      destruct k as [| k]; destruct j as [| j]; [lia | | |].
      + simpl in Hk. injection Hk as <-. exact (Hhd j r2 Hj).
      + simpl in Hj. injection Hj as <-.
        apply map_disjoint_sym. exact (Hhd k r1 Hk).
      + exact (Hdl k j r1 r2 ltac:(lia) Hk Hj).
  Qed.

  Lemma phi_map_q_in Γ (A : iProp Σ) (M : gmap Z (bv 8))
      (Hag : phi_agree Γ A M) (dq : dfrac) (N : gmap Z (bv 8)) :
    A -∗ phi_map_q Γ dq N -∗ ⌜N ⊆ M⌝.
  Proof.
    iIntros "HA HN". rewrite /phi_map_q.
    iAssert (⌜forall (a : Z) (v : bv 8), N !! a = Some v ->
               M !! a = Some v⌝)%I with "[HA HN]" as %Hpt.
    { rewrite bi.pure_forall. iIntros (a).
      rewrite bi.pure_forall. iIntros (v).
      rewrite bi.pure_impl. iIntros (Ha).
      iDestruct (big_sepM_lookup _ _ a v Ha with "HN") as "Hav".
      iApply (Hag dq a v with "[$HA $Hav]"). }
    iPureIntro. by apply map_subseteq_spec.
  Qed.

  (* ...POINTWISE, so no disjointness is needed on the way in: a union of
     submaps of [M] is a submap of [M]. *)
  Lemma phi_runs_q_in Γ (A : iProp Σ) (M : gmap Z (bv 8))
      (Hag : phi_agree Γ A M) (l : list xqrun) :
    A -∗ phi_runs_q Γ l -∗ ⌜xr_union (xq_strip l) ⊆ M⌝.
  Proof.
    induction l as [| r l IH].
    - iIntros "_ _". iPureIntro. rewrite /xq_strip /= xr_union_nil.
      apply map_empty_subseteq.
    - rewrite phi_runs_q_cons. iIntros "HA [Hr Hl]".
      iAssert (⌜xr_map r.2 ⊆ M⌝ ∧ A)%I with "[HA Hr]" as "[%H1 HA]".
      { iSplit; [| iExact "HA"].
        rewrite phi_map_q_of_range.
        iApply (phi_map_q_in Γ A M Hag r.1 with "HA Hr"). }
      iDestruct (IH with "HA Hl") as %H2.
      iPureIntro. rewrite xq_strip_cons xr_union_cons.
      apply map_union_least; [exact H1 | exact H2].
  Qed.

  (* ---- the CONCATENATION, with the shares existentially bound -------- *)

  (* The shape the collection produces: one object at a time, each at a
     share of its own, and the list is built as the walk goes.  Stating the
     share existentially PER OBJECT is what avoids a choice function over
     the inode map. *)
  Definition phi_runs_ex Γ (F : list xrun) : iProp Σ :=
    (∃ l : list xqrun,
       ⌜xq_strip l = F⌝ ∗ ⌜xq_ok l⌝ ∗ phi_runs_q Γ l)%I.

  Lemma phi_runs_ex_at Γ dq F :
    ~ ✓ (dq ⋅ dq) -> phi_runs (gamma_q Γ dq) F ⊢ phi_runs_ex Γ F.
  Proof.
    intros Hdq. iIntros "H". iExists (xq_at dq F).
    iSplitR; [iPureIntro; exact (xq_strip_at dq F) |].
    iSplitR; [iPureIntro; exact (xq_ok_at dq F Hdq) |].
    rewrite phi_runs_q_at. iExact "H".
  Qed.

  Lemma gamma_q_1_runs Γ l :
    phi_runs (gamma_q Γ (DfracOwn 1)) l ⊣⊢ phi_runs Γ l.
  Proof.
    rewrite /phi_runs. apply big_opL_proper. intros k r _.
    rewrite gamma_q_byte_range -byte_range_1 //.
  Qed.

  Lemma phi_runs_ex_full Γ l : phi_runs Γ l ⊢ phi_runs_ex Γ l.
  Proof.
    iIntros "H". iExists (xq_at (DfracOwn 1) l).
    iSplitR; [iPureIntro; exact (xq_strip_at (DfracOwn 1) l) |].
    iSplitR;
      [iPureIntro;
       exact (xq_ok_at (DfracOwn 1) l (dfrac_full_nvalid (DfracOwn 1))) |].
    rewrite phi_runs_q_at gamma_q_1_runs. iExact "H".
  Qed.

  Lemma phi_runs_ex_app Γ F1 F2 :
    phi_runs_ex Γ F1 ∗ phi_runs_ex Γ F2 ⊢ phi_runs_ex Γ (F1 ++ F2).
  Proof.
    iIntros "[H1 H2]".
    iDestruct "H1" as (l1 Hs1 Hk1) "H1".
    iDestruct "H2" as (l2 Hs2 Hk2) "H2".
    iExists (l1 ++ l2).
    iSplitR; [iPureIntro; rewrite xq_strip_app Hs1 Hs2 // |].
    iSplitR; [iPureIntro; exact (xq_ok_app l1 l2 Hk1 Hk2) |].
    rewrite phi_runs_q_app. iFrame.
  Qed.

  Lemma phi_runs_ex_cons Γ (dq : dfrac) (r : xrun) F :
    ~ ✓ (dq ⋅ dq) ->
    byte_range_q Γ dq (xr_blk r) (xr_off r) (xr_bs r) ∗ phi_runs_ex Γ F
    ⊢ phi_runs_ex Γ (r :: F).
  Proof.
    intros Hdq. iIntros "[Hr H]". iDestruct "H" as (l Hs Hk) "H".
    iExists ((dq, r) :: l).
    iSplitR; [iPureIntro; rewrite xq_strip_cons Hs // |].
    iSplitR; [iPureIntro; exact (xq_ok_cons (dq, r) l Hdq Hk) |].
    rewrite phi_runs_q_cons. iFrame.
  Qed.

  Lemma phi_runs_ex_concat {A : Type} Γ (xs : list A)
      (F : A -> list xrun) (Ψ : A -> iProp Σ) :
    (forall x, Ψ x ⊢ phi_runs_ex Γ (F x)) ->
    ([∗ list] x ∈ xs, Ψ x) ⊢ phi_runs_ex Γ (concat (F <$> xs)).
  Proof.
    intros Hone. induction xs as [| x xs IH].
    - iIntros "_". iExists []. rewrite phi_runs_q_nil.
      iSplitR; [by iPureIntro |]. iSplitR; [| done].
      iPureIntro. intros k r Hk. rewrite lookup_nil in Hk. discriminate.
    - assert (Hc : concat (F <$> (x :: xs)) = F x ++ concat (F <$> xs))
        by reflexivity.
      rewrite Hc big_sepL_cons. iIntros "[Hx Hxs]".
      iApply phi_runs_ex_app. iSplitL "Hx".
      + iApply (Hone x with "Hx").
      + iApply (IH with "Hxs").
  Qed.

  (* ...and what the transport reads off the whole of it. *)
  Lemma phi_runs_ex_disj Γ (Hex : phi_excl Γ) F :
    phi_runs_ex Γ F -∗ ⌜xr_disj F⌝.
  Proof.
    iIntros "H". iDestruct "H" as (l Hs Hk) "H".
    iDestruct (phi_runs_q_disj Γ Hex l Hk with "H") as %Hd.
    iPureIntro. rewrite -Hs. exact Hd.
  Qed.

  Lemma phi_runs_ex_in Γ (A : iProp Σ) (M : gmap Z (bv 8))
      (Hag : phi_agree Γ A M) F :
    A -∗ phi_runs_ex Γ F -∗ ⌜xr_union F ⊆ M⌝.
  Proof.
    iIntros "HA H". iDestruct "H" as (l Hs Hk) "H".
    iDestruct (phi_runs_q_in Γ A M Hag l with "HA H") as %Hin.
    iPureIntro. rewrite -Hs. exact Hin.
  Qed.

End RunsQ.

(* ====================================================================== *)
(*  3.  THE FILE SYSTEM'S OWN RUNS                                         *)
(*                                                                        *)
(*  [FsState.fs_footprint] IS a [∗] of byte runs -- one per object -- and  *)
(*  [xr_fs] names them.  The correspondence is Gamma-GENERIC and needs no  *)
(*  disjointness in either direction: it is the SHAPE of the predicate,    *)
(*  not a fact about it.  Its only side conditions are block LENGTHS and   *)
(*  the free pool's domain, and both are read off the source's own         *)
(*  resources ([fs_footprint_runs] produces them).                         *)
(* ====================================================================== *)

Definition xr_rec (sb : fs_sb) (i : Z) (n : fs_node) : xrun :=
  ((IBLOCK (fs_inum_bv i) (sb_inodestart sb),
    Z.of_nat (64 * islot (fs_inum_bv i))), dinode_bytes (fn_rec n)).

Definition xr_dat (n : fs_node) (p : nat * list (bv 8)) : xrun :=
  ((fn_naddr n p.1, 0), p.2).

Definition xr_ind (n : fs_node) : list xrun :=
  if decide (fn_indb n = 0) then []
  else [((fn_indb n, 0), ind_bytes (fn_ent n))].

(* AN INODE'S RUNS APART FROM ITS RECORD'S (durable-disk lane H4).  The
   split is not cosmetic: at a commit the record and the data blocks come
   from DIFFERENT places at DIFFERENT shares -- the record region-side at
   fraction 1, the data legs out of the inode's own bundle at a share of
   its own (plan section 4) -- so the two halves are read separately. *)
Definition xr_dats (n : fs_node) : list xrun :=
  (xr_dat n <$> map_to_list (fn_blk n)) ++ xr_ind n.

Definition xr_inode (sb : fs_sb) (i : Z) (n : fs_node) : list xrun :=
  xr_rec sb i n :: xr_dats n.

Definition xr_inodes (sb : fs_sb) (I : gmap Z fs_node) : list xrun :=
  concat ((fun p : Z * fs_node => xr_inode sb p.1 p.2) <$> map_to_list I).

Definition xr_pool (PM : gmap Z (list (bv 8))) : list xrun :=
  (fun p : Z * list (bv 8) => ((p.1, 0), p.2)) <$> map_to_list PM.

Definition xr_fs (S : fs_state_rec) (PM : gmap Z (list (bv 8))) : list xrun :=
  ((SB_BNO, 0), fss_sbb S)
  :: ((sb_bmapstart (fss_sb S), 0), bm_bytes BSIZE (fss_used S))
  :: (xr_inodes (fss_sb S) (fss_inodes S) ++ xr_pool PM).

(* the LENGTHS one node's runs carry, and the free pool's domain: what the
   [blk_owned] shape states and a [byte_range] does not *)
Definition node_lens (n : fs_node) : Prop :=
  (forall k bs, fn_blk n !! k = Some bs -> length bs = BSIZE)
  /\ (fn_indb n <> 0 -> length (ind_bytes (fn_ent n)) = BSIZE).

Definition pool_pm (l : list Z) (u : gset Z) (PM : gmap Z (list (bv 8)))
  : Prop :=
  (forall b, is_Some (PM !! b) <-> (b ∈ l /\ b ∉ u))
  /\ (forall b bs, PM !! b = Some bs -> length bs = BSIZE).

Definition xf_shape (S : fs_state_rec) (PM : gmap Z (list (bv 8))) : Prop :=
  length (fss_sbb S) = BSIZE
  /\ (forall i n, fss_inodes S !! i = Some n -> node_lens n)
  /\ pool_pm (seqZ 0 (sb_size (fss_sb S))) (fss_used S) PM.

Section FsRuns.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  (* ---------------------------------------------------------------- *)
  (*  3a.  ONE INODE                                                   *)
  (* ---------------------------------------------------------------- *)

  (* THE RECORD'S RUN IS THE RECORD ITSELF: [xr_rec] names exactly
     [FsStateInode.rec_owned]'s block, offset and bytes. *)
  Lemma rec_owned_run Γ (sb : fs_sb) (i : Z) (n : fs_node) :
    rec_owned Γ sb i (fn_rec n) ⊣⊢ phi_runs Γ [xr_rec sb i n].
  Proof.
    rewrite /phi_runs big_sepL_singleton
            /rec_owned /xr_rec /xr_blk /xr_off /xr_bs //=.
  Qed.

  (* ...AND THE DATA HALF ON ITS OWN (durable-disk lane H4): the runs of
     everything an inode owns but its record.  This is the half a commit
     reads out of the inode's BUNDLE, at the bundle's own share. *)
  Lemma inode_dats_runs Γ (n : fs_node) :
    (([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
     ∗ ind_owned Γ n)
    ⊢ ⌜node_lens n⌝ ∗ phi_runs Γ (xr_dats n).
  Proof.
    rewrite /xr_dats phi_runs_app. iIntros "(Hd & Hi)".
    iAssert (⌜forall k bs, fn_blk n !! k = Some bs -> length bs = BSIZE⌝)%I
      with "[Hd]" as %Hlen.
    { iIntros (k bs Hk).
      rewrite (big_sepM_lookup _ _ k bs Hk) /blk_owned.
      iDestruct "Hd" as "[$ _]". }
    iAssert (⌜fn_indb n <> 0 -> length (ind_bytes (fn_ent n)) = BSIZE⌝)%I
      with "[Hi]" as %Hind.
    { iIntros (Hnz). rewrite /ind_owned (decide_False _ _ Hnz) /blk_owned.
      iDestruct "Hi" as "[$ _]". }
    iSplitR; [iPureIntro; split; [exact Hlen | exact Hind] |].
    iSplitL "Hd".
    - iEval (rewrite big_sepM_map_to_list) in "Hd".
      rewrite /phi_runs big_sepL_fmap.
      iApply (big_sepL_mono with "Hd"). intros k p _.
      rewrite /blk_owned /xr_dat /xr_blk /xr_off /xr_bs /=. iIntros "[_ $]".
    - rewrite /xr_ind /ind_owned. case_decide as Hz.
      + rewrite phi_runs_nil //.
      + rewrite /phi_runs big_sepL_singleton /blk_owned /=.
        iDestruct "Hi" as "[_ $]".
  Qed.

  Lemma inode_dats_of_runs Γ (n : fs_node) :
    node_lens n ->
    phi_runs Γ (xr_dats n)
    ⊢ ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
      ∗ ind_owned Γ n.
  Proof.
    intros [Hlen Hind]. rewrite /xr_dats phi_runs_app.
    iIntros "(Hd & Hi)". iSplitL "Hd".
    - rewrite big_sepM_map_to_list.
      rewrite /phi_runs big_sepL_fmap.
      iApply (big_sepL_mono with "Hd"). intros k p Hp.
      rewrite /blk_owned /xr_dat /xr_blk /xr_off /xr_bs /=. iIntros "$".
      iPureIntro. apply (Hlen p.1 p.2).
      apply elem_of_map_to_list. rewrite -surjective_pairing.
      exact (elem_of_list_lookup_2 _ _ _ Hp).
    - rewrite /xr_ind /ind_owned. case_decide as Hz; [done |].
      rewrite /phi_runs big_sepL_singleton /blk_owned /=.
      iFrame "Hi". iPureIntro. exact (Hind Hz).
  Qed.

  Lemma inode_phi_runs Γ (sb : fs_sb) (i : Z) (n : fs_node) :
    inode_phi Γ sb i n ⊢ ⌜node_lens n⌝ ∗ phi_runs Γ (xr_inode sb i n).
  Proof.
    rewrite /inode_phi /xr_inode phi_runs_cons.
    iIntros "(Hr & Hd & Hi)".
    iDestruct (inode_dats_runs Γ n with "[$Hd $Hi]") as "[%Hlens Hdats]".
    iSplitR; [by iPureIntro |]. iSplitR "Hdats"; [| iExact "Hdats"].
    rewrite -phi_map_of_range /rec_owned /xr_rec //=.
  Qed.

  Lemma inode_phi_of_runs Γ (sb : fs_sb) (i : Z) (n : fs_node) :
    node_lens n -> phi_runs Γ (xr_inode sb i n) ⊢ inode_phi Γ sb i n.
  Proof.
    intros Hlens. rewrite /inode_phi /xr_inode phi_runs_cons.
    iIntros "(Hr & Hdats)".
    iDestruct (inode_dats_of_runs Γ n Hlens with "Hdats") as "[Hd Hi]".
    iFrame "Hd Hi". rewrite -phi_map_of_range /rec_owned /xr_rec //=.
  Qed.



  (* ---------------------------------------------------------------- *)
  (*  3a'. ONE INODE AT THE HOLDER'S OWN SHARE (durable-disk EV        *)
  (*       stage 5)                                                    *)
  (*                                                                   *)
  (*  [FsState.fs_footprint_q]'s inode column, as runs.  The RECORD    *)
  (*  rides at fraction 1 and the data legs at the bundle's own share,  *)
  (*  which is exactly what [phi_runs_ex] is for: a share per RUN,      *)
  (*  existentially bound, so no choice function over the inode map is  *)
  (*  needed.  The share-generic reading of the data half is free --    *)
  (*  [gamma_q Γ dq]'s [fsΦ] ignores the dfrac it is handed, so         *)
  (*  [inode_dat] AT that view IS [inode_dat_q Γ dq].                   *)
  (* ---------------------------------------------------------------- *)

  Lemma inode_phi_q_runs Γ dq (sb : fs_sb) (i : Z) (n : fs_node) :
    ~ ✓ (dq ⋅ dq) ->
    inode_phi_q Γ dq sb i n
    ⊢ ⌜node_lens n⌝ ∗ phi_runs_ex Γ (xr_inode sb i n).
  Proof.
    intros Hdq. rewrite /inode_phi_q -gamma_q_inode_dat /inode_dat.
    iIntros "[Hr Hd]".
    iDestruct (inode_dats_runs (gamma_q Γ dq) n with "Hd") as "[%Hlens Hdats]".
    iSplitR; [by iPureIntro |].
    iApply (phi_runs_ex_app Γ [xr_rec sb i n] (xr_dats n)).
    iSplitL "Hr".
    - iApply phi_runs_ex_full. rewrite -(rec_owned_run Γ sb i n). iExact "Hr".
    - iApply (phi_runs_ex_at Γ dq (xr_dats n) Hdq with "Hdats").
  Qed.

  Lemma fs_inodes_phi_q_runs Γ (sb : fs_sb) (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I,
       ∃ dq : dfrac, ⌜~ ✓ (dq ⋅ dq)⌝ ∗ inode_phi_q Γ dq sb i n)
    ⊢ ⌜forall i n, I !! i = Some n -> node_lens n⌝
      ∗ phi_runs_ex Γ (xr_inodes sb I).
  Proof.
    iIntros "H".
    iAssert (⌜forall i n, I !! i = Some n -> node_lens n⌝)%I
      with "[H]" as %Hlens.
    { iIntros (i n Hi). rewrite (big_sepM_lookup _ _ i n Hi).
      iDestruct "H" as (dq Hdq) "H".
      iDestruct (inode_phi_q_runs Γ dq sb i n Hdq with "H") as "[$ _]". }
    iSplitR; [by iPureIntro |].
    rewrite big_sepM_map_to_list /xr_inodes.
    iApply (phi_runs_ex_concat Γ (map_to_list I)
              (fun p : Z * fs_node => xr_inode sb p.1 p.2) _ _ with "H").
    Unshelve.
    intros p. iIntros "H". iDestruct "H" as (dq Hdq) "H".
    iDestruct (inode_phi_q_runs Γ dq sb p.1 p.2 Hdq with "H") as "[_ $]".
  Qed.


  (* ---------------------------------------------------------------- *)
  (*  3b.  EVERY INODE                                                 *)
  (* ---------------------------------------------------------------- *)

  Lemma phi_runs_concat Γ (ls : list (list xrun)) :
    phi_runs Γ (concat ls) ⊣⊢ [∗ list] l ∈ ls, phi_runs Γ l.
  Proof.
    induction ls as [| l ls IH].
    - rewrite /phi_runs //=.
    - assert (Hc : concat (l :: ls) = l ++ concat ls) by reflexivity.
      rewrite Hc phi_runs_app big_sepL_cons IH //.
  Qed.

  Lemma fs_inodes_phi_runs Γ (sb : fs_sb) (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I, inode_phi Γ sb i n)
    ⊢ ⌜forall i n, I !! i = Some n -> node_lens n⌝
      ∗ phi_runs Γ (xr_inodes sb I).
  Proof.
    iIntros "H".
    iAssert (⌜forall i n, I !! i = Some n -> node_lens n⌝)%I
      with "[H]" as %Hlens.
    { iIntros (i n Hi). rewrite (big_sepM_lookup _ _ i n Hi).
      iDestruct (inode_phi_runs with "H") as "[$ _]". }
    iSplitR; [by iPureIntro |].
    rewrite big_sepM_map_to_list.
    rewrite /xr_inodes phi_runs_concat big_sepL_fmap.
    iApply (big_sepL_mono with "H"). intros k p _. simpl.
    iIntros "H". iDestruct (inode_phi_runs with "H") as "[_ $]".
  Qed.

  Lemma fs_inodes_phi_of_runs Γ (sb : fs_sb) (I : gmap Z fs_node) :
    (forall i n, I !! i = Some n -> node_lens n) ->
    phi_runs Γ (xr_inodes sb I) ⊢ [∗ map] i ↦ n ∈ I, inode_phi Γ sb i n.
  Proof.
    intros Hlens.
    rewrite big_sepM_map_to_list.
    rewrite /xr_inodes phi_runs_concat big_sepL_fmap.
    iIntros "H". iApply (big_sepL_mono with "H"). intros k p Hp. simpl.
    iApply (inode_phi_of_runs Γ sb p.1 p.2).
    apply (Hlens p.1 p.2). apply elem_of_map_to_list.
    rewrite -surjective_pairing. exact (elem_of_list_lookup_2 _ _ _ Hp).
  Qed.

End FsRuns.

(* ====================================================================== *)
(*  3c.  THE FREE POOL                                                     *)
(*                                                                        *)
(*  [FsStateBitmap.free_pool] is a big-op over a RANGE whose free entries  *)
(*  hold EXISTENTIAL bytes.  The runs need those bytes named, so the walk  *)
(*  collects them into a map [PM] -- and the map is the SOURCE'S, read off *)
(*  its own resources, not a value anybody computes.                       *)
(* ====================================================================== *)

Section FsPool.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma free_pool_list_pm Γ (u : gset Z) (l : list Z) :
    base.NoDup l ->
    ([∗ list] b ∈ l, pool_elt Γ u b)
    ⊢ ∃ PM, ⌜pool_pm l u PM⌝ ∗ ([∗ map] b ↦ bs ∈ PM, blk_owned Γ b bs).
  Proof.
    induction l as [| b l IH]; intros Hnd.
    - iIntros "_". iExists ∅. rewrite big_sepM_empty. iSplitL; [| done].
      iPureIntro. split.
      + intros x. rewrite lookup_empty. split.
        * intros [? Hc]. discriminate.
        * intros [Hx _]. exfalso. eapply not_elem_of_nil. exact Hx.
      + intros x bs. rewrite lookup_empty. discriminate.
    - apply NoDup_cons in Hnd as [Hb Hnd].
      rewrite big_sepL_cons. iIntros "[Hb Hl]".
      iDestruct (IH Hnd with "Hl") as (PM) "[%Hpm HPM]".
      destruct Hpm as [Hdom Hlens].
      rewrite /pool_elt. destruct (bool_decide (b ∈ u)) eqn:Hbu.
      + apply bool_decide_eq_true in Hbu.
        iExists PM. iFrame "HPM". iPureIntro. split; [| exact Hlens].
        intros x. rewrite (Hdom x). split.
        * intros [Hx Hxu]. split; [apply elem_of_cons; by right | exact Hxu].
        * intros [Hx Hxu]. apply elem_of_cons in Hx as [-> | Hx];
            [contradiction | by split].
      + apply bool_decide_eq_false in Hbu.
        iDestruct "Hb" as (bs) "Hb".
        assert (HPMb : PM !! b = None).
        { destruct (PM !! b) as [c |] eqn:E; [| done].
          exfalso. destruct (proj1 (Hdom b) (mk_is_Some _ _ E)) as [Hin _].
          exact (Hb Hin). }
        iAssert (⌜length bs = BSIZE⌝)%I with "[Hb]" as %Hlen.
        { rewrite /blk_owned. iDestruct "Hb" as "[$ _]". }
        iExists (<[b := bs]> PM). iSplitR.
        * iPureIntro. split.
          -- intros x. destruct (decide (x = b)) as [-> | Hne].
             ++ rewrite lookup_insert. split.
                ** intros _. split; [apply elem_of_cons; by left | exact Hbu].
                ** intros _. by eexists.
             ++ rewrite lookup_insert_ne; [| done]. rewrite (Hdom x). split.
                ** intros [Hx Hxu]. split;
                     [apply elem_of_cons; by right | exact Hxu].
                ** intros [Hx Hxu]. apply elem_of_cons in Hx as [-> | Hx];
                     [contradiction | by split].
          -- intros x cs. destruct (decide (x = b)) as [-> | Hne].
             ++ rewrite lookup_insert. intros Hc. injection Hc as <-.
                exact Hlen.
             ++ rewrite lookup_insert_ne; [| done]. exact (Hlens x cs).
        * rewrite big_sepM_insert; [| exact HPMb]. iFrame.
  Qed.

  Lemma free_pool_list_of_pm Γ (u : gset Z) (l : list Z) PM :
    base.NoDup l -> pool_pm l u PM ->
    ([∗ map] b ↦ bs ∈ PM, blk_owned Γ b bs) ⊢ [∗ list] b ∈ l, pool_elt Γ u b.
  Proof.
    revert PM. induction l as [| b l IH]; intros PM Hnd [Hdom Hlens].
    - iIntros "_". rewrite big_sepL_nil //.
    - apply NoDup_cons in Hnd as [Hb Hnd].
      rewrite big_sepL_cons /pool_elt.
      destruct (bool_decide (b ∈ u)) eqn:Hbu.
      + apply bool_decide_eq_true in Hbu.
        iIntros "HPM". iSplitR; [done |].
        iApply (IH PM Hnd with "HPM"). split; [| exact Hlens].
        intros x. rewrite (Hdom x). split.
        * intros [Hx Hxu]. apply elem_of_cons in Hx as [-> | Hx];
            [contradiction | by split].
        * intros [Hx Hxu]. split; [apply elem_of_cons; by right | exact Hxu].
      + apply bool_decide_eq_false in Hbu.
        assert (Hsb : is_Some (PM !! b)).
        { apply (Hdom b). split; [apply elem_of_cons; by left | exact Hbu]. }
        destruct Hsb as [bs Hbs].
        rewrite (big_sepM_delete _ PM b bs Hbs).
        iIntros "[Hb HPM]". iSplitL "Hb"; [by iExists bs |].
        iApply (IH (delete b PM) Hnd with "HPM"). split.
        * intros x. destruct (decide (x = b)) as [-> | Hne].
          -- rewrite lookup_delete. split.
             ++ intros [? Hc]. discriminate.
             ++ intros [Hx _]. contradiction.
          -- rewrite lookup_delete_ne; [| done]. rewrite (Hdom x). split.
             ++ intros [Hx Hxu]. apply elem_of_cons in Hx as [-> | Hx];
                  [contradiction | by split].
             ++ intros [Hx Hxu]. split;
                  [apply elem_of_cons; by right | exact Hxu].
        * intros x cs Hx. apply lookup_delete_Some in Hx as [_ Hx].
          exact (Hlens x cs Hx).
  Qed.

  Lemma pool_pm_runs Γ PM :
    (forall b bs, PM !! b = Some bs -> length bs = BSIZE) ->
    ([∗ map] b ↦ bs ∈ PM, blk_owned Γ b bs) ⊣⊢ phi_runs Γ (xr_pool PM).
  Proof.
    intros Hlens.
    rewrite big_sepM_map_to_list /xr_pool /phi_runs big_sepL_fmap.
    apply big_sepL_proper. intros k p Hp.
    assert (Hin : PM !! p.1 = Some p.2).
    { apply elem_of_map_to_list. rewrite -surjective_pairing.
      exact (elem_of_list_lookup_2 _ _ _ Hp). }
    rewrite /blk_owned /xr_blk /xr_off /xr_bs /=.
    iSplit; [iIntros "[_ $]" | iIntros "$"; iPureIntro; exact (Hlens _ _ Hin)].
  Qed.

  Lemma free_pool_runs Γ (nb : Z) (u : gset Z) :
    free_pool Γ nb u
    ⊢ ∃ PM, ⌜pool_pm (seqZ 0 nb) u PM⌝ ∗ phi_runs Γ (xr_pool PM).
  Proof.
    rewrite /free_pool. iIntros "H".
    iDestruct (free_pool_list_pm Γ u (seqZ 0 nb) (NoDup_seqZ 0 nb) with "H")
      as (PM) "[%Hpm HPM]".
    iExists PM. iSplitR; [by iPureIntro |].
    rewrite -(pool_pm_runs Γ PM (proj2 Hpm)). iExact "HPM".
  Qed.

  Lemma free_pool_of_runs Γ (nb : Z) (u : gset Z) PM :
    pool_pm (seqZ 0 nb) u PM ->
    phi_runs Γ (xr_pool PM) ⊢ free_pool Γ nb u.
  Proof.
    intros Hpm. rewrite -(pool_pm_runs Γ PM (proj2 Hpm)) /free_pool.
    iApply (free_pool_list_of_pm Γ u (seqZ 0 nb) PM (NoDup_seqZ 0 nb) Hpm).
  Qed.

End FsPool.

(* ====================================================================== *)
(*  3d.  THE WHOLE BYTE HALF                                               *)
(* ====================================================================== *)

Section FsFoot.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma phi_runs_cons_range Γ r l :
    phi_runs Γ (r :: l)
    ⊣⊢ byte_range Γ (xr_blk r) (xr_off r) (xr_bs r) ∗ phi_runs Γ l.
  Proof. rewrite /phi_runs big_sepL_cons //. Qed.

  Lemma fs_footprint_runs Γ S :
    fs_footprint Γ (DfracOwn 1) S
    ⊢ ∃ PM, ⌜xf_shape S PM⌝ ∗ phi_runs Γ (xr_fs S PM).
  Proof.
    rewrite fs_footprint_1. iIntros "(Hsb & Hin & Hbm & Hpool)".
    iDestruct (fs_inodes_phi_runs with "Hin") as "[%Hlens Hin]".
    iDestruct (free_pool_runs with "Hpool") as (PM) "[%Hpm Hpool]".
    iAssert (⌜length (fss_sbb S) = BSIZE⌝)%I with "[Hsb]" as %Hsbl.
    { rewrite /blk_owned. iDestruct "Hsb" as "[$ _]". }
    iExists PM. iSplitR.
    { iPureIntro. split; [exact Hsbl | split; [exact Hlens | exact Hpm]]. }
    rewrite /xr_fs !phi_runs_cons_range phi_runs_app.
    rewrite /blk_owned /xr_blk /xr_off /xr_bs /=.
    iDestruct "Hsb" as "[_ Hsb]". iDestruct "Hbm" as "[_ Hbm]".
    iFrame.
  Qed.

  Lemma fs_footprint_of_runs Γ S PM :
    xf_shape S PM -> phi_runs Γ (xr_fs S PM) ⊢ fs_footprint Γ (DfracOwn 1) S.
  Proof.
    intros (Hsbl & Hlens & Hpm).
    rewrite /xr_fs !phi_runs_cons_range phi_runs_app.
    rewrite /xr_blk /xr_off /xr_bs /=.
    iIntros "(Hsb & Hbm & Hin & Hpool)".
    rewrite fs_footprint_1 /blk_owned.
    iSplitL "Hsb"; [by iFrame |].
    iSplitL "Hin"; [by iApply (fs_inodes_phi_of_runs Γ _ _ Hlens with "Hin") |].
    iSplitL "Hbm".
    { iFrame. iPureIntro. exact (bm_bytes_length BSIZE (fss_used S)). }
    iApply (free_pool_of_runs Γ _ _ PM Hpm with "Hpool").
  Qed.



  (* ...AND THE WHOLE FOOTPRINT AT QUIESCENCE'S SHARES (durable-disk EV
     stage 5).  [fs_footprint_runs]' twin, and the ONE step the commit's
     mint takes between the collection and [FsDurSnap.snap_mint]: the
     metadata objects at fraction 1, the inode column at a share per inode.
     The full-share instance factors through it by
     [FsState.fs_footprint_q_1], so nothing is duplicated. *)
  Lemma fs_footprint_q_runs Γ S :
    fs_footprint_q Γ S ⊢ ∃ PM, ⌜xf_shape S PM⌝ ∗ phi_runs_ex Γ (xr_fs S PM).
  Proof.
    rewrite /fs_footprint_q. iIntros "(Hsb & Hin & Hbm & Hpool)".
    iDestruct (fs_inodes_phi_q_runs with "Hin") as "[%Hlens Hin]".
    iDestruct (free_pool_runs with "Hpool") as (PM) "[%Hpm Hpool]".
    iAssert (⌜length (fss_sbb S) = BSIZE⌝)%I with "[Hsb]" as %Hsbl.
    { rewrite /blk_owned. iDestruct "Hsb" as "[$ _]". }
    iExists PM. iSplitR.
    { iPureIntro. split; [exact Hsbl | split; [exact Hlens | exact Hpm]]. }
    rewrite /xr_fs.
    iApply (phi_runs_ex_cons Γ (DfracOwn 1) ((SB_BNO, 0), fss_sbb S) _
              (dfrac_full_nvalid (DfracOwn 1))).
    rewrite /blk_owned /xr_blk /xr_off /xr_bs /=.
    iDestruct "Hsb" as "[_ Hsb]". iDestruct "Hbm" as "[_ Hbm]".
    iSplitL "Hsb"; [rewrite -byte_range_1; iExact "Hsb" |].
    iApply (phi_runs_ex_cons Γ (DfracOwn 1)
              ((sb_bmapstart (fss_sb S), 0), bm_bytes BSIZE (fss_used S)) _
              (dfrac_full_nvalid (DfracOwn 1))).
    rewrite /xr_blk /xr_off /xr_bs /=.
    iSplitL "Hbm"; [rewrite -byte_range_1; iExact "Hbm" |].
    iApply phi_runs_ex_app. iSplitL "Hin"; [iExact "Hin" |].
    iApply (phi_runs_ex_full with "Hpool").
  Qed.

End FsFoot.

(* ====================================================================== *)
(*  4.  THE TRANSPORT                                                      *)
(*                                                                        *)
(*  [fs_state Γ S] in, [fs_state Γ S ∗ fs_state Γ' S] out, over a FRESH    *)
(*  family [Γ'].  Three allocations and not one decode:                    *)
(*                                                                        *)
(*    - the BYTE map: [ghost_map_alloc] at the flattening of the source's  *)
(*      OWN runs.  The values are the source's; the fresh elements come    *)
(*      out already in the [∗] shape the source had, because the map they  *)
(*      are allocated at IS that [∗] flattened, and the flattening is a    *)
(*      bijection exactly where the source's own exclusivity says the      *)
(*      objects do not overlap ([phi_runs_disj]).  Nothing is carved and   *)
(*      no disjointness clause is stated, maintained or supplied.          *)
(*    - the LINK family: ONE [own_alloc] at the SOURCE'S own element,      *)
(*      read off its resources by [FsState.fs_links_valid].  The choice    *)
(*      function is the gather's, never a function of [S].                 *)
(*    - the TOP map: [ghost_map_alloc] at [fss_inodes S] -- the state      *)
(*      itself, which is the index of BOTH ends, so no value is decoded.   *)
(* ====================================================================== *)

Section Xfer.
  (* [diskImgG] is the tree's UNIQUE [ghost_mapG Σ Z (bv 8)]; a fresh
     family's byte map is a fresh gname at that same class. *)
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.

  (* [FsDurBytes.snap_gamma] is the durable family's record, and its byte
     authority IS the [phi_agree] the transport wants, by one
     [ghost_map_lookup].  So a snapshot is a legal SOURCE with its own
     identity in hand, which is what the boot mint needs.  This is the one
     fact about that record the TRANSPORT owns, which is why it stayed
     here when the record itself moved down. *)
  Lemma snap_gamma_agree (g gl gt : gname) (B : gmap Z (bv 8)) :
    phi_agree (snap_gamma g gl gt) (ghost_map_auth g 1 B) B.
  Proof.
    intros dq a v. rewrite /snap_gamma /=.
    iIntros "[Ha Hv]". iApply (ghost_map_lookup with "Ha Hv").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a'.  THE MINT (durable-disk lane H4)                            *)
  (*                                                                   *)
  (*  THE TRANSPORT'S SOURCE IS NEVER MOVED, and that is what lets a    *)
  (*  commit use it.  Everything [fs_footprint_xfer] does with the      *)
  (*  source instance is READ PURE FACTS off it -- the runs' shape, the *)
  (*  runs' disjointness (off [phi_excl]) and the runs' union's place   *)
  (*  inside the source's own authority (off [phi_agree]) -- and then   *)
  (*  allocate.  So the allocation half stands ALONE, over those facts  *)
  (*  and no resource at all, and the two halves compose back into the  *)
  (*  transport with its statement unchanged.                          *)
  (*                                                                   *)
  (*  WHAT IT BUYS.  The commit's source is not an [fs_state] -- it is  *)
  (*  [FsCollect.col_hand], whose records sit region-side and whose     *)
  (*  data legs are at each inode's own share -- so it cannot HAND the  *)
  (*  transport an instance.  It can read the same three facts off      *)
  (*  itself ([FsCollectAll]'s runs walk, share-generically through     *)
  (*  section 2d) and call the mint, and then nothing of the era's has  *)
  (*  to come back out of the collection.                              *)
  (* ---------------------------------------------------------------- *)

  Lemma fs_footprint_mint (S : fs_state_rec) (PM : gmap Z (list (bv 8)))
      (gl gt : gname) :
    xf_shape S PM -> xr_disj (xr_fs S PM) ->
    ⊢ |==> ∃ g : gname,
        ghost_map_auth g 1 (xr_union (xr_fs S PM))
        ∗ fs_footprint (snap_gamma g gl gt) (DfracOwn 1) S.
  Proof.
    intros Hshape Hdisj.
    iMod (ghost_map_alloc (xr_union (xr_fs S PM))) as (g) "[Hba Hbe]".
    iModIntro. iExists g. iFrame "Hba".
    iApply (fs_footprint_of_runs (snap_gamma g gl gt) S PM Hshape).
    rewrite (phi_runs_union (snap_gamma g gl gt) _ Hdisj).
    rewrite /phi_map /snap_gamma /=. iExact "Hbe".
  Qed.

  (* ...AND THE WHOLE INSTANCE, over the same facts plus the ghost half's:
     the superblock's parse, every inode's local clauses, and the link
     family's own validity WITH the root's keep-alive slack.  Not one of
     them is computed: at a commit each is read off the era's resources,
     at era 0 each comes off the image. *)
  Lemma fs_state_mint_runs (S : fs_state_rec) (PM : gmap Z (list (bv 8)))
      (f : link_choice) (v : ity) :
    xf_shape S PM -> xr_disj (xr_fs S PM) ->
    fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S) ->
    (forall i n, fss_inodes S !! i = Some n -> inode_local i n) ->
    (* THE MAP'S OWN GEOMETRY (durable-disk lane H5): the superblock's
       layout and the region's inum column, domain and directory clauses.
       It is [fs_state]'s last conjunct, so a mint owes it exactly as it
       owes the parse; both producers read it off their own source
       ([FsDurSnap.fs_geom_of_ok] at the image, [FsCollect.col_fs_geom] at
       a commit). *)
    fs_geom S ->
    link_elem_ok (fss_inodes S) f ->
    ✓ (link_elem (fss_inodes S) f ⋅ link_tok_elem ROOTINO v) ->
    ⊢ |==> ∃ g gl gt : gname,
        ghost_map_auth g 1 (xr_union (xr_fs S PM))
        ∗ ghost_map_auth gt 1 (fss_inodes S)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (snap_gamma g gl gt) i n)
        ∗ fs_state (snap_gamma g gl gt) (DfracOwn 1) S
        ∗ own gl (link_tok_elem ROOTINO v).
  Proof.
    intros Hshape Hdisj Hparse Hloc Hgeo Hfok Hfv.
    iMod (fs_boot_alloc_root_slack (fss_inodes S) f ROOTINO v Hfok Hfv)
      as (gl gt) "(Hta & Htf & Hl & Ht)".
    iMod (fs_footprint_mint S PM gl gt Hshape Hdisj) as (g) "[Hba Hf]".
    iModIntro. iExists g, gl, gt. iFrame "Hba Hta".
    iSplitL "Htf".
    { rewrite /top_frag /snap_gamma /=. iExact "Htf". }
    iSplitR "Ht"; [| rewrite /snap_gamma /=; iExact "Ht"].
    rewrite fs_state_split fs_ghost_split. iFrame "Hf".
    iSplitL "Hl"; [rewrite /snap_gamma /=; iExact "Hl" |].
    rewrite /fs_pure. iSplitR; [by iPureIntro |].
    iSplitR; [| by iPureIntro].
    iApply big_sepM_intro. iIntros "!>" (i n Hi).
    iPureIntro. exact (Hloc i n Hi).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a.  THE BYTE HALF                                               *)
  (* ---------------------------------------------------------------- *)

  (* THE OUTPUT'S IDENTITY RIDES ALONG (durable-disk lane H3): the fresh map
     is the flattening of the SOURCE's own runs, so the source's authority
     -- as [phi_agree] -- names every one of its bytes in [M], and the
     output map is a SUBSET of [M].  That subset IS what the snapshot's
     byte ties are later read through ([FsDurRead.snap_auth]); nothing is
     computed from [S] and no value is decoded. *)
  Lemma fs_footprint_xfer Γ (Hex : phi_excl Γ) (A : iProp Σ)
      (M : gmap Z (bv 8)) (Hag : phi_agree Γ A M) S (gl gt : gname) :
    A -∗ fs_footprint Γ (DfracOwn 1) S ==∗
      ∃ (g : gname) (B : gmap Z (bv 8)),
        ⌜B ⊆ M⌝ ∗ A ∗ fs_footprint Γ (DfracOwn 1) S ∗ ghost_map_auth g 1 B
        ∗ fs_footprint (snap_gamma g gl gt) (DfracOwn 1) S.
  Proof.
    iIntros "HA Hf".
    iDestruct (fs_footprint_runs with "Hf") as (PM) "[%Hshape Hr]".
    iAssert (⌜xr_disj (xr_fs S PM)⌝ ∧ phi_runs Γ (xr_fs S PM))%I
      with "[Hr]" as "[%Hdisj Hr]".
    { iSplit; [iApply (phi_runs_disj Γ Hex with "Hr") | iExact "Hr"]. }
    iAssert (⌜xr_union (xr_fs S PM) ⊆ M⌝ ∧ (A ∗ phi_runs Γ (xr_fs S PM)))%I
      with "[HA Hr]" as "[%Hin [HA Hr]]".
    { iSplit;
        [iApply (phi_runs_in Γ A M Hag _ Hdisj with "HA Hr") | iFrame]. }
    iMod (fs_footprint_mint S PM gl gt Hshape Hdisj) as (g) "[Hba Hf']".
    iModIntro. iExists g, (xr_union (xr_fs S PM)).
    iSplitR; [by iPureIntro |]. iFrame "HA".
    iSplitL "Hr".
    { iApply (fs_footprint_of_runs Γ S PM Hshape). iExact "Hr". }
    iFrame "Hba". iExact "Hf'".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4b.  THE WHOLE INSTANCE                                          *)
  (* ---------------------------------------------------------------- *)

  Theorem fs_state_xfer Γ (Hex : phi_excl Γ) (A : iProp Σ)
      (M : gmap Z (bv 8)) (Hag : phi_agree Γ A M) S :
    A -∗ fs_state Γ (DfracOwn 1) S ==∗
      ∃ (g gl gt : gname) (B : gmap Z (bv 8)),
        ⌜B ⊆ M⌝
        ∗ A
        ∗ fs_state Γ (DfracOwn 1) S
        ∗ ghost_map_auth g 1 B
        ∗ ghost_map_auth gt 1 (fss_inodes S)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (snap_gamma g gl gt) i n)
        ∗ fs_state (snap_gamma g gl gt) (DfracOwn 1) S.
  Proof.
    iIntros "HA HS". iEval (rewrite fs_state_split fs_ghost_split) in "HS".
    iDestruct "HS" as "(Hf & Hl & #Hp)".
    iAssert (⌜∃ f, link_elem_ok (fss_inodes S) f
                   /\ ✓ link_elem (fss_inodes S) f⌝
             ∧ fs_links (γlink Γ) (fss_inodes S))%I with "[Hl]" as "[%Hlv Hl]".
    { iSplit; [iApply (fs_links_valid with "Hl") | iExact "Hl"]. }
    destruct Hlv as (f & Hfok & Hfv).
    iMod (fs_boot_alloc_at (fss_inodes S) (fss_inodes S) f Hfok Hfv)
      as (gl gt) "(Hta & Htf & Hl')".
    iMod (fs_footprint_xfer Γ Hex A M Hag S gl gt with "HA Hf")
      as (g B) "(%Hin & HA & Hf & Hba & Hf')".
    iModIntro. iExists g, gl, gt, B.
    iSplitR; [by iPureIntro |]. iFrame "HA".
    iSplitL "Hf Hl".
    { rewrite fs_state_split fs_ghost_split. iFrame "Hf Hl Hp". }
    iFrame "Hba Hta".
    iSplitL "Htf".
    { rewrite /top_frag /snap_gamma /=. iExact "Htf". }
    rewrite fs_state_split fs_ghost_split. iFrame "Hf' Hp".
    rewrite /snap_gamma /=. iExact "Hl'".
  Qed.

  (* ...AND THE SAME WITH A SPARE LINK FRAGMENT RIDING ALONG (the inode
     region's keep-alive token at the root, [InodeRegion.ireg_keep]: no
     directory entry accounts for it, so it is not part of [fs_links] and
     has to be transported beside it).  ONE [own_alloc] at the source's own
     element PLUS that fragment -- [FsState.fs_boot_alloc_root_slack] --
     which is why the slack is never a pure clause of anything. *)
  Theorem fs_state_xfer_tok Γ (Hex : phi_excl Γ) (A : iProp Σ)
      (M : gmap Z (bv 8)) (Hag : phi_agree Γ A M) S (r : Z) (v : ity) :
    A -∗ fs_state Γ (DfracOwn 1) S -∗ own (γlink Γ) (link_tok_elem r v) ==∗
      ∃ (g gl gt : gname) (B : gmap Z (bv 8)),
        ⌜B ⊆ M⌝
        ∗ A
        ∗ fs_state Γ (DfracOwn 1) S ∗ own (γlink Γ) (link_tok_elem r v)
        ∗ ghost_map_auth g 1 B
        ∗ ghost_map_auth gt 1 (fss_inodes S)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (snap_gamma g gl gt) i n)
        ∗ fs_state (snap_gamma g gl gt) (DfracOwn 1) S
        ∗ own gl (link_tok_elem r v).
  Proof.
    iIntros "HA HS Ht". iEval (rewrite fs_state_split fs_ghost_split) in "HS".
    iDestruct "HS" as "(Hf & Hl & #Hp)".
    iAssert (⌜∃ f, link_elem_ok (fss_inodes S) f
                   /\ ✓ (link_elem (fss_inodes S) f ⋅ link_tok_elem r v)⌝
             ∧ (fs_links (γlink Γ) (fss_inodes S)
                ∗ own (γlink Γ) (link_tok_elem r v)))%I
      with "[Hl Ht]" as "[%Hlv [Hl Ht]]".
    { iSplit; [iApply (fs_links_valid_tok with "Hl Ht") | iFrame]. }
    destruct Hlv as (f & Hfok & Hfv).
    iMod (fs_boot_alloc_root_slack (fss_inodes S) f r v Hfok Hfv)
      as (gl gt) "(Hta & Htf & Hl' & Ht')".
    iMod (fs_footprint_xfer Γ Hex A M Hag S gl gt with "HA Hf")
      as (g B) "(%Hin & HA & Hf & Hba & Hf')".
    iModIntro. iExists g, gl, gt, B.
    iSplitR; [by iPureIntro |]. iFrame "HA".
    iSplitL "Hf Hl".
    { rewrite fs_state_split fs_ghost_split. iFrame "Hf Hl Hp". }
    iFrame "Ht Hba Hta".
    iSplitL "Htf".
    { rewrite /top_frag /snap_gamma /=. iExact "Htf". }
    iSplitR "Ht'"; [| rewrite /snap_gamma /=; iExact "Ht'"].
    rewrite fs_state_split fs_ghost_split. iFrame "Hf' Hp".
    rewrite /snap_gamma /=. iExact "Hl'".
  Qed.

End Xfer.
