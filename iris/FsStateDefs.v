(* FsStateDefs.v -- the view record [Γ], the byte points-to, and the two
   block-level shapes every other file-system predicate is built from.

   Design of record: claude-notes/design/fs-state.md sections 0-2.  This is
   stage 2a of claude-notes/projects/durable-disk.md.

   THE ONE THING THAT MENTIONS A DISK is the field [fsΦ] of [fs_view_names]:
   a byte-address-keyed points-to, ABSTRACT here.  The file system is
   instantiated twice over the same definitions (fs-state.md section 1) --
   at the committed view [Γ_D], where [fsΦ] is the full element of the
   fixed-layer byte map, and at the logged view [Γ_L], where it is the full
   element of the era's logged view.  Nothing below knows which.

   Consequently this file imports NOTHING from [FsBlocks]/[LogInv]/any
   [Proof*]/[Spec*] file: it is pure Iris over the tree's ENCODING
   vocabulary (FsImg/DinodeEnc/BitmapEnc/FsTree/BlockWords) only.

   THE POINTS-TO IS FRACTION-INDEXED (durable-fs-plan.md sections 4 and 6,
   lane B').  [fsΦ] takes a [dfrac], and so do the two block shapes, in the
   [_q] forms below; [byte_range] and [blk_owned] are the [DfracOwn 1]
   READINGS of them and their text has not moved, which is why the durable
   instance (FsDurBytes/FsDurImg/FsDurSnap/FsDurAlloc and
   FsStateBitmap -- about seventy-five uses, all at fraction 1 by plan
   section 1) is untouched by the index.  What wants a fraction is exactly
   the ERA instance's data and indirect blocks, so that [ilock] without a
   transaction can hand a reader a QUARTER (plan section 4: two read-locked
   inodes leaving three quarters each cannot alias a block, 3/4 + 3/4 > 1,
   so cross-inode disjointness at the commit's collection stays pure
   separation logic).  RECORDS DO NOT: they park region-side at fraction 1
   always, so [rec_owned] keeps its arity.

   Three properties of [fsΦ] are needed by consumers and cannot be proved of
   an abstract predicate, so they are stated here and TAKEN AS PARAMETERS
   where they are used (the standing rule: a parameter, not a new
   config-class dependency):

   - [phi_excl Γ]: two owners of one byte own no more than all of it, i.e.
     [fsΦ dq1 ∗ fsΦ dq2 ⊢ ✓ (dq1 ⋅ dq2)].  Its fraction-1 reading is the
     old "two owners is [False]", which is what makes [free_bitmap]'s "the
     bit reads allocated" argument run (fs-state.md section 2) -- the
     [fsblock_excl] of the concrete instance, lifted; its 3/4 + 3/4 reading
     is the commit's cross-inode disjointness.
   - [phi_frac Γ]: the points-to splits along [⋅], which is how a quarter
     is handed out and taken back.
   - [GTimeless Γ]: every byte points-to is timeless.  Both concrete
     instances are ghost-map elements, so both satisfy it, and every
     predicate below is then timeless -- which is what the [>]-strips of
     the in-memory accessors need (fs-ghost-state.md section 1).  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import BioDefs.
Require Import FsImg.

(* the proofmode import re-opens nat_scope on top of the scope stack, so the
   file's scope has to be (re-)issued after it -- durable-notes.md *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The view record                                                *)
(* ------------------------------------------------------------------ *)

Section GammaDefs.
  Context {Σ : gFunctors}.

  (* A RANGE-INDEXED BIG-OP OVER A [map_seqZ] IS THE MAP'S.  Stated over a
     bare [Σ], so every view -- the logged one and the durable one alike --
     uses this one copy.  [FsBlocks] keeps a twin only because that file
     defines its own [byte_range]/[byte_range_q]: importing this one there
     would shadow the block layer's names. *)
  Lemma big_sepM_map_seqZ_gen (Phi : Z -> bv 8 -> iProp Σ) (start : Z)
      (xs : list (bv 8)) :
    ([∗ map] a ↦ v ∈ (map_seqZ start xs : gmap Z (bv 8)), Phi a v)
    ⊣⊢ ([∗ list] k ↦ v ∈ xs, Phi (start + Z.of_nat k) v).
  Proof.
    revert start. induction xs as [| x xs IH]; intros start.
    - simpl. rewrite big_sepM_empty //.
    - rewrite map_seqZ_cons big_sepM_insert; [| apply map_seqZ_cons_disjoint].
      rewrite IH big_sepL_cons.
      assert (Hz : start + Z.of_nat 0 = start) by lia. rewrite Hz.
      f_equiv. apply big_sepL_proper. intros k y _.
      assert (Hs : Z.succ start + Z.of_nat k = start + Z.of_nat (S k)) by lia.
      rewrite Hs //.
  Qed.

  (* [fsΦ] is spelled [Φ] in the design; the field is renamed here because a
     top-level projection named [Φ] would shadow the proofmode's ubiquitous
     [Φ] binder at every use site. *)
  Record fs_view_names := MkFsView {
    fsΦ   : dfrac -> Z -> bv 8 -> iProp Σ;  (* byte ownership, BY BYTE ADDRESS *)
    γlink : gname;                  (* the link-counting family (FsStateLink) *)
    γtop  : gname;                  (* the top-level abstract map (FsState)   *)
  }.

  (* the exclusivity law of the concrete instances, as a hypothesis.  The
     fraction-aware form: two owners of one byte hold a VALID sum.  At
     [DfracOwn 1] on either side that sum is invalid, which is the old
     law; at [3/4 ⋅ 3/4] it is invalid too, which is why a read-locker's
     share is a quarter and not a half (plan section 4). *)
  Definition phi_excl (Γ : fs_view_names) : Prop :=
    forall (a : Z) (v w : bv 8) (dq1 dq2 : dfrac),
      (fsΦ Γ dq1 a v ∗ fsΦ Γ dq2 a w) ⊢ ⌜✓ (dq1 ⋅ dq2)⌝.

  (* ...and the splitting law, which is how the quarter is handed out.
     Stated on [DfracOwn] alone -- that is the [Fractional] law both
     ghost-map instances satisfy, and every share the design hands out is
     an ordinary fraction. *)
  Definition phi_frac (Γ : fs_view_names) : Prop :=
    forall (a : Z) (v : bv 8) (q1 q2 : Qp),
      fsΦ Γ (DfracOwn (q1 + q2)) a v
      ⊣⊢ fsΦ Γ (DfracOwn q1) a v ∗ fsΦ Γ (DfracOwn q2) a v.

  Class GTimeless (Γ : fs_view_names) :=
    gtimeless : forall (dq : dfrac) (a : Z) (v : bv 8), Timeless (fsΦ Γ dq a v).

  (* ---------------------------------------------------------------- *)
  (*  2.  The points-to run                                            *)
  (* ---------------------------------------------------------------- *)

  (* [bs] resides at byte offset [off] of block [b], at share [dq]. *)
  Definition byte_range_q (Γ : fs_view_names) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] k ↦ v ∈ bs, fsΦ Γ dq (b * BSIZE_z + off + Z.of_nat k) v)%I.

  (* THE FRACTION-1 READING, and it is a [Definition] rather than a
     notation so that every one of the ~75 durable-side uses and every
     [rewrite /blk_owned] in the tree keeps its exact text. *)
  Definition byte_range (Γ : fs_view_names) (b off : Z) (bs : list (bv 8))
    : iProp Σ :=
    byte_range_q Γ (DfracOwn 1) b off bs.

  (* a whole block, at its full width, at share [dq] *)
  Definition blk_owned_q (Γ : fs_view_names) (dq : dfrac) (b : Z)
      (bs : list (bv 8)) : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range_q Γ dq b 0 bs)%I.

  Definition blk_owned (Γ : fs_view_names) (b : Z) (bs : list (bv 8))
    : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range Γ b 0 bs)%I.

  Lemma byte_range_1 Γ b off bs :
    byte_range Γ b off bs = byte_range_q Γ (DfracOwn 1) b off bs.
  Proof. reflexivity. Qed.

  Lemma blk_owned_1 Γ b bs :
    blk_owned Γ b bs = blk_owned_q Γ (DfracOwn 1) b bs.
  Proof. reflexivity. Qed.

  Global Instance byte_range_q_timeless `{!GTimeless Γ} dq b off bs :
    Timeless (byte_range_q Γ dq b off bs).
  Proof.
    rewrite /byte_range_q. apply big_sepL_timeless.
    intros. apply gtimeless.
  Qed.

  Global Instance byte_range_timeless `{!GTimeless Γ} b off bs :
    Timeless (byte_range Γ b off bs).
  Proof. rewrite /byte_range. apply _. Qed.

  Global Instance blk_owned_q_timeless `{!GTimeless Γ} dq b bs :
    Timeless (blk_owned_q Γ dq b bs).
  Proof. rewrite /blk_owned_q. apply _. Qed.

  Global Instance blk_owned_timeless `{!GTimeless Γ} b bs :
    Timeless (blk_owned Γ b bs).
  Proof. rewrite /blk_owned. apply _. Qed.

  Lemma blk_owned_q_length Γ dq b bs :
    blk_owned_q Γ dq b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma blk_owned_length Γ b bs : blk_owned Γ b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma byte_range_q_nil Γ dq b off : byte_range_q Γ dq b off [] ⊣⊢ emp.
  Proof. rewrite /byte_range_q //. Qed.

  Lemma byte_range_nil Γ b off : byte_range Γ b off [] ⊣⊢ emp.
  Proof. rewrite /byte_range byte_range_q_nil //. Qed.

  Lemma byte_range_q_app Γ dq b off bs1 bs2 :
    byte_range_q Γ dq b off (bs1 ++ bs2)
    ⊣⊢ byte_range_q Γ dq b off bs1
        ∗ byte_range_q Γ dq b (off + Z.of_nat (length bs1)) bs2.
  Proof.
    rewrite /byte_range_q big_sepL_app.
    apply bi.sep_proper; [done |].
    apply big_sepL_proper. intros k y _.
    assert (Hz : b * BSIZE_z + off + Z.of_nat (length bs1 + k)
                 = b * BSIZE_z + (off + Z.of_nat (length bs1)) + Z.of_nat k)
      by lia.
    rewrite Hz //.
  Qed.

  Lemma byte_range_app Γ b off bs1 bs2 :
    byte_range Γ b off (bs1 ++ bs2)
    ⊣⊢ byte_range Γ b off bs1
        ∗ byte_range Γ b (off + Z.of_nat (length bs1)) bs2.
  Proof. rewrite /byte_range byte_range_q_app //. Qed.

  (* ---------------------------------------------------------------- *)
  (*  2a.  SPLITTING A RUN ALONG [⋅] -- how the quarter is handed out  *)
  (* ---------------------------------------------------------------- *)

  Lemma byte_range_q_split Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) b off bs :
    byte_range_q Γ (DfracOwn (q1 + q2)) b off bs
    ⊣⊢ byte_range_q Γ (DfracOwn q1) b off bs
        ∗ byte_range_q Γ (DfracOwn q2) b off bs.
  Proof.
    rewrite /byte_range_q -big_sepL_sep.
    apply big_sepL_proper. intros k v _. apply Hfr.
  Qed.

  Lemma blk_owned_q_split Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) b bs :
    blk_owned_q Γ (DfracOwn (q1 + q2)) b bs
    ⊣⊢ blk_owned_q Γ (DfracOwn q1) b bs ∗ blk_owned_q Γ (DfracOwn q2) b bs.
  Proof.
    rewrite /blk_owned_q (byte_range_q_split Γ Hfr).
    iSplit.
    - iIntros "[%Hl [H1 H2]]". iSplitL "H1"; by iFrame.
    - iIntros "[[%Hl H1] [_ H2]]". by iFrame.
  Qed.

  (* the shares the design names: a read-locker takes a quarter and the
     escrow keeps three quarters (plan section 4) *)
  Lemma blk_owned_split_34 Γ (Hfr : phi_frac Γ) b bs :
    blk_owned Γ b bs
    ⊣⊢ blk_owned_q Γ (DfracOwn (3/4)) b bs ∗ blk_owned_q Γ (DfracOwn (1/4)) b bs.
  Proof.
    rewrite blk_owned_1 -(blk_owned_q_split Γ Hfr (3/4) (1/4)).
    rewrite Qp.three_quarter_quarter //.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2b.  THE CONSTANT-SHARE VIEW (durable-disk lane H4, moved down    *)
  (*       here at EV-X)                                                *)
  (*                                                                    *)
  (*  [gamma_q Γ dq] is [Γ] with its byte points-to pinned at ONE share: *)
  (*  its [fsΦ] DISCARDS the dfrac it is handed and always uses [dq].    *)
  (*  Consequently EVERY Gamma-generic shape in the tree -- [byte_range],*)
  (*  [blk_owned], [FsStateInode.inode_phi], [FsStateBitmap.free_pool],  *)
  (*  [FsState.fs_state] -- reads AT A SHARE with no new definition and  *)
  (*  no new lemma: the [_q] twins below are what those shapes BECOME    *)
  (*  at this view, on the nose ([gamma_q_byte_range] is [reflexivity]). *)
  (*  That is what makes [FsState.fs_state]'s dfrac argument cost one    *)
  (*  line rather than a parallel hierarchy (durable-disk EV-X).         *)
  (*                                                                    *)
  (*  THE GHOST COLUMN IS UNTOUCHED: [γlink] and [γtop] are copied, so   *)
  (*  every Φ-FREE piece of a file system ([FsStateInode.inode_ghost],   *)
  (*  [FsState.fs_links], [top_frag]) is LITERALLY the same proposition  *)
  (*  at [gamma_q Γ dq] as at [Γ] -- which is the whole content of the   *)
  (*  ruling: byte legs take the share, authorities stay whole.          *)
  (*                                                                    *)
  (*  IT DOES NOT SATISFY [phi_excl] (its [fsΦ] ignores the dfracs the   *)
  (*  law quantifies over), so exclusivity is always read at [Γ] with a  *)
  (*  [~ ✓ (dq ⋅ dq)] side condition -- [FsDurXfer]'s [phi_runs_q_disj]. *)
  (* ---------------------------------------------------------------- *)

  Definition gamma_q (Γ : fs_view_names) (dq : dfrac) : fs_view_names :=
    MkFsView (fun (_ : dfrac) (a : Z) (v : bv 8) => fsΦ Γ dq a v)
             (γlink Γ) (γtop Γ).

  Lemma gamma_q_byte_range Γ dq b off bs :
    byte_range (gamma_q Γ dq) b off bs ⊣⊢ byte_range_q Γ dq b off bs.
  Proof. rewrite /byte_range /byte_range_q /gamma_q //. Qed.

  Lemma gamma_q_blk_owned Γ dq b bs :
    blk_owned (gamma_q Γ dq) b bs ⊣⊢ blk_owned_q Γ dq b bs.
  Proof. rewrite /blk_owned /blk_owned_q gamma_q_byte_range //. Qed.

  (* THE FULL-SHARE READING IS THE THING ITSELF, on the nose: [byte_range]
     hands [DfracOwn 1] down, and that is what the constant view then
     ignores.  This is why a consumer of the old fraction-1 predicate moves
     by a SWEEP ([DfracOwn 1] in the argument list) and not by re-proof. *)
  Lemma gamma_q_1_byte_range Γ b off bs :
    byte_range (gamma_q Γ (DfracOwn 1)) b off bs = byte_range Γ b off bs.
  Proof. reflexivity. Qed.

  Lemma gamma_q_1_blk_owned Γ b bs :
    blk_owned (gamma_q Γ (DfracOwn 1)) b bs = blk_owned Γ b bs.
  Proof. reflexivity. Qed.

  Global Instance gamma_q_gtimeless Γ `{!GTimeless Γ} dq :
    GTimeless (gamma_q Γ dq).
  Proof. intros dq' a v. rewrite /gamma_q /=. apply gtimeless. Qed.

  (* ---------------------------------------------------------------- *)
  (*  2c.  SHEDDING A SHARE, AS A MAP BETWEEN VIEWS                     *)
  (*                                                                    *)
  (*  The commit's collection meets the metadata objects and the         *)
  (*  region's records at fraction 1 while a read-locked inode's data    *)
  (*  leg stands at three quarters, so the whole ones are SHED down to   *)
  (*  the uniform share the transport takes (durable-disk EV-X).  Stated *)
  (*  once, at the VIEW: [view_shed Γ Γ1 Γ2] says a byte at [Γ] splits   *)
  (*  into one at [Γ1] and one at [Γ2], and every shape above then sheds *)
  (*  by one three-line induction each.  [gamma_q_shed] is the only      *)
  (*  instance, and it is [phi_frac] verbatim.                           *)
  (*                                                                    *)
  (*  ONE DIRECTION ONLY.  Rejoining is not stated here because the free *)
  (*  pool's element hides its bytes under an existential, so two halves *)
  (*  of a pool row cannot be put back without an agreement law -- and   *)
  (*  nothing ever needs to: the transport RETURNS its source.           *)
  (* ---------------------------------------------------------------- *)

  Definition view_shed (Γ Γ1 Γ2 : fs_view_names) : Prop :=
    forall (dq : dfrac) (a : Z) (v : bv 8),
      fsΦ Γ dq a v ⊢ fsΦ Γ1 dq a v ∗ fsΦ Γ2 dq a v.

  Lemma gamma_q_shed Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) :
    view_shed (gamma_q Γ (DfracOwn (q1 + q2)))
              (gamma_q Γ (DfracOwn q1)) (gamma_q Γ (DfracOwn q2)).
  Proof. intros dq a v. rewrite /gamma_q /=. rewrite (Hfr a v q1 q2) //. Qed.

  Lemma byte_range_shed Γ Γ1 Γ2 (Hs : view_shed Γ Γ1 Γ2) b off bs :
    byte_range Γ b off bs ⊢ byte_range Γ1 b off bs ∗ byte_range Γ2 b off bs.
  Proof.
    rewrite /byte_range /byte_range_q -big_sepL_sep.
    apply big_sepL_mono. intros k v _. apply Hs.
  Qed.

  Lemma blk_owned_shed Γ Γ1 Γ2 (Hs : view_shed Γ Γ1 Γ2) b bs :
    blk_owned Γ b bs ⊢ blk_owned Γ1 b bs ∗ blk_owned Γ2 b bs.
  Proof.
    rewrite /blk_owned. iIntros "[%Hl H]".
    iDestruct (byte_range_shed Γ Γ1 Γ2 Hs with "H") as "[H1 H2]".
    iSplitL "H1"; by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  Exclusivity: two owners of one byte is [False]               *)
  (*                                                                   *)
  (*  This is the ONE exclusivity law the design ever invokes -- used  *)
  (*  exactly as [l ↦ _ ∗ l ↦ _ ⊢ False] is, to learn that two owned   *)
  (*  things are different objects, never as an invariant.             *)
  (* ---------------------------------------------------------------- *)

  (* the general form: two runs at the same address bound their shares *)
  Lemma byte_range_q_valid Γ (Hex : phi_excl Γ) dq1 dq2 b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range_q Γ dq1 b off bs -∗ byte_range_q Γ dq2 b off bs' -∗
    ⌜✓ (dq1 ⋅ dq2)⌝.
  Proof.
    intros Hl Hl'.
    iIntros "H H'".
    destruct (lookup_lt_is_Some_2 bs 0%nat Hl) as [v Hv].
    destruct (lookup_lt_is_Some_2 bs' 0%nat Hl') as [v' Hv'].
    rewrite /byte_range_q.
    iDestruct (big_sepL_lookup _ _ 0%nat v Hv with "H") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat v' Hv' with "H'") as "H2".
    iApply (Hex (b * BSIZE_z + off + Z.of_nat 0%nat) v v' dq1 dq2).
    iFrame.
  Qed.

  Lemma byte_range_q_excl Γ (Hex : phi_excl Γ) dq1 dq2 b off bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range_q Γ dq1 b off bs -∗ byte_range_q Γ dq2 b off bs' -∗ False.
  Proof.
    intros Hnv Hl Hl'. iIntros "H H'".
    iDestruct (byte_range_q_valid Γ Hex dq1 dq2 b off bs bs' Hl Hl'
                 with "H H'") as %Hv.
    done.
  Qed.

  (* [DfracOwn 1] excludes ANY other share: the shape every fraction-1
     reading below goes through. *)
  Lemma dfrac_full_nvalid (dq : dfrac) : ~ ✓ (DfracOwn 1 ⋅ dq).
  Proof. intros Hv. exact (exclusive_l (DfracOwn 1) dq Hv). Qed.

  Lemma byte_range_excl Γ (Hex : phi_excl Γ) b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range Γ b off bs -∗ byte_range Γ b off bs' -∗ False.
  Proof.
    intros Hl Hl'. rewrite !byte_range_1.
    iApply (byte_range_q_excl Γ Hex (DfracOwn 1) (DfracOwn 1) b off bs bs'
              (dfrac_full_nvalid _) Hl Hl').
  Qed.

  Lemma BSIZE_pos_nat : (0 < BSIZE)%nat.
  Proof. rewrite /BSIZE. lia. Qed.

  Lemma blk_owned_q_excl Γ (Hex : phi_excl Γ) dq1 dq2 b bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    blk_owned_q Γ dq1 b bs -∗ blk_owned_q Γ dq2 b bs' -∗ False.
  Proof.
    intros Hnv.
    iIntros "[%Hl H] [%Hl' H']".
    iApply (byte_range_q_excl Γ Hex dq1 dq2 b 0 bs bs' Hnv with "H H'");
      [rewrite Hl | rewrite Hl']; apply BSIZE_pos_nat.
  Qed.

  Lemma blk_owned_excl Γ (Hex : phi_excl Γ) b bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b bs' -∗ False.
  Proof.
    rewrite !blk_owned_1.
    iApply (blk_owned_q_excl Γ Hex (DfracOwn 1) (DfracOwn 1) b bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* "distinctness of an inode's own blocks is the [∗]" (fs-state.md
     section 2): the disjointness clause [blkmap_wf]'s injectivity used to
     state is a CONSEQUENCE here, not a maintained fact. *)
  Lemma blk_owned_q_ne Γ (Hex : phi_excl Γ) dq1 dq2 b b' bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    blk_owned_q Γ dq1 b bs -∗ blk_owned_q Γ dq2 b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    intros Hnv.
    iIntros "H H'". destruct (decide (b = b')) as [-> | Hne]; [| done].
    iDestruct (blk_owned_q_excl Γ Hex dq1 dq2 _ _ _ Hnv with "H H'") as "[]".
  Qed.

  Lemma blk_owned_ne Γ (Hex : phi_excl Γ) b b' bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    rewrite !blk_owned_1.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn 1) (DfracOwn 1) b b' bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* THE TWO SPECIALISATIONS THE DESIGN NAMES (plan section 4).

     [_full]: a full owner excludes ANY other share -- which is what makes
     "a read-locker cannot write a data block" a resource fact, since
     [SpecLogWrite.wp_log_write_au_range] needs fraction 1.
     [_34]: two THREE-QUARTER owners cannot alias, because 3/4 + 3/4 > 1.
     That is the reason the reader's share is a quarter: the commit's
     collection lemma reads cross-inode block disjointness off the [∗]
     between two read-locked inodes' escrow residues. *)
  Lemma blk_owned_ne_full Γ (Hex : phi_excl Γ) dq b b' bs bs' :
    blk_owned Γ b bs -∗ blk_owned_q Γ dq b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    rewrite blk_owned_1.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn 1) dq b b' bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* 3/4 + 3/4 > 1 -- the arithmetic that makes the reader's share a
     QUARTER and not a half (plan section 4) *)
  Lemma dfrac_34_nvalid : ~ ✓ (DfracOwn (3/4) ⋅ DfracOwn (3/4)).
  Proof.
    rewrite dfrac_op_own. intros Hv%dfrac_valid_own.
    apply (Qp.lt_nge 1 (3/4 + 3/4)%Qp); [| exact Hv].
    apply Qp.lt_sum. exists (1/2)%Qp. compute_done.
  Qed.

  Lemma blk_owned_ne_34 Γ (Hex : phi_excl Γ) b b' bs bs' :
    blk_owned_q Γ (DfracOwn (3/4)) b bs -∗
    blk_owned_q Γ (DfracOwn (3/4)) b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn (3/4)) (DfracOwn (3/4)) b b' bs bs'
              dfrac_34_nvalid).
  Qed.

End GammaDefs.

Global Arguments fs_view_names : clear implicits.
Global Existing Instance gtimeless.

(* Any [Definition] whose body is a big-op over a block-sized list must be
   sealed the day it is written, or [iFrame] resolves its [Frame] instances
   up to delta, unfolds a 1024-element [big_sepL] and does not come back
   (measured at over ten minutes on the concrete twin, [FsBlocks.fsblock]).
   [rewrite /byte_range] and the declared [Timeless] instances still work. *)
Global Typeclasses Opaque byte_range_q blk_owned_q byte_range blk_owned.
