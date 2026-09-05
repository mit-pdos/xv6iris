(* FsAbsDelta.v -- THE FIVE WRITE DELTAS ON [aview], HOISTED.

   The pure delta functions the AU commits fire, each moved here VERBATIM
   from the spec file that minted it (2026-09-04; a pure hoist -- no
   statement changed, no proof touched, R10):

     [acre_bump], [delta_create] + row algebra      from SpecSysMknodAU.v
     splice algebra, [delta_write] + row algebra    from SpecSysWriteAU.v
     [delta_trunc] + row algebra                    from SpecSysOpenAU.v
     [unl_dec], [delta_unl_ent], [delta_unl_tgt],
       [delta_unlink] + row algebra                 from SpecSysUnlinkAU.v

   Each of those files does [Require Export FsAbsDelta] at the point the
   text stood, so every consumer of a spec file still sees the same names
   bound to the same constants.  What did NOT move: the side-condition
   predicates ([cre_pre], [wri_pre], [unl_pre]) and every lemma stated over
   one of them ([delta_create_dev], [delta_unlink_split], the orphan
   family, [unl_pre_ne]), the chained reading ([woff]/[wri_row]/
   [delta_write_chain]), and anything that names an iProp or a ghost.

   WHY.  An application's license (FsAbsInv.fsabs_lic) is stated over the
   union of these deltas -- [fs_delta], at the END of this file -- and
   FsAbsInv sits below [ProcInv]; the spec files do not.  This file's cone
   is FsAbsDefs (the pure abstract state), FsBlocks ([blk_splice]) and
   TsoCtx ([CurCtx], the binder [delta_trunc] carries).

   [delta_trunc]'s `{XI : CurCtx}` binder is kept EXACTLY: consumers apply
   it under an ambient [CurCtx], and dropping the binder would change the
   constant's arity.  [fs_delta] carries the same binder for the same
   reason. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import FsBlocks.       (* [blk_splice]: the landed byte splice        *)
Require Import TsoCtx.         (* [CurCtx]: [delta_trunc]'s binder            *)
Require Import FsTree.         (* [fname]                                     *)
Require Import FsAbsDefs.      (* LAST: [aview], [anode], [absnode]            *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  CREATE (from SpecSysMknodAU.v)                                   *)
(* ===================================================================== *)

(* mkdir's fused parent bump (doc section 4: "mkdir additionally:
   d.nlink+1 -- fused, one delta"); zero for every other child kind *)
Definition acre_bump (c : absnode) : nat :=
  match c with ADir _ => 1%nat | _ => 0%nat end.

(* THE DELTA (doc section 4's [δ_create], type-parameterized): the parent
   gains [nm ↦ i], the child's row becomes [c] at nlink 1, and a
   directory child bumps the parent's nlink.  Total on purpose -- applied
   where the parent is not a directory it is the identity; the side
   conditions live in [cre_pre], not in the function. *)
Definition delta_create (d : Z) (nm : fname) (i : Z) (c : absnode)
    (av : aview) : aview :=
  match av !! d with
  | Some a =>
      match an_node a with
      | ADir ents =>
          <[i := MkAnode c 1%nat]>
            (<[d := MkAnode (ADir (<[nm := i]> ents))
                            (an_nlink a + acre_bump c)%nat]> av)
      | _ => av
      end
  | None => av
  end.

(* the delta's row algebra -- the caller-facing readings unlink and write
   will restate in their own vocabulary *)
Lemma delta_create_parent (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> d <> i ->
  delta_create d nm i c av !! d
  = Some (MkAnode (ADir (<[nm := i]> ents)) (nl + acre_bump c)%nat).
Proof.
  intros Hd Hne. rewrite /delta_create Hd /=.
  rewrite lookup_insert_ne; [| congruence].
  by rewrite lookup_insert.
Qed.

Lemma delta_create_child (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  delta_create d nm i c av !! i = Some (MkAnode c 1%nat).
Proof. intros Hd. rewrite /delta_create Hd /=. by rewrite lookup_insert. Qed.

Lemma delta_create_other (av : aview) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (j : Z) :
  j <> d -> j <> i -> delta_create d nm i c av !! j = av !! j.
Proof.
  intros Hjd Hji. rewrite /delta_create.
  destruct (av !! d) as [a |]; [| done].
  destruct (an_node a) as [bs | ents0 | ma0 mi0]; [done | | done].
  rewrite lookup_insert_ne; [| congruence].
  by rewrite lookup_insert_ne; [| congruence].
Qed.

(* ===================================================================== *)
(*  2.  WRITE (from SpecSysWriteAU.v)                                    *)
(* ===================================================================== *)

(* THE SPLICE IS [FsBlocks.blk_splice], REUSED: [blk_splice off sub bs] is
   [take off bs ++ sub ++ drop (off + length sub) bs], which is the doc's
   "AFile (splice off bs)" already -- and it MAY GROW: past the end the
   [drop] is empty and the result's length is [off + length sub].
   [blk_splice_length_grow] is the "size = max" reading; FsBlocks's own
   [blk_splice_length] is the in-bounds special case. *)

Lemma blk_splice_nil (off : nat) (bs : list (bv 8)) :
  blk_splice off [] bs = bs.
Proof. rewrite /blk_splice /= Nat.add_0_r take_drop //. Qed.

Lemma blk_splice_length_grow (off : nat) (sub bs : list (bv 8)) :
  (off <= length bs)%nat ->
  length (blk_splice off sub bs) = Nat.max (off + length sub) (length bs).
Proof.
  intros Hle.
  rewrite /blk_splice !length_app length_take_le // length_drop. lia.
Qed.

(* THE COMPOSITION: two splices at adjacent offsets ARE one splice of the
   concatenation.  This is what makes the per-chunk deltas COMPOSE, and it
   is the pure heart of the stable corollary. *)
Lemma blk_splice_splice (off : nat) (bs1 bs2 bs0 : list (bv 8)) :
  (off <= length bs0)%nat ->
  blk_splice (off + length bs1)%nat bs2 (blk_splice off bs1 bs0)
  = blk_splice off (bs1 ++ bs2) bs0.
Proof.
  intros Hle. rewrite {1 2}/blk_splice.
  assert (HA : off = length (take off bs0))
    by (rewrite length_take_le //).
  rewrite (take_app_add' _ _ _ _ HA) take_app_length.
  rewrite -Nat.add_assoc (drop_app_add' _ _ _ _ HA) drop_app_add drop_drop.
  rewrite /blk_splice length_app Nat.add_assoc -!app_assoc //.
Qed.

(* THE DELTA (doc section 4's [δ_write]): splice [new] into the file's
   bytes at [off]; nlink untouched.  Total on purpose -- applied where the
   row is not an [AFile] it is the identity; the side conditions live in
   [wri_pre], not in the function (the mknod mold's rule). *)
Definition delta_write (i : Z) (off : nat) (new : list (bv 8))
    (av : aview) : aview :=
  match av !! i with
  | Some a =>
      match an_node a with
      | AFile bs =>
          <[i := MkAnode (AFile (blk_splice off new bs)) (an_nlink a)]> av
      | _ => av
      end
  | None => av
  end.

(* the delta's row algebra *)
Lemma delta_write_file (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off new av
  = <[i := MkAnode (AFile (blk_splice off new bs0)) nl]> av.
Proof. intros Hi. rewrite /delta_write Hi //=. Qed.

Lemma delta_write_lookup (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off new av !! i
  = Some (MkAnode (AFile (blk_splice off new bs0)) nl).
Proof.
  intros Hi. rewrite (delta_write_file _ _ _ _ _ _ Hi) lookup_insert //.
Qed.

Lemma delta_write_other (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (j : Z) :
  j <> i -> delta_write i off new av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_write.
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node a) as [bs | ents | ma mi]; [| done | done].
  rewrite lookup_insert_ne //.
Qed.

(* a zero-byte chunk is the identity -- which is why [wri_pre] may demand
   [0 < length bs] with nothing lost *)
Lemma delta_write_nil (av : aview) (i : Z) (off : nat)
    (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off [] av = av.
Proof.
  intros Hi.
  rewrite (delta_write_file _ _ _ _ _ _ Hi) blk_splice_nil insert_id //.
Qed.

(* ===================================================================== *)
(*  3.  TRUNC (from SpecSysOpenAU.v)                                     *)
(* ===================================================================== *)

(* THE DELTA: the file's bytes become empty; nlink untouched.  Total on
   purpose -- applied where the row is not an [AFile] it is the identity;
   the side condition lives in the commit's premise, not in the function
   (the family rule). *)
Definition delta_trunc `{XI : CurCtx} (i : Z) (av : aview) : aview :=
  match av !! i with
  | Some a =>
      match an_node a with
      | AFile _ => <[i := MkAnode (AFile []) (an_nlink a)]> av
      | _ => av
      end
  | None => av
  end.

(* the delta's row algebra *)
Lemma delta_trunc_file `{XI : CurCtx} (av : aview) (i : Z) (bs0 : list (bv 8))
    (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_trunc i av = <[i := MkAnode (AFile []) nl]> av.
Proof. intros Hi. rewrite /delta_trunc Hi //=. Qed.

Lemma delta_trunc_lookup `{XI : CurCtx} (av : aview) (i : Z) (bs0 : list (bv 8))
    (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_trunc i av !! i = Some (MkAnode (AFile []) nl).
Proof.
  intros Hi. rewrite (delta_trunc_file av i bs0 nl Hi) lookup_insert //.
Qed.

Lemma delta_trunc_other `{XI : CurCtx} (av : aview) (i j : Z) :
  j <> i -> delta_trunc i av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_trunc.
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node a) as [bs | ents | ma mi]; [| done | done].
  rewrite lookup_insert_ne //.
Qed.

(* truncating an EMPTY file is the identity -- why the CREATE-fresh arm
   refunds the trunc commit instead of firing it vacuously (header) *)
Lemma delta_trunc_nil `{XI : CurCtx} (av : aview) (i : Z) (nl : nat) :
  av !! i = Some (MkAnode (AFile []) nl) -> delta_trunc i av = av.
Proof.
  intros Hi. rewrite (delta_trunc_file av i [] nl Hi).
  by rewrite (insert_id av i (MkAnode (AFile []) nl) Hi).
Qed.

(* ===================================================================== *)
(*  4.  UNLINK (from SpecSysUnlinkAU.v)                                  *)
(* ===================================================================== *)

(* the dir-arm's parent decrement -- [acre_bump]'s inverse-shaped sibling:
   unlinking a directory child drops the parent's [".."]-backed count *)
Definition unl_dec (c : absnode) : nat :=
  match c with ADir _ => 1%nat | _ => 0%nat end.

(* THE TWO ONE-ROW HALVES THE MACHINE REALIZES (header: THE DELTA IS TWO
   INSTANTS).  Total on purpose; applied off-shape they are the
   identity. *)

(* instant 1 -- the parent's row: the name deleted, the count down [dec]
   (the dir arm's [dp->nlink--], zero otherwise) *)
Definition delta_unl_ent (d : Z) (nm : fname) (dec : nat)
    (av : aview) : aview :=
  match av !! d with
  | Some p =>
      match an_node p with
      | ADir ents =>
          <[d := MkAnode (ADir (delete nm ents))
                         (an_nlink p - dec)%nat]> av
      | _ => av
      end
  | None => av
  end.

(* instant 2 -- the target's row: same node, count down one *)
Definition delta_unl_tgt (t : Z) (av : aview) : aview :=
  match av !! t with
  | Some a => <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]> av
  | None => av
  end.

(* THE FUSED DELTA (doc section 4's [δ_unlink], the quiescent reading):
   parent loses [nm], target's nlink drops, a directory target drops the
   parent's nlink too.  [delta_unlink_split] below ties it to the two
   halves; the AU commits fire the halves. *)
Definition delta_unlink (d : Z) (nm : fname) (t : Z)
    (av : aview) : aview :=
  match av !! d with
  | Some p =>
      match av !! t with
      | Some a =>
          match an_node p with
          | ADir ents =>
              <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]>
                (<[d := MkAnode (ADir (delete nm ents))
                                (an_nlink p - unl_dec (an_node a))%nat]> av)
          | _ => av
          end
      | None => av
      end
  | None => av
  end.

(* ---- the halves' row algebra ---------------------------------------- *)

Lemma delta_unl_ent_parent (av : aview) (d : Z) (nm : fname) (dec : nat)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  delta_unl_ent d nm dec av !! d
  = Some (MkAnode (ADir (delete nm ents)) (nl - dec)%nat).
Proof. intros Hd. rewrite /delta_unl_ent Hd /=. by rewrite lookup_insert. Qed.

Lemma delta_unl_ent_other (av : aview) (d : Z) (nm : fname) (dec : nat)
    (j : Z) :
  j <> d -> delta_unl_ent d nm dec av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_unl_ent.
  destruct (av !! d) as [p |]; [| done].
  destruct (an_node p) as [bs | ents0 | ma mi]; [done | | done].
  by rewrite lookup_insert_ne; [| congruence].
Qed.

Lemma delta_unl_tgt_target (av : aview) (t : Z) (a : anode) :
  av !! t = Some a ->
  delta_unl_tgt t av !! t
  = Some (MkAnode (an_node a) (an_nlink a - 1)%nat).
Proof. intros Ht. rewrite /delta_unl_tgt Ht. by rewrite lookup_insert. Qed.

Lemma delta_unl_tgt_other (av : aview) (t j : Z) :
  j <> t -> delta_unl_tgt t av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_unl_tgt.
  destruct (av !! t) as [a |]; [| done].
  by rewrite lookup_insert_ne; [| congruence].
Qed.

(* ---- the fused delta's row algebra ---------------------------------- *)

Lemma delta_unlink_parent (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a -> d <> t ->
  delta_unlink d nm t av !! d
  = Some (MkAnode (ADir (delete nm ents))
                  (nl - unl_dec (an_node a))%nat).
Proof.
  intros Hd Ht Hne. rewrite /delta_unlink Hd Ht /=.
  rewrite lookup_insert_ne; [| congruence]. by rewrite lookup_insert.
Qed.

Lemma delta_unlink_target (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a ->
  delta_unlink d nm t av !! t
  = Some (MkAnode (an_node a) (an_nlink a - 1)%nat).
Proof.
  intros Hd Ht. rewrite /delta_unlink Hd Ht /=. by rewrite lookup_insert.
Qed.

Lemma delta_unlink_other (av : aview) (d : Z) (nm : fname) (t j : Z) :
  j <> d -> j <> t -> delta_unlink d nm t av !! j = av !! j.
Proof.
  intros Hjd Hjt. rewrite /delta_unlink.
  destruct (av !! d) as [p |]; [| done].
  destruct (av !! t) as [a |]; [| done].
  destruct (an_node p) as [bs | ents0 | ma mi]; [done | | done].
  rewrite lookup_insert_ne; [| congruence].
  by rewrite lookup_insert_ne; [| congruence].
Qed.

(* no key ever leaves: unlink deletes an EDGE, never a node.  [δ_free]
   (the row leaving [aview]) is iput's, at nlink 0 + last reference --
   doc sections 1, 4 and 7. *)
Lemma delta_unlink_is_Some (av : aview) (d : Z) (nm : fname) (t j : Z) :
  is_Some (delta_unlink d nm t av !! j) <-> is_Some (av !! j).
Proof.
  rewrite /delta_unlink.
  destruct (av !! d) as [p |] eqn:Hd; [| done].
  destruct (av !! t) as [a |] eqn:Ht; [| done].
  destruct (an_node p) as [bs | ents0 | ma mi]; [done | | done].
  destruct (decide (j = t)) as [-> | Hjt].
  { rewrite lookup_insert Ht. split; intros _; by eexists. }
  rewrite lookup_insert_ne; [| congruence].
  destruct (decide (j = d)) as [-> | Hjd].
  { rewrite lookup_insert Hd. split; intros _; by eexists. }
  by rewrite lookup_insert_ne; [| congruence].
Qed.

(* ===================================================================== *)
(*  5.  THE UNION                                                        *)
(* ===================================================================== *)

(* THE UNION OF THE WRITE-KIND DELTAS the AU commits fire: what an
   application's license (FsAbsInv.fsabs_lic) is stated over. *)
Definition fs_delta `{XI : CurCtx} (av av' : aview) : Prop :=
  (exists d nm i c, av' = delta_create d nm i c av)
  \/ (exists i, av' = delta_trunc i av)
  \/ (exists i off bs, av' = delta_write i off bs av)
  \/ (exists d nm dec, av' = delta_unl_ent d nm dec av)
  \/ (exists t, av' = delta_unl_tgt t av).
