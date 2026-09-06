(* FsAbsDelta.v -- THE WRITE DELTAS ON [aview]: the five hoisted ones, and
   (round E2, lane E2-D) the LEGS of create and link they decompose into.

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
   one of them ([delta_create_dev], [delta_unlink_split], the last-link
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
   reason.

   ROUND E2, LANE E2-D (2026-09-05; claude-notes/projects/app-round-e2.md
   sections 2(b)-5, briefs file): the fused deltas are what a QUIESCENT
   observer reads; the kernel performs them as LEGS, one retag each, and
   round E's fires commit a leg at a time.  Section 1b mints create's legs
   -- [delta_arm] (the row APPEARS at nlink 1), [delta_unarm] (the failure
   arm's undo: it DISAPPEARS), [delta_dots] (mkdir's dot writes), and
   [delta_ent] (the parent leg, with mkdir's count bump fused) -- and
   [delta_create_split] ties [delta_create] to arm-then-ent.  Section 4b
   mints link's -- [delta_link_tgt] (count up), [delta_link_ent] (the
   parent's new name), [delta_link_untgt] (the failure arm's count down,
   which IS [delta_unl_tgt]) -- and [delta_link] with [delta_link_split].
   THE VIEW IS THE LIVE NAMESPACE (lane E2-V2), so there is no
   [delta_claim] and no [delta_free]: ialloc's claim and iput's free move
   nothing the view has.

   ONE DEVIATION FROM THE BRIEF, forced by the kernel: [delta_link_tgt]
   takes the target's OBSERVED ROW [a] as a parameter instead of reading
   it from the view.  sys_link has no [ip->nlink == 0] guard on its target
   (ProofSysLink.v, "THE IIIc WALL": the walk pays iupdate's freeze-pin
   premise with the freeze token because the count fact is genuinely
   unavailable), so the target may be an unlinked-but-open file -- a row
   the live view does NOT have -- and the bump RESURRECTS it: count 0 -> 1,
   the row appears with the record's content.  A view-only "nlink+1 at t"
   would be the identity there, which is false of the machine.  With [a]
   in hand ([arow_at av t a] is the side condition: present at a nonzero
   count, absent at zero) the delta is one insert in both arms, and
   [delta_link_untgt] -- [delta_unl_tgt], count down and gone at 0 --
   undoes it exactly ([delta_link_untgt_tgt]). *)

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
(*  1b.  CREATE'S LEGS (round E2, lane E2-D)                             *)
(* ===================================================================== *)

(* THE ARM (doc: "nlink 0 -> 1"): the child's row APPEARS, content [c]
   at count 1 -- create's [ip->nlink = 1; iupdate(ip)] after ialloc's
   claim (which the live view does not see: the claim box is at count 0).
   For a device [c] carries the major/minor the two stores before it set;
   for a directory it is [ADir ∅], the dots come with [delta_dots].  Side
   condition, kept out of the function: [av !! i = None] (the inum was
   free or a claim box, either way not in the view). *)
Definition delta_arm (i : Z) (c : absnode) (av : aview) : aview :=
  <[i := MkAnode c 1%nat]> av.

(* THE UNARM (ruling Q-h, the failure arm's [ip->nlink = 0]): the row
   DISAPPEARS.  Total: deleting an absent key is the identity. *)
Definition delta_unarm (i : Z) (av : aview) : aview := delete i av.

(* THE DOTS (mkdir's two [dirlink(ip, ".", ip->inum)] /
   [dirlink(ip, "..", dp->inum)], one retag in the landed proof): the
   directory's entry map gains its two dot names; the count does not move
   ("No ip->nlink++ for '.'").  Total on purpose -- at a non-directory or
   an absent row it is the identity. *)
Definition delta_dots (i d : Z) (av : aview) : aview :=
  match av !! i with
  | Some a =>
      match an_node a with
      | ADir ents =>
          <[i := MkAnode (ADir (<[DOT := i]> (<[DOTDOT := d]> ents))) (an_nlink a)]> av
      | _ => av
      end
  | None => av
  end.

(* THE PARENT LEG (create's [dirlink(dp, name, ip->inum)] fused with
   mkdir's [dp->nlink++] "for '..'"): the parent gains [nm ↦ i] and, if
   the child is a directory, one link.  The child's KIND is read off the
   VIEW -- at this instant the child is armed (in the view at count 1,
   dots included), so [acre_bump] of its row is exactly [delta_create]'s
   bump.  Total: identity unless both rows are there and the parent is a
   directory. *)
Definition delta_ent (d : Z) (nm : fname) (i : Z) (av : aview) : aview :=
  match av !! d, av !! i with
  | Some p, Some a =>
      match an_node p with
      | ADir ents =>
          <[d := MkAnode (ADir (<[nm := i]> ents))
                         (an_nlink p + acre_bump (an_node a))%nat]> av
      | _ => av
      end
  | _, _ => av
  end.

(* ---- the row algebra: [_lookup_at] the moved key, [_lookup_same] the
   others, and each leg's collapse to one insert -------------------- *)

Lemma delta_arm_lookup_at (av : aview) (i : Z) (c : absnode) :
  delta_arm i c av !! i = Some (MkAnode c 1%nat).
Proof. rewrite /delta_arm lookup_insert //. Qed.

Lemma delta_arm_lookup_same (av : aview) (i : Z) (c : absnode) (j : Z) :
  j <> i -> delta_arm i c av !! j = av !! j.
Proof. intros Hj. rewrite /delta_arm lookup_insert_ne //. Qed.

(* the precondition's consequence: an arm at a row the view lacks is
   undone EXACTLY by the unarm -- the failure arm restores the pre-view *)
Lemma delta_arm_unarm (av : aview) (i : Z) (c : absnode) :
  av !! i = None -> delta_unarm i (delta_arm i c av) = av.
Proof.
  intros Hi. rewrite /delta_unarm /delta_arm delete_insert //.
Qed.

(* ...and [i ∉ dom av] is that precondition's [dom] spelling *)
Lemma delta_arm_fresh (av : aview) (i : Z) :
  i ∉ dom av <-> av !! i = None.
Proof. apply not_elem_of_dom. Qed.

Lemma delta_unarm_lookup_at (av : aview) (i : Z) :
  delta_unarm i av !! i = None.
Proof. rewrite /delta_unarm lookup_delete //. Qed.

Lemma delta_unarm_lookup_same (av : aview) (i j : Z) :
  j <> i -> delta_unarm i av !! j = av !! j.
Proof. intros Hj. rewrite /delta_unarm lookup_delete_ne //. Qed.

Lemma delta_dots_dir (av : aview) (i d : Z) (ents : gmap fname Z) (nl : nat) :
  av !! i = Some (MkAnode (ADir ents) nl) ->
  delta_dots i d av
  = <[i := MkAnode (ADir (<[DOT := i]> (<[DOTDOT := d]> ents))) nl]> av.
Proof. intros Hi. rewrite /delta_dots Hi //=. Qed.

Lemma delta_dots_lookup_at (av : aview) (i d : Z) (ents : gmap fname Z) (nl : nat) :
  av !! i = Some (MkAnode (ADir ents) nl) ->
  delta_dots i d av !! i
  = Some (MkAnode (ADir (<[DOT := i]> (<[DOTDOT := d]> ents))) nl).
Proof. intros Hi. rewrite (delta_dots_dir _ _ _ _ _ Hi) lookup_insert //. Qed.

Lemma delta_dots_lookup_same (av : aview) (i d j : Z) :
  j <> i -> delta_dots i d av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_dots.
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node a) as [bs | ents | ma mi]; [done | | done].
  rewrite lookup_insert_ne //.
Qed.

Lemma delta_dots_absent (av : aview) (i d : Z) :
  av !! i = None -> delta_dots i d av = av.
Proof. intros Hi. rewrite /delta_dots Hi //. Qed.

Lemma delta_ent_dir (av : aview) (d : Z) (nm : fname) (i : Z)
    (ents : gmap fname Z) (nl : nat) (c : absnode) (k : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  av !! i = Some (MkAnode c k) ->
  delta_ent d nm i av
  = <[d := MkAnode (ADir (<[nm := i]> ents)) (nl + acre_bump c)%nat]> av.
Proof. intros Hd Hi. rewrite /delta_ent Hd Hi //=. Qed.

Lemma delta_ent_lookup_at (av : aview) (d : Z) (nm : fname) (i : Z)
    (ents : gmap fname Z) (nl : nat) (c : absnode) (k : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  av !! i = Some (MkAnode c k) ->
  delta_ent d nm i av !! d
  = Some (MkAnode (ADir (<[nm := i]> ents)) (nl + acre_bump c)%nat).
Proof.
  intros Hd Hi. rewrite (delta_ent_dir _ _ _ _ _ _ _ _ Hd Hi) lookup_insert //.
Qed.

Lemma delta_ent_lookup_same (av : aview) (d : Z) (nm : fname) (i j : Z) :
  j <> d -> delta_ent d nm i av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_ent.
  destruct (av !! d) as [p |]; [| done].
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node p) as [bs | ents | ma mi]; [done | | done].
  rewrite lookup_insert_ne //.
Qed.

(* the child's own row is untouched by the parent leg *)
Lemma delta_ent_lookup_child (av : aview) (d : Z) (nm : fname) (i : Z) :
  d <> i -> delta_ent d nm i av !! i = av !! i.
Proof. intros Hne. apply delta_ent_lookup_same. congruence. Qed.

(* THE SPLIT (the mold: [delta_unlink_split]): under create's premises --
   the parent is a directory in the view, the child's inum is NOT -- the
   fused [delta_create] IS the arm followed by the parent leg.  (mkdir's
   dots sit between the two and change neither the parent's row nor the
   child's kind, so [delta_create] at [ADir ∅] composes with [delta_dots]
   the same way; the fires state that where they fire it.) *)
Lemma delta_create_split (av : aview) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  av !! i = None ->
  delta_create d nm i c av = delta_ent d nm i (delta_arm i c av).
Proof.
  intros Hd Hi.
  assert (Hne : d <> i) by (intros ->; rewrite Hd in Hi; discriminate Hi).
  rewrite /delta_create Hd /=.
  rewrite (delta_ent_dir _ d nm i ents nl c 1%nat).
  - rewrite /delta_arm. apply insert_commute. congruence.
  - rewrite (delta_arm_lookup_same _ _ _ _ Hne). exact Hd.
  - apply delta_arm_lookup_at.
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

(* a row the view does not have is not written: a write through the fd of
   an UNLINKED file is view-preserving (E2-V2, ruling Q-d) *)
Lemma delta_write_absent (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) :
  av !! i = None -> delta_write i off new av = av.
Proof. intros Hi. rewrite /delta_write Hi //. Qed.

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

(* ...and so is truncating a row the view does not have: O_TRUNC on a
   file unlinked between namei and the open's lock (E2-V2) *)
Lemma delta_trunc_absent `{XI : CurCtx} (av : aview) (i : Z) :
  av !! i = None -> delta_trunc i av = av.
Proof. intros Hi. rewrite /delta_trunc Hi //. Qed.

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

(* instant 2 -- the target's row: same node, count down one, AND GONE WHEN
   THE COUNT REACHES ZERO (E2-V2, ruling Q-d).  The view keeps live rows
   only, so the last unlink DELETES the row, whatever descriptors still
   reach the inode: from here on the file is the fd-holders' private
   buffer, not part of the file system a user can name. *)
Definition delta_unl_tgt (t : Z) (av : aview) : aview :=
  match av !! t with
  | Some a =>
      if decide ((an_nlink a - 1)%nat = 0%nat) then delete t av
      else <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]> av
  | None => av
  end.

(* THE FUSED DELTA (doc section 4's [δ_unlink], the quiescent reading):
   parent loses [nm], target's nlink drops -- and its row leaves when the
   link was its last -- a directory target drops the parent's nlink too.
   [delta_unlink_split] below ties it to the two halves; the AU commits
   fire the halves. *)
Definition delta_unlink (d : Z) (nm : fname) (t : Z)
    (av : aview) : aview :=
  match av !! d with
  | Some p =>
      match av !! t with
      | Some a =>
          match an_node p with
          | ADir ents =>
              if decide ((an_nlink a - 1)%nat = 0%nat)
              then delete t
                     (<[d := MkAnode (ADir (delete nm ents))
                                     (an_nlink p - unl_dec (an_node a))%nat]> av)
              else <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]>
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

(* the target's row after the halves, spelled out: the [match] on the row
   the view has, reduced -- so a consumer can case on the count *)
Lemma delta_unl_tgt_unfold (av : aview) (t : Z) (a : anode) :
  av !! t = Some a ->
  delta_unl_tgt t av
  = (if decide ((an_nlink a - 1)%nat = 0%nat) then delete t av
     else <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]> av).
Proof. intros Ht. rewrite /delta_unl_tgt Ht. reflexivity. Qed.

Lemma delta_unl_tgt_target (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> (2 <= an_nlink a)%nat ->
  delta_unl_tgt t av !! t
  = Some (MkAnode (an_node a) (an_nlink a - 1)%nat).
Proof.
  intros Ht Hnl. rewrite (delta_unl_tgt_unfold av t a Ht).
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)); [lia |].
  by rewrite lookup_insert.
Qed.

(* the LAST link: the row leaves *)
Lemma delta_unl_tgt_last (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> an_nlink a = 1%nat ->
  delta_unl_tgt t av !! t = None.
Proof.
  intros Ht Hnl. rewrite (delta_unl_tgt_unfold av t a Ht).
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)); [| lia].
  by rewrite lookup_delete.
Qed.

Lemma delta_unl_tgt_other (av : aview) (t j : Z) :
  j <> t -> delta_unl_tgt t av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_unl_tgt.
  destruct (av !! t) as [a |]; [| done].
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)).
  - by rewrite lookup_delete_ne; [| congruence].
  - by rewrite lookup_insert_ne; [| congruence].
Qed.

(* ---- the fused delta's row algebra ---------------------------------- *)

(* the fused delta at a parent row and a target row, spelled out *)
Lemma delta_unlink_unfold (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a ->
  delta_unlink d nm t av
  = (if decide ((an_nlink a - 1)%nat = 0%nat)
     then delete t
            (<[d := MkAnode (ADir (delete nm ents))
                            (nl - unl_dec (an_node a))%nat]> av)
     else <[t := MkAnode (an_node a) (an_nlink a - 1)%nat]>
            (<[d := MkAnode (ADir (delete nm ents))
                            (nl - unl_dec (an_node a))%nat]> av)).
Proof. intros Hd Ht. rewrite /delta_unlink Hd Ht. reflexivity. Qed.

Lemma delta_unlink_parent (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a -> d <> t ->
  delta_unlink d nm t av !! d
  = Some (MkAnode (ADir (delete nm ents))
                  (nl - unl_dec (an_node a))%nat).
Proof.
  intros Hd Ht Hne. rewrite (delta_unlink_unfold av d nm ents nl t a Hd Ht).
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)).
  - rewrite lookup_delete_ne; [| congruence]. by rewrite lookup_insert.
  - rewrite lookup_insert_ne; [| congruence]. by rewrite lookup_insert.
Qed.

Lemma delta_unlink_target (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a ->
  (2 <= an_nlink a)%nat ->
  delta_unlink d nm t av !! t
  = Some (MkAnode (an_node a) (an_nlink a - 1)%nat).
Proof.
  intros Hd Ht Hnl. rewrite (delta_unlink_unfold av d nm ents nl t a Hd Ht).
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)); [lia |].
  by rewrite lookup_insert.
Qed.

(* the LAST link: the target's row leaves the view (E2-V2) *)
Lemma delta_unlink_last (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> av !! t = Some a ->
  an_nlink a = 1%nat ->
  delta_unlink d nm t av !! t = None.
Proof.
  intros Hd Ht Hnl. rewrite (delta_unlink_unfold av d nm ents nl t a Hd Ht).
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)); [| lia].
  by rewrite lookup_delete.
Qed.

Lemma delta_unlink_other (av : aview) (d : Z) (nm : fname) (t j : Z) :
  j <> d -> j <> t -> delta_unlink d nm t av !! j = av !! j.
Proof.
  intros Hjd Hjt. rewrite /delta_unlink.
  destruct (av !! d) as [p |]; [| done].
  destruct (av !! t) as [a |]; [| done].
  destruct (an_node p) as [bs | ents0 | ma mi]; [done | | done].
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)).
  - rewrite lookup_delete_ne; [| congruence].
    by rewrite lookup_insert_ne; [| congruence].
  - rewrite lookup_insert_ne; [| congruence].
    by rewrite lookup_insert_ne; [| congruence].
Qed.

(* no key but the TARGET's ever leaves: unlink deletes an EDGE, and the
   target's row only when that edge was its last link (E2-V2; before it,
   [δ_free] was iput's alone -- doc sections 1, 4 and 7). *)
Lemma delta_unlink_is_Some_other (av : aview) (d : Z) (nm : fname) (t j : Z) :
  j <> t ->
  (is_Some (delta_unlink d nm t av !! j) <-> is_Some (av !! j)).
Proof.
  intros Hjt. rewrite /delta_unlink.
  destruct (av !! d) as [p |] eqn:Hd; [| done].
  destruct (av !! t) as [a |] eqn:Ht; [| done].
  destruct (an_node p) as [bs | ents0 | ma mi]; [done | | done].
  destruct (decide ((an_nlink a - 1)%nat = 0%nat)).
  - rewrite lookup_delete_ne; [| congruence].
    destruct (decide (j = d)) as [-> | Hjd].
    { rewrite lookup_insert Hd. split; intros _; by eexists. }
    by rewrite lookup_insert_ne; [| congruence].
  - rewrite lookup_insert_ne; [| congruence].
    destruct (decide (j = d)) as [-> | Hjd].
    { rewrite lookup_insert Hd. split; intros _; by eexists. }
    by rewrite lookup_insert_ne; [| congruence].
Qed.

(* ===================================================================== *)
(*  4b.  LINK (round E2, lane E2-D)                                      *)
(* ===================================================================== *)

(* THE TARGET LEG (sys_link's [ip->nlink++; iupdate(ip)]): the target's
   row at one more link, from the row [a] THE MACHINE READS under
   [ip->lock].  Parameterized by [a] (the header's deviation): the view
   has the row iff its count is nonzero ([arow_at av t a]), and sys_link
   does not check the count, so at a count of zero this leg makes an
   unlinked-but-open file REAPPEAR in the namespace-to-be.  One insert
   either way. *)
Definition delta_link_tgt (t : Z) (a : anode) (av : aview) : aview :=
  <[t := MkAnode (an_node a) (an_nlink a + 1)%nat]> av.

(* THE PARENT LEG (sys_link's [dirlink(dp, name, ip->inum)]): the parent
   gains [nm ↦ t]; link is for files and devices only, so no count moves.
   Total: identity unless the parent is a directory in the view. *)
Definition delta_link_ent (d : Z) (nm : fname) (t : Z) (av : aview) : aview :=
  match av !! d with
  | Some p =>
      match an_node p with
      | ADir ents => <[d := MkAnode (ADir (<[nm := t]> ents)) (an_nlink p)]> av
      | _ => av
      end
  | None => av
  end.

(* THE FAILURE ARM'S UNDO ([bad: ip->nlink--]): one link down, and gone
   at zero -- which is [delta_unl_tgt] on the nose. *)
Definition delta_link_untgt (t : Z) : aview -> aview := delta_unl_tgt t.

(* THE FUSED DELTA (doc section 4's [δ_link]): the target leg, then the
   parent's. *)
Definition delta_link (d : Z) (nm : fname) (t : Z) (a : anode)
    (av : aview) : aview :=
  delta_link_ent d nm t (delta_link_tgt t a av).

(* ---- the row algebra --------------------------------------------- *)

Lemma delta_link_tgt_lookup_at (av : aview) (t : Z) (a : anode) :
  delta_link_tgt t a av !! t = Some (MkAnode (an_node a) (an_nlink a + 1)%nat).
Proof. rewrite /delta_link_tgt lookup_insert //. Qed.

Lemma delta_link_tgt_lookup_same (av : aview) (t : Z) (a : anode) (j : Z) :
  j <> t -> delta_link_tgt t a av !! j = av !! j.
Proof. intros Hj. rewrite /delta_link_tgt lookup_insert_ne //. Qed.

Lemma delta_link_ent_dir (av : aview) (d : Z) (nm : fname) (t : Z)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  delta_link_ent d nm t av = <[d := MkAnode (ADir (<[nm := t]> ents)) nl]> av.
Proof. intros Hd. rewrite /delta_link_ent Hd //=. Qed.

Lemma delta_link_ent_lookup_at (av : aview) (d : Z) (nm : fname) (t : Z)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  delta_link_ent d nm t av !! d = Some (MkAnode (ADir (<[nm := t]> ents)) nl).
Proof. intros Hd. rewrite (delta_link_ent_dir _ _ _ _ _ _ Hd) lookup_insert //. Qed.

Lemma delta_link_ent_lookup_same (av : aview) (d : Z) (nm : fname) (t j : Z) :
  j <> d -> delta_link_ent d nm t av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_link_ent.
  destruct (av !! d) as [p |]; [| done].
  destruct (an_node p) as [bs | ents | ma mi]; [done | | done].
  rewrite lookup_insert_ne //.
Qed.

Lemma delta_link_ent_absent (av : aview) (d : Z) (nm : fname) (t : Z) :
  av !! d = None -> delta_link_ent d nm t av = av.
Proof. intros Hd. rewrite /delta_link_ent Hd //. Qed.

(* THE UNDO IS EXACT: at the row the machine read -- present at a nonzero
   count, absent at zero -- the failure arm's count-down restores the
   pre-view, in both arms.  [arow_at] is the [FsAbsDefs] counted clause. *)
Lemma delta_link_untgt_tgt (av : aview) (t : Z) (a : anode) :
  arow_at av t a -> delta_link_untgt t (delta_link_tgt t a av) = av.
Proof.
  intros Hrow. destruct a as [n k].
  rewrite /delta_link_untgt /delta_link_tgt. cbn [an_node an_nlink].
  erewrite delta_unl_tgt_unfold; [| apply lookup_insert]. cbn [an_node an_nlink].
  destruct (arow_at_cases _ _ _ Hrow) as [[Hz Hnone] | [Hnz Hsome]].
  - cbn [an_nlink] in Hz. case_decide as Hc; [| exfalso; lia].
    rewrite delete_insert; [reflexivity | exact Hnone].
  - cbn [an_nlink] in Hnz. case_decide as Hc; [exfalso; lia |].
    rewrite insert_insert. replace (k + 1 - 1)%nat with k by lia.
    apply insert_id. exact Hsome.
Qed.

(* THE SPLIT, spelled out: under link's premises -- the parent is a
   directory in the view and is not the target -- the fused delta is the
   two inserts. *)
Lemma delta_link_split (av : aview) (d : Z) (nm : fname) (t : Z) (a : anode)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) -> d <> t ->
  delta_link d nm t a av
  = <[d := MkAnode (ADir (<[nm := t]> ents)) nl]>
      (<[t := MkAnode (an_node a) (an_nlink a + 1)%nat]> av).
Proof.
  intros Hd Hne. rewrite /delta_link.
  rewrite (delta_link_ent_dir _ d nm t ents nl); [reflexivity |].
  rewrite (delta_link_tgt_lookup_same _ _ _ _ Hne). exact Hd.
Qed.

Lemma delta_link_parent (av : aview) (d : Z) (nm : fname) (t : Z) (a : anode)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) -> d <> t ->
  delta_link d nm t a av !! d = Some (MkAnode (ADir (<[nm := t]> ents)) nl).
Proof.
  intros Hd Hne. rewrite (delta_link_split _ _ _ _ _ _ _ Hd Hne) lookup_insert //.
Qed.

Lemma delta_link_target (av : aview) (d : Z) (nm : fname) (t : Z) (a : anode)
    (ents : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir ents) nl) -> d <> t ->
  delta_link d nm t a av !! t = Some (MkAnode (an_node a) (an_nlink a + 1)%nat).
Proof.
  intros Hd Hne. rewrite (delta_link_split _ _ _ _ _ _ _ Hd Hne).
  rewrite lookup_insert_ne; [| exact Hne]. rewrite lookup_insert //.
Qed.

Lemma delta_link_other (av : aview) (d : Z) (nm : fname) (t : Z) (a : anode) (j : Z) :
  j <> d -> j <> t -> delta_link d nm t a av !! j = av !! j.
Proof.
  intros Hjd Hjt. rewrite /delta_link.
  rewrite (delta_link_ent_lookup_same _ _ _ _ _ Hjd).
  exact (delta_link_tgt_lookup_same _ _ _ _ Hjt).
Qed.

(* ===================================================================== *)
(*  5.  THE UNION                                                        *)
(* ===================================================================== *)

(* THE UNION OF THE WRITE-KIND DELTAS the AU commits fire: what an
   application's license (FsAbsInv.fsabs_lic) is stated over.  Round E2
   added the legs (section 1b, 4b); the fused forms stay for the
   quiescent readers.  [delta_link_untgt] is [delta_unl_tgt] and needs no
   disjunct of its own. *)
Definition fs_delta `{XI : CurCtx} (av av' : aview) : Prop :=
  (exists d nm i c, av' = delta_create d nm i c av)
  \/ (exists i, av' = delta_trunc i av)
  \/ (exists i off bs, av' = delta_write i off bs av)
  \/ (exists d nm dec, av' = delta_unl_ent d nm dec av)
  \/ (exists t, av' = delta_unl_tgt t av)
  \/ (exists i c, av' = delta_arm i c av)
  \/ (exists i, av' = delta_unarm i av)
  \/ (exists i d, av' = delta_dots i d av)
  \/ (exists d nm i, av' = delta_ent d nm i av)
  \/ (exists t a, av' = delta_link_tgt t a av)
  \/ (exists d nm t, av' = delta_link_ent d nm t av).
