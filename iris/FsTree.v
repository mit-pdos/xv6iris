(* ======================================================================= *)
(*  FsTree.v -- THE PURE TREE LAYER: an inum-keyed node store, the          *)
(*  bytes-to-tree reading of a directory, and path lookup.                  *)
(*  design: claude-notes/design/fs-fragments.md §1 (rulings R1, R2)         *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS, AND WHAT IT IS NOT.

    This is the FRAGMENT CAMPAIGN's F1a increment: the pure, resource-free
    vocabulary in which "the file system's shape" can be said at all.  It
    introduces no [iProp], no ghost name and no authority; [FsRep.v] one
    level up is where the reading becomes a resource.  [DirView.v] is the
    precedent for both the placement and the style -- a pure record view
    that imports [InodeInv] only for [file_byte], with no proofmode
    reasoning anywhere below.

    ---- THE TYPE IS A STORE PLUS A ROOT, NOT AN INDUCTIVE TREE (R1) ------

    [fstree] is a [gmap Z fsnode] keyed by INUM plus a distinguished root.
    Four things force that shape and none of them is a preference:

      1. every landed inum-indexed resource is [Z]-keyed
         ([InodeRegion.dinode_at] is a [ghost_map Z dinode] element,
         [Xv6Cameras.linkUR] is a [gmapUR Z _]), so a path-keyed abstract
         state would need a coercion at every one of them;
      2. hard links make files MULTI-PARENT, so an inductive [Tree] is
         already wrong at the leaves -- the object is a DAG;
      3. [".."] has to be IN [ents] rather than derived: the on-disk
         records are keyed by record INDEX, and nothing in the model places
         [".."] at index 1 (fs-icache.md §20.17.4(b));
      4. xv6 has no rename, so the only shape movers are insert-edge and
         delete-edge -- there is no tree surgery to be structural about.

    "Directories form a tree" is therefore a DERIVED, SEPARABLE predicate
    ([fs_dirs_acyclic] below), never a property of the type.  Nothing
    landed needs it; keeping it separable means no mover has to
    re-establish it.

    PATHS ADD NO NEW DATATYPE.  [PathElems.path_elems] is already the
    name-sequence vocabulary and [DirentEnc.bname 14] is already the
    canonical name, so [fname] is a definitional abbreviation and
    [path_at] is one [foldl].

    ---- THE ABSTRACTION RELATION'S ONE TRAP: DUPLICATE NAMES (R2) --------

    **xv6's on-disk format PERMITS two live records with the same name,
    and [dirlookup] returns the FIRST ([DirView.dir_first]).  A [gmap fname
    Z] therefore loses information the format admits, and a naive fold
    over the live records is WRONG -- it would model the LAST record, i.e.
    the one dirlookup never returns.**  [dir_view] below is defined so
    that the k-th record contributes only when it WINS its own name
    ([dir_wins]), and [dir_view_lookup] is the theorem that the resulting
    map is exactly dirlookup's answer at every name.  The relation is
    used ONE-DIRECTIONALLY, bytes -> tree, never tree -> bytes.

    ---- ...AND WHY UNIQUENESS IS CARRIED AS AN INVARIANT ANYWAY ----------

    First-match keeps [dir_view] TOTAL on every byte state, with no
    definedness side conditions -- which is why it stays the definition.
    But first-match alone leaves a real hole, THE UNMASKING ARGUMENT:
    zeroing the first record of a duplicated name leaves the name still
    mapped, to a DIFFERENT inum, so the tree delta of an unlink is not
    [delete name] and sys_unlink's friendly spec would be FALSE.

    So name uniqueness is carried as an INVARIANT ([dir_names_unique]),
    per-directory and over live records only.  xv6 cannot reach a
    duplicate-name state: every insertion goes through [dirlink], which
    refuses a present name under the caller's directory lock, and
    [SpecDirlink] already exposes the maintenance fact on both arms.
    Under the invariant [dir_view] is the exact ANY-match map
    ([dir_view_live]) and record-zeroing commutes with [delete]
    ([dir_view_zero]).  Those two are what F3's unlink triple rests on.

    ---- THE ONE REAL PROOF OBLIGATION -----------------------------------

    [node_rep_inj]: the tree is a FUNCTION of the bytes, so [fs_rep] is
    determinate.  It is the analogue of [InodeRegion.diblk_bytes_inj], and
    it is proved here in its sharpest form -- [node_rep_node_of], "any
    node representing (dn, data) IS [node_of dn data]".                    *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeDefs.
Require Import DirView.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  NAMES                                                              *)
(* ====================================================================== *)

(* A directory entry's name is exactly what [namecmp] compares and what
   [dirlookup] matches on: [DirentEnc.bname 14] of the record's name
   bytes.  Definitionally [list (bv 8)], which is also
   [PathElems.path_elems]'s element type -- so a path is a [list fname]
   with no coercion anywhere. *)
Definition fname := list (bv 8).

Global Instance fname_eq_dec : EqDecision fname := _.
Global Instance fname_countable : Countable fname := _.

(* The two names xv6 gives every directory.  [DOT] is the self-record xv6
   deliberately does not count ("No ip->nlink++ for '.'"), and [DOTDOT] is
   the parent link whose LOCATION the model has no fact about -- see
   [FsRep.v]'s [fnode_dotdot], which is the whole reason this layer pays
   for itself.

   S7 MAY SHARPEN THIS (R1).  Whether the tree records [".."] explicitly
   or derives it is decided by whichever fragment sys_unlink's grey
   conversion consumes, and sys_unlink does not exist.  Until then [".."]
   is an ordinary entry of [ents], for reason 3 in the header. *)
Definition DOT : fname := [(mword_of_int 46 : mword 8)].
Definition DOTDOT : fname :=
  [(mword_of_int 46 : mword 8); (mword_of_int 46 : mword 8)].

(* ====================================================================== *)
(*  2.  THE NODE STORE                                                     *)
(* ====================================================================== *)

(* A node is either a file's CONTENT BYTES or a directory's NAME MAP.
   Device nodes are [NFile []] -- their size is zero and they have no data;
   the type halfword distinguishing T_FILE from T_DEVICE is the dinode's
   business, not the tree's. *)
Inductive fsnode :=
| NFile (bs : list (bv 8))
| NDir  (ents : gmap fname Z).

Record fstree := MkTree { fs_nodes : gmap Z fsnode; fs_root : Z }.

(* ====================================================================== *)
(*  3.  THE BYTES -> TREE READING OF ONE DIRECTORY                         *)
(* ====================================================================== *)

(* the k-th record's canonical name *)
Definition dir_bname (data : nat -> list (bv 8)) (k : nat) : fname :=
  bname 14 (dir_name data k).

(* THE FIRST-MATCH FILTER, AND IT IS [nrec]-FREE.  Record [k] contributes
   to the view exactly when it is LIVE and no EARLIER record carries its
   name -- which is precisely "[k] is what [dirlookup] would return for
   [dir_bname data k]", at any record count above [k] ([dir_first_wins]).
   Being independent of [nrec] is what makes [dir_view_S] a one-step
   recursion and hence [dir_view_lookup] an ordinary induction. *)
Definition dir_wins (data : nat -> list (bv 8)) (k : nat) : bool :=
  dir_liveb data k && bool_decide (dir_first data k (dir_bname data k) = None).

Definition dir_entry (data : nat -> list (bv 8)) (k : nat)
  : option (fname * Z) :=
  if dir_wins data k
  then Some (dir_bname data k, bv_unsigned (dir_inum data k))
  else None.

(* THE ABSTRACTION RELATION, FIRST-MATCH-WINS.  Total on every byte state:
   no well-formedness premise, no definedness side condition.  Used
   ONE-DIRECTIONALLY (bytes -> tree) -- there is no inverse and there must
   not be one, because the format carries strictly more information than
   the map does. *)
Definition dir_view (data : nat -> list (bv 8)) (nrec : nat) : gmap fname Z :=
  list_to_map (omap (dir_entry data) (seq 0 nrec)).

(* ---- [dir_wins] against [dir_first] ---------------------------------- *)

Lemma dir_wins_true (data : nat -> list (bv 8)) (k : nat) :
  dir_wins data k = true
  <-> (dir_live data k /\ dir_first data k (dir_bname data k) = None).
Proof.
  unfold dir_wins. rewrite andb_true_iff. rewrite dir_liveb_true.
  rewrite bool_decide_eq_true. reflexivity.
Qed.

Lemma dir_wins_live (data : nat -> list (bv 8)) (k : nat) :
  dir_wins data k = true -> dir_live data k.
Proof. intros H. exact (proj1 (proj1 (dir_wins_true data k) H)). Qed.

Lemma dir_first_wins (data : nat -> list (bv 8)) (nrec k : nat) :
  (k < nrec)%nat ->
  (dir_first data nrec (dir_bname data k) = Some k <-> dir_wins data k = true).
Proof.
  intros Hk. rewrite dir_wins_true. split.
  - intros H. apply dir_first_Some in H. destruct H as (_ & [Hl _] & Hbelow).
    split; [exact Hl |]. apply dir_first_None. exact Hbelow.
  - intros [Hl Hnone]. apply dir_first_Some. split; [exact Hk | split].
    + split; [exact Hl | reflexivity].
    + apply dir_first_None. exact Hnone.
Qed.

(* ---- the one-step recursion, and THE theorem -------------------------- *)

Lemma dir_first_S (data : nat -> list (bv 8)) (n : nat) (s : fname) :
  dir_first data (S n) s
  = match dir_first data n s with
    | Some k => Some k
    | None => if dir_matchb data n s then Some n else None
    end.
Proof. unfold dir_first. apply dfirst_S. Qed.

Lemma dir_view_nil (data : nat -> list (bv 8)) : dir_view data 0 = ∅.
Proof. reflexivity. Qed.

Lemma dir_view_S (data : nat -> list (bv 8)) (n : nat) :
  dir_view data (S n)
  = dir_view data n
    ∪ (if dir_wins data n
       then <[dir_bname data n := bv_unsigned (dir_inum data n)]> ∅
       else ∅).
Proof.
  unfold dir_view. rewrite seq_S.
  replace (0 + n)%nat with n by lia.
  rewrite omap_app. rewrite list_to_map_app. f_equal.
  cbn [omap list_omap list_to_map]. unfold dir_entry.
  destruct (dir_wins data n); cbn [list_omap list_to_map]; reflexivity.
Qed.

(* the union at one key, with both sides already constructors -- stated
   separately so the induction below never has to reduce an option union
   whose right operand is a stuck lookup *)
Lemma dir_view_S_lookup (data : nat -> list (bv 8)) (n : nat) (s : fname) :
  dir_view data (S n) !! s
  = match dir_view data n !! s with
    | Some z => Some z
    | None => if dir_wins data n && bool_decide (dir_bname data n = s)
              then Some (bv_unsigned (dir_inum data n))
              else None
    end.
Proof.
  rewrite dir_view_S. rewrite lookup_union.
  destruct (dir_wins data n) eqn:Hw; cbn [andb].
  - destruct (decide (dir_bname data n = s)) as [Heq | Hne].
    + rewrite (bool_decide_eq_true_2 (dir_bname data n = s) Heq).
      rewrite Heq. rewrite lookup_insert.
      destruct (dir_view data n !! s) as [z |]; reflexivity.
    + rewrite lookup_insert_ne by exact Hne. rewrite lookup_empty.
      rewrite (bool_decide_eq_false_2 (dir_bname data n = s) Hne).
      destruct (dir_view data n !! s) as [z |]; reflexivity.
  - rewrite lookup_empty.
    destruct (dir_view data n !! s) as [z |]; reflexivity.
Qed.

(* **THE ABSTRACTION THEOREM.**  The view's answer at every name IS
   [dirlookup]'s answer -- the inum of the FIRST matching record, and
   nothing at all when no record matches.  Every other law about
   [dir_view] below is read off this one. *)
Lemma dir_view_lookup (data : nat -> list (bv 8)) (nrec : nat) (s : fname) :
  dir_view data nrec !! s
  = (fun k => bv_unsigned (dir_inum data k)) <$> dir_first data nrec s.
Proof.
  induction nrec as [| n IH].
  - reflexivity.
  - rewrite dir_view_S_lookup. rewrite IH. rewrite dir_first_S.
    destruct (dir_first data n s) as [k |] eqn:Hf;
      cbn [fmap option_fmap option_map]; [reflexivity |].
    destruct (dir_matchb data n s) eqn:Hm.
    + assert (Hmm : dir_match data n s) by (apply dir_matchb_true; exact Hm).
      destruct Hmm as [Hlive Hname].
      assert (Hw : dir_wins data n = true).
      { apply dir_wins_true. split; [exact Hlive |].
        unfold dir_bname. rewrite Hname. exact Hf. }
      rewrite Hw. cbn [andb].
      rewrite (bool_decide_eq_true_2 (dir_bname data n = s)).
      2:{ unfold dir_bname. exact Hname. }
      reflexivity.
    + destruct (dir_wins data n) eqn:Hw; cbn [andb]; [| reflexivity].
      assert (Hne : dir_bname data n <> s).
      { intros Heq. apply dir_wins_true in Hw. destruct Hw as [Hl _].
        assert (Hmt : dir_match data n s).
        { split; [exact Hl |]. rewrite <- Heq. reflexivity. }
        apply dir_matchb_true in Hmt. rewrite Hmt in Hm. discriminate. }
      rewrite (bool_decide_eq_false_2 (dir_bname data n = s) Hne).
      reflexivity.
Qed.

Lemma dir_view_lookup_Some (data : nat -> list (bv 8)) (nrec : nat)
    (s : fname) (z : Z) :
  dir_view data nrec !! s = Some z
  <-> (exists k : nat, dir_first data nrec s = Some k
                       /\ bv_unsigned (dir_inum data k) = z).
Proof.
  rewrite dir_view_lookup. split.
  - intros H. destruct (dir_first data nrec s) as [k |]; [| discriminate].
    exists k. split; [reflexivity |]. cbn in H. congruence.
  - intros (k & Hk & Hz). rewrite Hk. cbn. congruence.
Qed.

Lemma dir_view_lookup_None (data : nat -> list (bv 8)) (nrec : nat)
    (s : fname) :
  dir_view data nrec !! s = None <-> dir_first data nrec s = None.
Proof.
  rewrite dir_view_lookup.
  destruct (dir_first data nrec s) as [k |];
    cbn [fmap option_fmap option_map]; split; intros H;
    solve [ discriminate | reflexivity ].
Qed.

Lemma dir_view_lookup_None_match (data : nat -> list (bv 8)) (nrec : nat)
    (s : fname) :
  dir_view data nrec !! s = None
  <-> (forall k : nat, (k < nrec)%nat -> ~ dir_match data k s).
Proof. rewrite dir_view_lookup_None. apply dir_first_None. Qed.

(* every entry of the view comes from a live record inside the count *)
Lemma dir_view_lookup_rec (data : nat -> list (bv 8)) (nrec : nat)
    (s : fname) (z : Z) :
  dir_view data nrec !! s = Some z ->
  exists k : nat, (k < nrec)%nat /\ dir_live data k /\ dir_bname data k = s
                  /\ bv_unsigned (dir_inum data k) = z.
Proof.
  intros H. apply dir_view_lookup_Some in H. destruct H as (k & Hk & Hz).
  exists k. split; [exact (dir_first_lt _ _ _ _ Hk) |].
  split; [exact (dir_first_live _ _ _ _ Hk) |].
  split; [exact (dir_first_name _ _ _ _ Hk) | exact Hz].
Qed.

(* ====================================================================== *)
(*  3bis.  THE LOOKUP FACTS AT A BARE VIEW EQUATION                        *)
(*         (namei-pinned-lookup.md §9.2, the N-2 probe verdict)            *)
(* ====================================================================== *)

(*  WHY THESE EXIST BESIDE [FsLookup]'s [node_lookup_*].  Those five facts
    take [node_rep (NDir ents) dn data] -- a THREE-way bundle whose second
    conjunct is [dir_names_unique] -- and every one of their proofs opens
    with [intros (_ & _ & ->)], discarding the type tag and the uniqueness
    invariant UNREAD.  The pinned-lookup campaign's carrier
    ([DirViewG.dv_hold z (dv_of dn data)]) holds only the THIRD conjunct:
    the abstract map IS the byte view, with no well-formedness attached.

    So the family below is the same five statements with the hypothesis
    weakened to the bare equation [ents = dir_view data nrec] and [nrec]
    generalised from a record's own count to an arbitrary one.  Nothing is
    lost: [dir_view_lookup] above is itself uniqueness-free and total on
    every byte state, and it is the only thing any of these consult.  The
    ONE reading that genuinely needs uniqueness is the ANY-match VALUE
    reading [dir_view_live] below -- see [dv_lookup_live_is_Some] for the
    strongest uniqueness-free residue of it, and [dv_live_value_shadowed]
    for the failure itself.                                                *)

(* **THE MASTER EQUATION** -- [dir_view_lookup] read through the caller's
   own name for the map. *)
Lemma dv_lookup_first (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec : nat) (s : fname) :
  ents = dir_view data nrec ->
  ents !! s
  = (fun k => bv_unsigned (dir_inum data k)) <$> dir_first data nrec s.
Proof. intros ->. apply dir_view_lookup. Qed.

(* THE FOUND ARM.  The scan stopped at record [k]; the map answers with
   that record's inum. *)
Lemma dv_lookup_found (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec : nat) (s : fname) (k : nat) :
  ents = dir_view data nrec ->
  dir_first data nrec s = Some k ->
  ents !! s = Some (bv_unsigned (dir_inum data k)).
Proof.
  intros Hv Hf. rewrite (dv_lookup_first ents data nrec s Hv).
  rewrite Hf. reflexivity.
Qed.

(* THE MISS ARM.  The scan ran off the end; the name is not in the map. *)
Lemma dv_lookup_none (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec : nat) (s : fname) :
  ents = dir_view data nrec ->
  dir_first data nrec s = None ->
  ents !! s = None.
Proof.
  intros Hv Hf. rewrite (dv_lookup_first ents data nrec s Hv).
  rewrite Hf. reflexivity.
Qed.

(* ---- and BOTH converses, which is the point: the reading is an
   EQUIVALENCE even with uniqueness gone.  A caller that knows the map can
   predict the scan.  (Bytes -> tree remains the only DEFINITIONAL
   direction; these are theorems about a map that is already a view.) ---- *)

Lemma dv_lookup_none_inv (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec : nat) (s : fname) :
  ents = dir_view data nrec ->
  ents !! s = None ->
  dir_first data nrec s = None.
Proof.
  intros Hv H. rewrite (dv_lookup_first ents data nrec s Hv) in H.
  destruct (dir_first data nrec s) as [k |];
    cbn [fmap option_fmap option_map] in H; [discriminate | reflexivity].
Qed.

Lemma dv_lookup_some_inv (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec : nat) (s : fname) (z : Z) :
  ents = dir_view data nrec ->
  ents !! s = Some z ->
  exists k : nat,
    dir_first data nrec s = Some k
    /\ (k < nrec)%nat /\ dir_live data k /\ dir_bname data k = s
    /\ bv_unsigned (dir_inum data k) = z.
Proof.
  intros Hv H. rewrite (dv_lookup_first ents data nrec s Hv) in H.
  destruct (dir_first data nrec s) as [k |] eqn:Hf;
    cbn [fmap option_fmap option_map] in H; [| discriminate].
  exists k.
  split; [reflexivity |].
  split; [exact (dir_first_lt _ _ _ _ Hf) |].
  split; [exact (dir_first_live _ _ _ _ Hf) |].
  split; [exact (dir_first_name _ _ _ _ Hf) | congruence].
Qed.

(* THE UNIQUENESS-FREE RESIDUE OF [dir_view_live]: MEMBERSHIP SURVIVES.
   A live record inside the count always puts its name in the view's
   domain -- what it cannot promise, without uniqueness, is that the value
   found there is ITS inum. *)
Lemma dv_lookup_live_is_Some (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec k : nat) (s : fname) :
  ents = dir_view data nrec ->
  (k < nrec)%nat -> dir_live data k -> dir_bname data k = s ->
  is_Some (ents !! s).
Proof.
  intros -> Hk Hl Hn.
  destruct (dir_view data nrec !! s) as [z |] eqn:Hlk; [by eexists |].
  exfalso.
  pose proof (proj1 (dir_view_lookup_None_match data nrec s) Hlk) as Hno.
  apply (Hno k Hk). split; [exact Hl | exact Hn].
Qed.

(* ...and THE FAILURE ITSELF.  If the scan's first hit is [k0] but the
   record in hand is [k1] with a different inum, the view does NOT answer
   with the latter -- so [dir_view_live] is unprovable without a hypothesis
   ruling this configuration out, and [dir_names_unique] is that
   hypothesis.  ([k0 <> k1] is a consequence, not an assumption.) *)
Lemma dv_live_value_shadowed (ents : gmap fname Z)
    (data : nat -> list (bv 8)) (nrec k0 k1 : nat) (s : fname) :
  ents = dir_view data nrec ->
  dir_first data nrec s = Some k0 ->
  (k1 < nrec)%nat -> dir_live data k1 -> dir_bname data k1 = s ->
  bv_unsigned (dir_inum data k1) <> bv_unsigned (dir_inum data k0) ->
  ents !! s <> Some (bv_unsigned (dir_inum data k1)).
Proof.
  intros Hv Hf _ _ _ Hne Habs.
  rewrite (dv_lookup_found ents data nrec s k0 Hv Hf) in Habs.
  apply Hne. injection Habs. intros H. exact (eq_sym H).
Qed.

(* ====================================================================== *)
(*  4.  THE NAME-UNIQUENESS INVARIANT (R2)                                 *)
(* ====================================================================== *)

(* PURE, PER-DIRECTORY, OVER LIVE RECORDS ONLY.  Free records carry
   whatever bytes the last deletion left and are deliberately unconstrained
   -- xv6 zeroes only the inum halfword, so a dead record's NAME bytes
   survive its deletion and two dead records may well share a name. *)
Definition dir_names_unique (data : nat -> list (bv 8)) (nrec : nat) : Prop :=
  forall j k : nat, (j < nrec)%nat -> (k < nrec)%nat ->
    dir_live data j -> dir_live data k ->
    dir_bname data j = dir_bname data k -> j = k.

Lemma dir_names_unique_le (data : nat -> list (bv 8)) (n m : nat) :
  (n <= m)%nat -> dir_names_unique data m -> dir_names_unique data n.
Proof. intros Hle Hu j k Hj Hk. apply Hu; lia. Qed.

(* **UNDER THE INVARIANT, [dir_view] IS THE EXACT ANY-MATCH MAP.**  Every
   live record appears, at its own inum -- not merely the first one of its
   name.  This is the half of R2 that makes the tree a faithful reading
   rather than a lossy one. *)
Lemma dir_view_live (data : nat -> list (bv 8)) (nrec k : nat) :
  dir_names_unique data nrec -> (k < nrec)%nat -> dir_live data k ->
  dir_view data nrec !! dir_bname data k = Some (bv_unsigned (dir_inum data k)).
Proof.
  intros Hu Hk Hl. rewrite dir_view_lookup.
  destruct (dir_first data nrec (dir_bname data k)) as [k' |] eqn:Hf.
  - assert (Hk' : k' = k).
    { apply dir_first_Some in Hf. destruct Hf as (Hlt & [Hlv Hnm] & _).
      apply (Hu k' k Hlt Hk Hlv Hl). exact Hnm. }
    rewrite Hk'. reflexivity.
  - exfalso.
    apply (proj1 (dir_first_None data nrec (dir_bname data k)) Hf k Hk).
    split; [exact Hl | reflexivity].
Qed.

(* ====================================================================== *)
(*  5.  RECORD-ZEROING, AND THE TREE DELTA OF AN UNLINK                    *)
(* ====================================================================== *)

(* What sys_unlink's [memset(&de,0,sizeof(de)); writei(...)] leaves behind,
   said at the record view rather than at the bytes: slot [k0]'s inum
   halfword is zero (so the record is dead) and no other record's inum or
   name moved.  [dir_zeroed_of_bytes] builds it from the byte-range clause
   writei's postcondition actually delivers. *)
Definition dir_zeroed_at (data data' : nat -> list (bv 8)) (k0 : nat) : Prop :=
  dir_inum data' k0 = bv_0 16
  /\ (forall q : nat, q <> k0 -> dir_inum data' q = dir_inum data q)
  /\ (forall q : nat, q <> k0 -> dir_bname data' q = dir_bname data q).

Lemma dir_zeroed_of_bytes (data data' : nat -> list (bv 8))
    (k0 tot : nat) (d : dirent) :
  (2 <= tot)%nat -> (tot <= 16)%nat ->
  de_inum d = bv_0 16 ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes d !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_zeroed_at data data' k0.
Proof.
  intros Ht2 Ht16 Hz Hrng.
  assert (Hout : forall q x : nat, q <> k0 -> (16 * q <= x)%nat ->
                   (x < 16 * q + 16)%nat -> file_byte data' x = file_byte data x).
  { intros q x Hq Hlo Hhi. rewrite (Hrng x).
    rewrite decide_False; [reflexivity | intros [H1 H2]; lia]. }
  split; [| split].
  - rewrite (dir_inum_of_two data' k0 d); [exact Hz |].
    intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
    rewrite decide_True; [| lia].
    replace (16 * k0 + j - 16 * k0)%nat with j by lia. reflexivity.
  - intros q Hq. unfold dir_inum.
    rewrite (Hout q (16 * q)%nat Hq ltac:(lia) ltac:(lia)).
    rewrite (Hout q (16 * q + 1)%nat Hq ltac:(lia) ltac:(lia)).
    reflexivity.
  - intros q Hq. unfold dir_bname. apply bname_ext. intros j Hj.
    unfold dir_name. apply (Hout q (16 * q + 2 + j)%nat Hq); lia.
Qed.

Lemma dir_zeroed_dead (data data' : nat -> list (bv 8)) (k0 : nat) :
  dir_zeroed_at data data' k0 -> ~ dir_live data' k0.
Proof. intros (H & _ & _) Hl. exact (Hl H). Qed.

(* uniqueness is preserved trivially: zeroing only REMOVES a live name *)
Lemma dir_names_unique_zero (data data' : nat -> list (bv 8))
    (nrec k0 : nat) :
  dir_zeroed_at data data' k0 ->
  dir_names_unique data nrec -> dir_names_unique data' nrec.
Proof.
  intros (Hz & Hinum & Hname) Hu j k Hj Hk Hlj Hlk Heq.
  assert (Hjk0 : j <> k0) by (intros ->; exact (Hlj Hz)).
  assert (Hkk0 : k <> k0) by (intros ->; exact (Hlk Hz)).
  apply Hu; try assumption.
  - unfold dir_live. rewrite <- (Hinum j Hjk0). exact Hlj.
  - unfold dir_live. rewrite <- (Hinum k Hkk0). exact Hlk.
  - rewrite <- (Hname j Hjk0). rewrite <- (Hname k Hkk0). exact Heq.
Qed.

(* the matchb pointwise comparison the two [dfirst_ext] uses below need *)
Lemma dir_zeroed_matchb (data data' : nat -> list (bv 8))
    (k0 : nat) (s : fname) (q : nat) :
  dir_zeroed_at data data' k0 -> q <> k0 ->
  dir_matchb data' q s = dir_matchb data q s.
Proof.
  intros (_ & Hinum & Hname) Hq.
  unfold dir_matchb, dir_liveb, dir_freeb.
  rewrite (Hinum q Hq).
  replace (bname 14 (dir_name data' q)) with (dir_bname data' q) by reflexivity.
  replace (bname 14 (dir_name data q)) with (dir_bname data q) by reflexivity.
  rewrite (Hname q Hq). reflexivity.
Qed.

(* **THE TREE DELTA OF AN UNLINK, AND WHY THE INVARIANT IS LOAD-BEARING.**
   Under [dir_names_unique] the zeroed record's name leaves the view
   outright.  WITHOUT the invariant this is FALSE: a hidden duplicate
   behind the zeroed record is UNMASKED and the name stays mapped, to a
   different inum.  That is the whole reason R2 amended the first-match
   dodge into an invariant. *)
Lemma dir_view_zero (data data' : nat -> list (bv 8)) (nrec k0 : nat) :
  dir_names_unique data nrec ->
  (k0 < nrec)%nat -> dir_live data k0 ->
  dir_zeroed_at data data' k0 ->
  dir_view data' nrec = delete (dir_bname data k0) (dir_view data nrec).
Proof.
  intros Hu Hk0 Hl0 Hzer.
  pose proof Hzer as (Hz & Hinum & Hname).
  apply map_eq. intros s.
  destruct (decide (s = dir_bname data k0)) as [-> | Hne].
  - (* the deleted name: NOTHING is left matching it *)
    rewrite lookup_delete.
    apply dir_view_lookup_None_match. intros k Hk [Hlk Hnk].
    assert (Hkk0 : k <> k0) by (intros ->; exact (Hlk Hz)).
    assert (Hlk' : dir_live data k)
      by (unfold dir_live; rewrite <- (Hinum k Hkk0); exact Hlk).
    apply Hkk0. apply (Hu k k0 Hk Hk0 Hlk' Hl0).
    rewrite <- (Hname k Hkk0). exact Hnk.
  - (* every other name: the first-match search is unmoved *)
    rewrite lookup_delete_ne by congruence.
    rewrite !dir_view_lookup.
    assert (Hfirst : dir_first data' nrec s = dir_first data nrec s).
    { unfold dir_first. apply dfirst_ext. intros j Hj.
      destruct (decide (j = k0)) as [-> | Hjk].
      - assert (H1 : dir_matchb data' k0 s = false).
        { apply dir_matchb_false. intros [Hlv _].
          exact (dir_zeroed_dead data data' k0 Hzer Hlv). }
        assert (H2 : dir_matchb data k0 s = false).
        { apply dir_matchb_false. intros [_ Hnm]. apply Hne.
          rewrite <- Hnm. reflexivity. }
        rewrite H1, H2. reflexivity.
      - exact (dir_zeroed_matchb data data' k0 s j Hzer Hjk). }
    rewrite Hfirst.
    destruct (dir_first data nrec s) as [k |] eqn:Hf; [| reflexivity].
    assert (Hkk0 : k <> k0).
    { intros ->. apply Hne. rewrite <- (dir_first_name _ _ _ _ Hf). reflexivity. }
    cbn. rewrite (Hinum k Hkk0). reflexivity.
Qed.

(* ====================================================================== *)
(*  6.  A NODE'S READING OFF ITS RECORD AND ITS BYTES                      *)
(* ====================================================================== *)

(* a file's content: the first [size] bytes of its data *)
Definition file_bytes (data : nat -> list (bv 8)) (n : nat) : list (bv 8) :=
  file_byte data <$> seq 0 n.

(* THE READING, AND IT IS A FUNCTION.  [node_of] is bytes -> tree spelled
   out; [node_rep] is the relation, which exists so that a resource can
   carry it as a [⌜⌝] conjunct without committing to the [decide]. *)
Definition node_of (dn : dinode) (data : nat -> list (bv 8)) : fsnode :=
  if decide (bv_unsigned (di_type dn) = T_DIR_z)
  then NDir (dir_view data (dir_nrec (bv_unsigned (di_size dn))))
  else NFile (file_bytes data (Z.to_nat (bv_unsigned (di_size dn)))).

(* [node_rep n dn data]: the abstract node [n] IS what the on-disk record
   [dn] and the payload bytes [data] say.

   THE NDir CASE CARRIES [dir_names_unique] (R2).  It rides here rather
   than in a separate conjunct because it is exactly the premise
   [dir_view_zero] needs, and because a directory that has lost it is not
   a directory this layer can talk about at all.

   A node is ALLOCATED by construction: [NFile] demands a nonzero type, so
   a free record represents no node and the tree never contains one. *)
Definition node_rep (n : fsnode) (dn : dinode) (data : nat -> list (bv 8))
  : Prop :=
  match n with
  | NFile bs =>
      bv_unsigned (di_type dn) <> 0
      /\ bv_unsigned (di_type dn) <> T_DIR_z
      /\ bs = file_bytes data (Z.to_nat (bv_unsigned (di_size dn)))
  | NDir ents =>
      bv_unsigned (di_type dn) = T_DIR_z
      /\ dir_names_unique data (dir_nrec (bv_unsigned (di_size dn)))
      /\ ents = dir_view data (dir_nrec (bv_unsigned (di_size dn)))
  end.

Lemma node_rep_of (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> 0 ->
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
  node_rep (node_of dn data) dn data.
Proof.
  intros Hnz Hu. unfold node_of.
  destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [Hd | Hd];
    cbn; [split; [exact Hd | split; [exact Hu | reflexivity]] |].
  split; [exact Hnz | split; [exact Hd | reflexivity]].
Qed.

(* **THE SHARP FORM OF F1's ONE PROOF OBLIGATION.**  Any node representing
   [(dn, data)] IS [node_of dn data] -- bytes determine the tree. *)
Lemma node_rep_node_of (n : fsnode) (dn : dinode) (data : nat -> list (bv 8)) :
  node_rep n dn data -> n = node_of dn data.
Proof.
  destruct n as [bs | ents]; cbn; unfold node_of.
  - intros (_ & Hnd & ->). rewrite decide_False by exact Hnd. reflexivity.
  - intros (Hd & _ & ->). rewrite decide_True by exact Hd. reflexivity.
Qed.

(* ...and its determinacy corollary, [diblk_bytes_inj]'s analogue: this is
   what makes [FsRep.fs_rep] a function of the resources rather than a
   relation, and it is what the twice-instantiate audit demands. *)
Lemma node_rep_inj (n1 n2 : fsnode) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep n1 dn data -> node_rep n2 dn data -> n1 = n2.
Proof.
  intros H1 H2.
  rewrite (node_rep_node_of n1 dn data H1).
  rewrite (node_rep_node_of n2 dn data H2). reflexivity.
Qed.

(* the node's type, read back off the representation *)
Lemma node_rep_dir (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep (NDir ents) dn data -> bv_unsigned (di_type dn) = T_DIR_z.
Proof. intros (H & _ & _). exact H. Qed.

Lemma node_rep_file (bs : list (bv 8)) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep (NFile bs) dn data -> bv_unsigned (di_type dn) <> T_DIR_z.
Proof. intros (_ & H & _). exact H. Qed.

Lemma node_rep_alloc (n : fsnode) (dn : dinode) (data : nat -> list (bv 8)) :
  node_rep n dn data -> bv_unsigned (di_type dn) <> 0.
Proof.
  destruct n as [bs | ents]; cbn.
  - intros (H & _ & _). exact H.
  - intros (H & _ & _). rewrite H. unfold T_DIR_z. lia.
Qed.

(* THE ENTRY BRIDGE, and the reason F1b can state the [".."] fact at all:
   a name in [ents] IS a live record of the bytes, at the index
   [dirlookup] stops on.  The model places no record at a fixed index; the
   tree names it, and this lemma converts between the two. *)
Lemma node_rep_ent (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) (z : Z) :
  node_rep (NDir ents) dn data ->
  ents !! s = Some z ->
  exists k : nat,
    dir_first data (dir_nrec (bv_unsigned (di_size dn))) s = Some k
    /\ dir_live data k
    /\ dir_bname data k = s
    /\ bv_unsigned (dir_inum data k) = z.
Proof.
  intros (_ & _ & ->) H. apply dir_view_lookup_Some in H.
  destruct H as (k & Hk & Hz). exists k.
  split; [exact Hk |].
  split; [exact (dir_first_live _ _ _ _ Hk) |].
  split; [exact (dir_first_name _ _ _ _ Hk) | exact Hz].
Qed.

(* ...and back: under the invariant every live record IS an entry *)
Lemma node_rep_ent_of (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (k : nat) :
  node_rep (NDir ents) dn data ->
  (k < dir_nrec (bv_unsigned (di_size dn)))%nat -> dir_live data k ->
  ents !! dir_bname data k = Some (bv_unsigned (dir_inum data k)).
Proof.
  intros (_ & Hu & ->) Hk Hl. exact (dir_view_live data _ k Hu Hk Hl).
Qed.

(* ====================================================================== *)
(*  7.  PATHS                                                              *)
(* ====================================================================== *)

(* one step: follow name [f] out of node [i].  A file has no out-edges, and
   an inum outside the store has none either -- FRAGMENTS-WITH-HOLES is the
   only consistent top-level shape (fs-fragments.md §1.4), so a missing
   node is an ordinary [None] and never an error. *)
Definition tree_ent (t : fstree) (i : Z) (f : fname) : option Z :=
  match fs_nodes t !! i with
  | Some (NDir ents) => ents !! f
  | _ => None
  end.

Definition path_step (t : fstree) (oi : option Z) (f : fname) : option Z :=
  match oi with
  | Some i => tree_ent t i f
  | None => None
  end.

(* ONE [foldl] OVER [PathElems.path_elems]'s VOCABULARY.  No new path
   datatype: a path is the [list fname] [path_elems] already produces. *)
Definition path_at (t : fstree) (i : Z) (p : list fname) : option Z :=
  foldl (path_step t) (Some i) p.

Lemma path_at_nil (t : fstree) (i : Z) : path_at t i [] = Some i.
Proof. reflexivity. Qed.

Lemma path_step_none (t : fstree) (p : list fname) :
  foldl (path_step t) None p = None.
Proof. induction p as [| f p IH]; [reflexivity | exact IH]. Qed.

Lemma path_at_cons (t : fstree) (i : Z) (f : fname) (p : list fname) :
  path_at t i (f :: p)
  = match tree_ent t i f with
    | Some j => path_at t j p
    | None => None
    end.
Proof.
  unfold path_at. cbn [foldl path_step].
  destruct (tree_ent t i f) as [j |]; [reflexivity | apply path_step_none].
Qed.

Lemma path_at_app (t : fstree) (i : Z) (p q : list fname) :
  path_at t i (p ++ q)
  = match path_at t i p with
    | Some j => path_at t j q
    | None => None
    end.
Proof.
  revert i. induction p as [| f p IH]; intros i; [reflexivity |].
  cbn [app]. rewrite !path_at_cons. destruct (tree_ent t i f) as [j |].
  - apply IH.
  - reflexivity.
Qed.

Lemma path_at_singleton (t : fstree) (i : Z) (f : fname) :
  path_at t i [f] = tree_ent t i f.
Proof. rewrite path_at_cons. destruct (tree_ent t i f); reflexivity. Qed.

(* THE NODES A WALK TOUCHES, in order, stopping where the walk does.  This
   is what [FsRep.fslice] holds an [fnode] for -- the "closed fragment"
   special case a path-points-to is built out of. *)
Fixpoint path_chain (t : fstree) (i : Z) (p : list fname) : list Z :=
  match p with
  | [] => [i]
  | f :: p' =>
      i :: (match tree_ent t i f with
            | Some j => path_chain t j p'
            | None => []
            end)
  end.

Lemma path_chain_head (t : fstree) (i : Z) (p : list fname) :
  exists l, path_chain t i p = i :: l.
Proof. destruct p as [| f p]; cbn; eauto. Qed.

Lemma path_chain_last (t : fstree) (i j : Z) (p : list fname) :
  path_at t i p = Some j -> j ∈ path_chain t i p.
Proof.
  revert i. induction p as [| f p IH]; intros i H.
  - cbn in H. injection H as ->. cbn. apply elem_of_list_here.
  - rewrite path_at_cons in H. cbn [path_chain].
    destruct (tree_ent t i f) as [k |]; [| discriminate].
    apply elem_of_list_further. exact (IH k H).
Qed.

(* ====================================================================== *)
(*  8.  WELL-FORMEDNESS, AND ACYCLICITY AS A SEPARATE CONJUNCT (R1)        *)
(* ====================================================================== *)

(* Every key is a legal inum -- what makes the [bv 32] coercion at
   [FsRep.inum_of] round-trip.  Range against the region's capacity is
   [DirView.dir_inums_ok]'s business and stays there: it is a fact about
   the BYTES and it already rides in both escrow payloads. *)
Definition fs_inums_ok (t : fstree) : Prop :=
  forall (i : Z) (n : fsnode), fs_nodes t !! i = Some n -> 0 <= i < 2 ^ 32.

Definition fs_root_dir (t : fstree) : Prop :=
  exists ents : gmap fname Z, fs_nodes t !! fs_root t = Some (NDir ents).

Definition fs_wf (t : fstree) : Prop := fs_inums_ok t /\ fs_root_dir t.

(* A PROPER name is one that is neither of the two links every directory
   carries; following only proper names is what "descend" means. *)
Definition fs_proper (p : list fname) : Prop :=
  Forall (fun f => f <> DOT /\ f <> DOTDOT) p.

(* **ACYCLICITY IS NEVER A PROPERTY OF THE TYPE** (R1).  It is this, a
   separate derived conjunct that nothing landed needs and that no mover
   is therefore obliged to re-establish; it becomes load-bearing only at
   S7 (sys_unlink's [isdirempty]) and F4. *)
Definition fs_dirs_acyclic (t : fstree) : Prop :=
  forall (i : Z) (p : list fname),
    p <> [] -> fs_proper p -> path_at t i p <> Some i.

Lemma fs_dirs_acyclic_ne (t : fstree) (i j : Z) (f : fname) :
  fs_dirs_acyclic t -> f <> DOT -> f <> DOTDOT -> tree_ent t i f = Some j ->
  i <> j.
Proof.
  intros Hac Hd Hdd Hst ->. apply (Hac j [f]).
  - intros Hc. discriminate.
  - apply Forall_singleton. split; assumption.
  - rewrite path_at_singleton. exact Hst.
Qed.

(* ====================================================================== *)
(*  2.  THE RECORD DELTAS THE FRIENDLY LAYER READS ITS TREE DELTAS OFF     *)
(* ====================================================================== *)

(* WHAT dirlink LEAVES BEHIND, said at the record view -- the exact twin of
   [FsTree.dir_zeroed_at], which says what sys_unlink's memset+writei
   leaves behind.  Slot [k0] now holds the name [s] at inum [z]; every
   other record's sixteen bytes are untouched, which is
   [DirView.dir_win_agree], the vocabulary a byte-range postcondition
   converts into with [DirView.dir_win_agree_below].

   ONE CLAUSE COVERS BOTH OF dirlink's ARMS.  The APPEND arm has
   [k0 = nrec] and grows the count; the REUSE arm has [k0 < nrec] at a
   record that was FREE.  They differ only in where [k0] sits relative to
   the OLD count, which is why the lemmas below quantify over [nrec] and
   [nrec'] separately instead of being written twice. *)
Definition dir_written_at (data data' : nat -> list (bv 8)) (k0 : nat)
    (s : fname) (z : bv 16) : Prop :=
  dir_inum data' k0 = z
  /\ dir_bname data' k0 = s
  /\ (forall q : nat, q <> k0 -> dir_win_agree data data' q).

Lemma dir_written_inum (data data' : nat -> list (bv 8)) (k0 : nat)
    (s : fname) (z : bv 16) (q : nat) :
  dir_written_at data data' k0 s z -> q <> k0 ->
  dir_inum data' q = dir_inum data q.
Proof. intros (_ & _ & H) Hq. exact (dir_inum_agree data data' q (H q Hq)). Qed.

Lemma dir_written_bname (data data' : nat -> list (bv 8)) (k0 : nat)
    (s : fname) (z : bv 16) (q : nat) :
  dir_written_at data data' k0 s z -> q <> k0 ->
  dir_bname data' q = dir_bname data q.
Proof.
  intros (_ & _ & H) Hq. exact (dir_bname_agree data data' q (H q Hq)).
Qed.

Lemma dir_written_live (data data' : nat -> list (bv 8)) (k0 : nat)
    (s : fname) (z : bv 16) (q : nat) :
  dir_written_at data data' k0 s z -> q <> k0 ->
  (dir_live data' q <-> dir_live data q).
Proof.
  intros Hw Hq. unfold dir_live.
  rewrite (dir_written_inum data data' k0 s z q Hw Hq). reflexivity.
Qed.

(* the written record is LIVE: its inum halfword is the nonzero [z] *)
Lemma dir_written_live0 (data data' : nat -> list (bv 8)) (k0 : nat)
    (s : fname) (z : bv 16) :
  dir_written_at data data' k0 s z -> z <> bv_0 16 -> dir_live data' k0.
Proof. intros (Hz & _ & _) Hnz. unfold dir_live. rewrite Hz. exact Hnz. Qed.

(* EVERY LIVE RECORD OF THE NEW STATE IS EITHER THE WRITTEN ONE OR AN OLD
   ONE.  The workhorse of both lemmas below; the second premise is what the
   APPEND arm supplies (the records the count grew over, other than the one
   written, are free -- and there are none at all when the count grows by
   exactly one, onto [k0]). *)
Lemma dir_written_class (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) (q : nat) :
  dir_written_at data data' k0 s z ->
  (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r) ->
  (q < nrec')%nat -> dir_live data' q -> q <> k0 ->
  (q < nrec)%nat /\ dir_live data q.
Proof.
  intros Hw Hdead Hq Hl Hqk.
  destruct (decide (q < nrec)%nat) as [Hlt | Hge].
  - split; [exact Hlt |].
    exact (proj1 (dir_written_live data data' k0 s z q Hw Hqk) Hl).
  - exfalso. assert (Hrng : (nrec <= q < nrec')%nat) by lia.
    exact (Hdead q Hrng Hqk Hl).
Qed.

(* UNIQUENESS IS PRESERVED, and dirlink's guard is exactly what pays for it:
   the kernel refuses to append a name the scan already found
   ([SpecDirlink] exposes [dir_first data nrec s = None] on the append arm
   and the found-arm negation on the other), so the written name collides
   with no surviving live record. *)
Lemma dir_names_unique_write (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) :
  dir_names_unique data nrec ->
  (nrec <= nrec')%nat -> (k0 < nrec')%nat ->
  (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r) ->
  dir_first data nrec s = None ->
  dir_written_at data data' k0 s z ->
  dir_names_unique data' nrec'.
Proof.
  intros Hu Hle Hk0 Hdead Hnone Hw j k Hj Hk Hlj Hlk Heq.
  (* the written name meets no surviving live record *)
  assert (Hno : forall q : nat, (q < nrec')%nat -> dir_live data' q ->
                  q <> k0 -> dir_bname data' q <> s).
  { intros q Hq Hl Hqk Hnm.
    destruct (dir_written_class data data' nrec nrec' k0 s z q Hw Hdead Hq Hl Hqk)
      as [Hqlt Hlq].
    apply (proj1 (dir_first_None data nrec s) Hnone q Hqlt).
    split; [exact Hlq |].
    rewrite <- Hnm. symmetry.
    exact (dir_written_bname data data' k0 s z q Hw Hqk). }
  destruct (decide (j = k0)) as [Hjk0 | Hjk0];
    destruct (decide (k = k0)) as [Hkk0 | Hkk0].
  - congruence.
  - exfalso. apply (Hno k Hk Hlk Hkk0).
    rewrite <- Heq. rewrite Hjk0. exact (proj1 (proj2 Hw)).
  - exfalso. apply (Hno j Hj Hlj Hjk0).
    rewrite Heq. rewrite Hkk0. exact (proj1 (proj2 Hw)).
  - destruct (dir_written_class data data' nrec nrec' k0 s z j Hw Hdead Hj Hlj Hjk0)
      as [Hjlt Hlj0].
    destruct (dir_written_class data data' nrec nrec' k0 s z k Hw Hdead Hk Hlk Hkk0)
      as [Hklt Hlk0].
    apply (Hu j k Hjlt Hklt Hlj0 Hlk0).
    rewrite <- (dir_written_bname data data' k0 s z j Hw Hjk0).
    rewrite <- (dir_written_bname data data' k0 s z k Hw Hkk0).
    exact Heq.
Qed.

(* ---- THE INSERT'S VIEW EQUATION, THE TWIN OF [dir_view_zero] --------- *)

(* The scan that finds nothing new above [n] answers at [n].  ([dfirst_ext]
   compares two predicates at ONE count; this compares one predicate at two
   counts, which is what the APPEND arm's grown record count needs.) *)
Lemma dfirst_trunc (p : nat -> bool) (n m : nat) :
  (n <= m)%nat -> (forall j : nat, (n <= j < m)%nat -> p j = false) ->
  dfirst p m = dfirst p n.
Proof.
  intros Hle Hab. destruct (dfirst p n) as [k |] eqn:Hf.
  - exact (dfirst_mono p n m k Hle Hf).
  - apply dfirst_None_2. intros j Hj.
    destruct (decide (j < n)%nat) as [Hlt | Hge].
    + exact (dfirst_None_1 p n Hf j Hlt).
    + apply Hab. lia.
Qed.

(* the [dfirst_ext] comparison off the written slot, [dir_zeroed_matchb]'s
   twin *)
Lemma dir_written_matchb (data data' : nat -> list (bv 8))
    (k0 : nat) (s : fname) (z : bv 16) (x : fname) (q : nat) :
  dir_written_at data data' k0 s z -> q <> k0 ->
  dir_matchb data' q x = dir_matchb data q x.
Proof.
  intros Hw Hq. unfold dir_matchb, dir_liveb, dir_freeb.
  rewrite (dir_written_inum data data' k0 s z q Hw Hq).
  replace (bname 14 (dir_name data' q)) with (dir_bname data' q) by reflexivity.
  replace (bname 14 (dir_name data q)) with (dir_bname data q) by reflexivity.
  rewrite (dir_written_bname data data' k0 s z q Hw Hq). reflexivity.
Qed.

(* **WHAT dirlink DOES TO A DIRECTORY, AT THE RECORD VIEW.**
   [dir_written_at] says only that slot [k0] now reads [(s, z)] and that no
   other record's sixteen bytes moved; that alone is not an INSERT, for two
   reasons this clause adds:

     - the slot must not have been LIVE below the old count, or the write
       would have DESTROYED a name rather than added one.  Both of dirlink's
       arms give it: the REUSE arm's slot is the free record the scan
       settled on, and the APPEND arm's [k0 = nrec] makes it vacuous;
     - the records the count GREW over, other than [k0], must be dead --
       there are none at all when the count grows onto [k0] by exactly one,
       which is what [dir_insert_append] discharges.

   [z <> bv_0 16] is what makes the new record live at all.  The two
   constructors below are the two arms; everything else here quantifies over
   [nrec]/[nrec'] separately rather than being written twice. *)
Definition dir_insert_at (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) : Prop :=
  (nrec <= nrec')%nat
  /\ (k0 < nrec')%nat
  /\ ((k0 < nrec)%nat -> ~ dir_live data k0)
  /\ (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r)
  /\ z <> bv_0 16
  /\ dir_written_at data data' k0 s z.

(* ARM 1 -- REUSE: a free record below the count, and the count is unmoved *)
Lemma dir_insert_reuse (data data' : nat -> list (bv 8))
    (nrec k0 : nat) (s : fname) (z : bv 16) :
  (k0 < nrec)%nat -> ~ dir_live data k0 -> z <> bv_0 16 ->
  dir_written_at data data' k0 s z ->
  dir_insert_at data data' nrec nrec k0 s z.
Proof.
  intros Hk0 Hfree Hnz Hw.
  split; [lia | split; [lia | split; [intros _; exact Hfree | split]]].
  - intros r Hr. exfalso. lia.
  - split; [exact Hnz | exact Hw].
Qed.

(* ARM 2 -- APPEND: the record past the end, and the count grows by one *)
Lemma dir_insert_append (data data' : nat -> list (bv 8))
    (nrec : nat) (s : fname) (z : bv 16) :
  z <> bv_0 16 -> dir_written_at data data' nrec s z ->
  dir_insert_at data data' nrec (S nrec) nrec s z.
Proof.
  intros Hnz Hw.
  split; [lia | split; [lia | split; [intros H; exfalso; lia | split]]].
  - intros r Hr Hrk. exfalso. lia.
  - split; [exact Hnz | exact Hw].
Qed.

(* **THE TREE DELTA OF A dirlink, AND IT NEEDS NO UNIQUENESS.**  Unlike
   [dir_view_zero] -- where a hidden duplicate BEHIND the zeroed record is
   unmasked -- an insert only has to reach the front of the first-match
   scan, so [dir_names_unique] is not a premise here.  The one guard is
   dirlink's own, and it is the WEAKEST that makes the equation true: [s]
   must not already be a live name ([dir_first data nrec s = None],
   equivalently [dir_view data nrec !! s = None] by
   [dir_view_lookup_None]).  Without it the name is already mapped, to the
   OLD record's inum, and the first-match answer never reaches [k0]. *)
Lemma dir_view_insert (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) :
  dir_first data nrec s = None ->
  dir_insert_at data data' nrec nrec' k0 s z ->
  dir_view data' nrec' = <[s := bv_unsigned z]> (dir_view data nrec).
Proof.
  intros Hnone (Hle & Hk0 & Hfree & Hdead & Hnz & Hw).
  pose proof Hw as (Hinum0 & Hbname0 & _).
  assert (Hl0 : dir_live data' k0)
    by exact (dir_written_live0 data data' k0 s z Hw Hnz).
  apply map_eq. intros x.
  destruct (decide (x = s)) as [-> | Hne].
  - (* the written name: the scan stops AT [k0] *)
    rewrite lookup_insert. rewrite dir_view_lookup.
    assert (Hf : dir_first data' nrec' s = Some k0).
    { unfold dir_first. apply dfirst_Some_2; [exact Hk0 | |].
      - apply dir_matchb_true. split; [exact Hl0 | exact Hbname0].
      - intros j Hj.
        assert (Hjk : j <> k0) by lia.
        destruct (decide (j < nrec)%nat) as [Hjn | Hjn].
        + rewrite (dir_written_matchb data data' k0 s z s j Hw Hjk).
          apply dir_matchb_false.
          exact (proj1 (dir_first_None data nrec s) Hnone j Hjn).
        + apply dir_matchb_false. intros [Hlv _].
          exact (Hdead j ltac:(lia) Hjk Hlv). }
    rewrite Hf. cbn. rewrite Hinum0. reflexivity.
  - (* every other name: the first-match search is unmoved *)
    rewrite lookup_insert_ne by congruence.
    rewrite !dir_view_lookup.
    assert (Hab : forall r : nat, (nrec <= r < nrec')%nat ->
                    dir_matchb data' r x = false).
    { intros r Hr. apply dir_matchb_false. intros [Hlv Hnm].
      destruct (decide (r = k0)) as [-> | Hrk].
      - apply Hne. rewrite <- Hnm. exact Hbname0.
      - exact (Hdead r Hr Hrk Hlv). }
    assert (Hf : dir_first data' nrec' x = dir_first data nrec x).
    { unfold dir_first.
      rewrite (dfirst_trunc (fun k => dir_matchb data' k x) nrec nrec' Hle Hab).
      apply dfirst_ext. intros j Hj.
      destruct (decide (j = k0)) as [-> | Hjk].
      - assert (H1 : dir_matchb data' k0 x = false).
        { apply dir_matchb_false. intros [_ Hnm].
          apply Hne. rewrite <- Hnm. exact Hbname0. }
        assert (H2 : dir_matchb data k0 x = false).
        { apply dir_matchb_false. intros [Hlv _]. exact (Hfree Hj Hlv). }
        rewrite H1, H2. reflexivity.
      - exact (dir_written_matchb data data' k0 s z x j Hw Hjk). }
    rewrite Hf.
    destruct (dir_first data nrec x) as [k |] eqn:Hfd; [| reflexivity].
    apply dir_first_Some in Hfd. destruct Hfd as (Hkn & [Hlv Hnm] & _).
    assert (Hkk0 : k <> k0) by (intros ->; exact (Hfree Hkn Hlv)).
    cbn. rewrite (dir_written_inum data data' k0 s z k Hw Hkk0). reflexivity.
Qed.

(* ...and the value half, straight off [dir_names_unique_write] *)
Lemma dir_names_unique_insert (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) :
  dir_names_unique data nrec ->
  dir_first data nrec s = None ->
  dir_insert_at data data' nrec nrec' k0 s z ->
  dir_names_unique data' nrec'.
Proof.
  intros Hu Hnone (Hle & Hk0 & _ & Hdead & _ & Hw).
  exact (dir_names_unique_write data data' nrec nrec' k0 s z
           Hu Hle Hk0 Hdead Hnone Hw).
Qed.

(* ====================================================================== *)
(*  9.  THE PAYLOAD CLAUSE [dir_uniq] (fs-fragments §7.5.8, item S2-0),     *)
(*      AND dirlink's PRESERVATION MOVER, MOVED DOWN FROM [FsLookup.v].     *)
(*                                                                          *)
(*  R2 rules that name uniqueness is an INVARIANT.  Until this clause it     *)
(*  had no CARRIER: [dir_names_unique] occurred in exactly two files         *)
(*  ([FsTree.v] and [FsLookup.v]) and in no payload, no spec and no walk,    *)
(*  so no landed proof could build an [FsRep.fnode] / [FsLookup.fdir] and    *)
(*  the whole tree layer was unreachable from every WP in the tree.  This    *)
(*  is that carrier: it rides in [IcacheEscrow.ipool_alloc] and              *)
(*  [ic_loaded] beside [dir_ok] / [dir_dots_ix] / [dir_orphan_clean].        *)
(*                                                                          *)
(*  IT IS TYPE-GUARDED EXACTLY AS [dir_ok] IS, AND THE GUARD IS NOT          *)
(*  DECORATION: unguarded the clause is FALSE of a FILE -- a large file's    *)
(*  bytes read as records will collide -- which is the [dir_dots_ix]         *)
(*  road-test lesson, one clause over.                                       *)
(*                                                                          *)
(*  LAYERING NOTE.  fs-fragments §7.5.8 charts the definition for            *)
(*  [DirView.v]; it lands HERE because [dir_names_unique], [dir_bname] and   *)
(*  [fname] are this file's vocabulary and DirView is BELOW it (DirView is   *)
(*  a leaf; FsTree imports it, not the other way round).  Moving the three   *)
(*  down into DirView would have restated [dir_bname] as [bname 14 (…)] in   *)
(*  every proof of two files for no gain.  [IcacheEscrow.v] therefore        *)
(*  gains one import of this file, which costs nothing: FsTree's own         *)
(*  imports are a subset of the escrow's.                                    *)
(* ====================================================================== *)

Definition dir_uniq (dn : dinode) (data : nat -> list (bv 8)) : Prop :=
  bv_unsigned (di_type dn) = T_DIR_z ->
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))).

(* ---- the five ways a holder discharges it, [dir_ok]'s shape exactly --- *)

(* (i) it is not a directory *)
Lemma dir_uniq_not_dir (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> dir_uniq dn data.
Proof. intros H Hc. exfalso. exact (H Hc). Qed.

(* (ii) it is FREE -- [ipool_shape_np]'s free arm, and iput's post-itrunc park *)
Lemma dir_uniq_free (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = 0 -> dir_uniq dn data.
Proof.
  intros H. apply dir_uniq_not_dir. rewrite H. unfold T_DIR_z. lia.
Qed.

(* (iii) it holds no whole record -- a claim box and a truncated corpse *)
Lemma dir_uniq_size_zero (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn) = 0 -> dir_uniq dn data.
Proof.
  intros H _ j k Hj. exfalso. rewrite H in Hj.
  change (dir_nrec 0) with 0%nat in Hj. lia.
Qed.

(* (iv) the record and the data are unchanged -- the "rides" case every
   re-park in the cache is *)
Lemma dir_uniq_eq (dn dn' : dinode) (data data' : nat -> list (bv 8)) :
  dn = dn' -> data = data' -> dir_uniq dn data -> dir_uniq dn' data'.
Proof. intros -> ->. exact id. Qed.

(* (v) ONLY THE COUNT MOVED.  [dir_uniq] reads the record through
   [di_type] and [di_size] alone, so every [nlink]-moving walk
   (sys_link's [bad:], create's [dp->nlink++] and its three [fail:]
   flushes, sys_unlink's two decrements) crosses it in one line. *)
Lemma dir_uniq_cong (dn dn' : dinode) (data : nat -> list (bv 8)) :
  di_type dn' = di_type dn -> di_size dn' = di_size dn ->
  dir_uniq dn data -> dir_uniq dn' data.
Proof. intros Hty Hsz H Hd. rewrite Hsz. apply H. rewrite <- Hty. exact Hd. Qed.

(* the raw form, for a producer that has the invariant outright (boot) *)
Lemma dir_uniq_of (dn : dinode) (data : nat -> list (bv 8)) :
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
  dir_uniq dn data.
Proof. intros H _. exact H. Qed.

(* ...and the projection, which is what [FsRep.fnode_intro_of] consumes *)
Lemma dir_uniq_names (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z -> dir_uniq dn data ->
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))).
Proof. intros Hty H. exact (H Hty). Qed.

(* ---- MOVER 1: sys_unlink's ZEROING ----------------------------------- *)

(* Free, and for the reason [dir_names_unique_zero] records: zeroing only
   REMOVES a live name.  The size cannot rise (the record is inside the
   directory), so the count cannot either. *)
Lemma dir_uniq_zero (dn dn' : dinode) (data data' : nat -> list (bv 8))
    (k0 : nat) :
  di_type dn' = di_type dn ->
  bv_unsigned (di_size dn') <= bv_unsigned (di_size dn) ->
  dir_zeroed_at data data' k0 ->
  dir_uniq dn data -> dir_uniq dn' data'.
Proof.
  intros Hty Hsz Hzer H Hd'.
  assert (Hd : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hd').
  apply (dir_names_unique_le data'
           (dir_nrec (bv_unsigned (di_size dn')))
           (dir_nrec (bv_unsigned (di_size dn)))).
  - apply dir_nrec_mono. exact Hsz.
  - exact (dir_names_unique_zero data data' _ k0 Hzer (H Hd)).
Qed.

(* ---- MOVER 2: dirlink's WRITE ---------------------------------------- *)

(* **THE ATOMICITY PREMISE IS THE WHOLE ARGUMENT.**  At [0 < tot < 16] the
   clause is genuinely FALSE: a partial record goes LIVE carrying the NAME
   BYTES the last deletion left behind (xv6 zeroes only the inum
   halfword), and those may well duplicate a live name.  [SpecDirlink]'s
   [dl_post] already relays [SpecWritei.wi16_atomic] -- [tot = 0 \/
   tot = 16] at this call's single-block window -- so the premise costs a
   caller one [destruct].  At [tot = 0] nothing moved at all; at
   [tot = 16] the guard dirlink itself applies ([dir_first data nrec s =
   None]) is what pays. *)
Lemma dir_uniq_dirlink (dn dn' : dinode)
    (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  (tot = 0%nat \/ tot = 16%nat) ->
  (length s <= 14)%nat -> nonul s ->
  di_type dn' = di_type dn ->
  bv_unsigned (di_size dn')
    = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_first data nrec s = None ->
  dir_uniq dn data -> dir_uniq dn' data'.
Proof.
  intros Hnrec Hk0 Htot Hlen Hs Hty Hsz Hrng Hnone H Hd'.
  assert (Hd : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hd').
  specialize (H Hd). rewrite <- Hnrec in H.
  (* the count arithmetic, [dir_ok_dirlink]'s verbatim *)
  assert (Hsznn : 0 <= bv_unsigned (di_size dn))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
  assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
  destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
  destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn') as [Hnr1' Hnr2'].
  rewrite <- Hnrec in Hnr1, Hnr2.
  assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
  set (nrec' := dir_nrec (bv_unsigned (di_size dn'))).
  assert (Hcle : (nrec <= nrec')%nat) by (unfold nrec'; lia).
  destruct Htot as [Htot | Htot].
  - (* ======== tot = 0: nothing was written, and the size did not move === *)
    subst tot.
    assert (Hagr : forall q : nat, dir_win_agree data data' q).
    { intros q j Hj. rewrite (Hrng (16 * q + j)%nat).
      rewrite decide_False; [reflexivity |]. lia. }
    assert (Hnre : (nrec' <= nrec)%nat) by (unfold nrec'; lia).
    intros j k Hj Hk Hlj Hlk Heq.
    apply H; try lia.
    + unfold dir_live. rewrite <- (dir_inum_agree data data' j (Hagr j)).
      exact Hlj.
    + unfold dir_live. rewrite <- (dir_inum_agree data data' k (Hagr k)).
      exact Hlk.
    + unfold dir_bname.
      rewrite <- (dir_bname_agree data data' j (Hagr j)).
      rewrite <- (dir_bname_agree data data' k (Hagr k)).
      exact Heq.
  - (* ======== tot = 16: the record is WHOLLY new ======================= *)
    subst tot.
    assert (Hwin : forall j, (j < 16)%nat ->
              file_byte data' (16 * k0 + j)%nat
              = dirent_bytes (de_of_name inum s) !!! j).
    { intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + j - 16 * k0)%nat with j by lia. reflexivity. }
    destruct (dir_record_of_name data' k0 inum s Hlen Hs Hwin) as [Hrin Hrnm].
    assert (Hwrit : dir_written_at data data' k0 s inum).
    { split; [exact Hrin | split].
      - unfold dir_bname. exact Hrnm.
      - intros q Hq j Hj. rewrite (Hrng (16 * q + j)%nat).
        rewrite decide_False; [reflexivity |].
        intros [Hlo Hhi]. apply Hq. lia. }
    assert (Hk0lt : (k0 < nrec')%nat) by (unfold nrec'; lia).
    assert (Hdead : forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 ->
                      ~ dir_live data' r).
    { intros r Hr Hrk. exfalso. unfold nrec' in Hr. lia. }
    exact (dir_names_unique_write data data' nrec nrec' k0 s inum
             H Hcle Hk0lt Hdead Hnone Hwrit).
Qed.
