(* FsAbsDefs.v -- THE PURE LAYER OF FsAbs.v, HOISTED.

   This file is FsAbs.v's sections 1-2 and section 3a's [abs_view], moved
   here VERBATIM on 2026-09-04 (a pure hoist: no statement changed, no proof
   touched).  FsAbs.v does [Require Export FsAbsDefs], so every consumer of
   FsAbs sees the same names bound to the same constants; nothing landed
   moved (R10).

   WHY A SEPARATE FILE.  Everything below is pure -- [absnode]/[anode]/
   [aview], [abs_of] as a reading of [FsStateInode]'s readings, the bridge
   to [FsTree.fsnode], the hop-by-hop lookup [apath_at], the visited-inum
   run [arun], and [abs_view] (the raw γtop map read through [abs_of]).
   None of it mentions a ghost, Σ, or an iProp; FsAbs.v's sections 3-5 do.
   Files BELOW [ProcInv] that must STATE something over [aview]/[abs_view]
   -- FsAbsInv's application license, FsAbsDelta's write deltas -- can now
   require this file alone instead of FsAbs's ghost cone.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 1-3
   (v3).  The prose that belongs to each definition travelled with it; the
   file-level history (why [abs_view] is over the RAW map, why [apath_at]
   is not spelled [path_at], what the seam attempt found) is in FsAbs.v's
   header, which remains the design's home.

   REQUIRES: FsAbs.v's block minus [Xv6Cameras] (only the ghost sections
   need the camera classes).  [FsState] stays an Export, as in FsAbs.v:
   the readings this file packages ([fn_is_dir], [dir_entries],
   [fn_file_bytes], [fn_nlink]) are FsStateInode's. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import iprop own ghost_map fancy_updates.
Require Import DinodeEnc.      (* [di_major], [di_minor]                     *)
Require Import DirView.        (* [T_DIR_z]                                  *)
Require Import FsTree.         (* [fname], [fsnode], [path_at], [node_of]    *)
Require Import FsImg.          (* [T_FILE_z], [ROOTINO]                      *)
Require Export FsState.        (* Export's FsStateInode: the readings        *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ABSTRACT NODE, AND [abs_of] AS A READING                      *)
(* ===================================================================== *)

(* The device numbers are the only field of the record the tree's readings
   never needed: a device node's CONTENT is its (major, minor) pair, and
   [fn_file_bytes] of one is the empty list.  Two one-line readings, spelled
   the way [fn_type]/[fn_size] are. *)
Definition fn_major (n : fs_node) : Z := bv_unsigned (di_major (fn_rec n)).
Definition fn_minor (n : fs_node) : Z := bv_unsigned (di_minor (fn_rec n)).

Inductive absnode :=
| AFile (bs   : list (bv 8))
| ADir  (ents : gmap fname Z)          (* INCLUDES "." and ".."            *)
| ADev  (major minor : Z).

Record anode := MkAnode { an_node : absnode ; an_nlink : nat }.

(* inum-keyed (fs-fragments section 1.1).  A NOTATION, not a [Definition]:
   an abbreviation that is a [Definition] elaborates [av !! d] at the type
   [aview] while a landed lemma about the same map ([lookup_fmap]) elaborates
   it at [gmap Z anode], and the two terms PRINT IDENTICALLY while [destruct]
   and [rewrite] miss one of them (durable-notes, "rewrite CAN FAIL ON A
   SUBTERM THAT PRINTS CHARACTER-FOR-CHARACTER").  Cost measured: one
   [abs_tree_ent] that would not close. *)
Notation aview := (gmap Z anode).

Global Instance absnode_eq_dec : EqDecision absnode.
Proof. solve_decision. Defined.
Global Instance anode_eq_dec : EqDecision anode.
Proof. solve_decision. Defined.
Global Instance absnode_inhabited : Inhabited absnode := populate (AFile []).
Global Instance anode_inhabited : Inhabited anode :=
  populate (MkAnode (AFile []) 0%nat).

(* THE READING.  Three arms, each one of FsStateInode's existing readings;
   the type halfword picks the arm and [fn_nlink] is carried as a FIELD, not
   derived from any edge count (fs-syscall-specs section 1, "nlink is
   node-local data"). *)
Definition abs_node (n : fs_node) : absnode :=
  if fn_is_dir n then ADir (dir_entries n)
  else if decide (fn_type n = T_FILE_z) then AFile (fn_file_bytes n)
  else ADev (fn_major n) (fn_minor n).

Definition abs_of (n : fs_node) : anode := MkAnode (abs_node n) (fn_nlink n).

Lemma abs_of_nlink (n : fs_node) : an_nlink (abs_of n) = fn_nlink n.
Proof. reflexivity. Qed.

Lemma abs_of_dir (n : fs_node) :
  fn_is_dir n = true -> an_node (abs_of n) = ADir (dir_entries n).
Proof. intros Hd. rewrite /abs_of /abs_node /= Hd //. Qed.

(* ...AND ITS INVERSE, which is what a LEND-side law needs: only a directory
   reads as [ADir], and the map it reads as is [dir_entries].  Stated as an
   inversion rather than as an [iff] because the two conclusions are used
   together at exactly one place ([FsAbsSeam.dv_top_seam]). *)
Lemma abs_of_dir_inv (n : fs_node) (e : gmap fname Z) :
  an_node (abs_of n) = ADir e -> fn_is_dir n = true /\ e = dir_entries n.
Proof.
  rewrite /abs_of /abs_node /=. destruct (fn_is_dir n) eqn:Hd.
  - intros He. injection He as He. split; [reflexivity | by rewrite He].
  - destruct (decide (fn_type n = T_FILE_z)); intros He; discriminate.
Qed.

Lemma abs_of_file (n : fs_node) :
  fn_is_dir n = false -> fn_type n = T_FILE_z ->
  an_node (abs_of n) = AFile (fn_file_bytes n).
Proof.
  intros Hd Ht. rewrite /abs_of /abs_node /= Hd.
  by rewrite (decide_True (P := fn_type n = T_FILE_z)).
Qed.

Lemma abs_of_dev (n : fs_node) :
  fn_is_dir n = false -> fn_type n <> T_FILE_z ->
  an_node (abs_of n) = ADev (fn_major n) (fn_minor n).
Proof.
  intros Hd Ht. rewrite /abs_of /abs_node /= Hd.
  by rewrite (decide_False (P := fn_type n = T_FILE_z)).
Qed.

(* the orphan reading (fs-syscall-specs section 1, "orphans are IN the
   map"): an unlinked-but-open node is an ordinary row at nlink 0 *)
Lemma abs_of_orphan (n : fs_node) :
  fn_orphan n = true <-> an_nlink (abs_of n) = 0%nat.
Proof. rewrite /fn_orphan bool_decide_eq_true. reflexivity. Qed.

(* a bare record (every free record, [ialloc]'s claim box, the corpse
   [itrunc]/[iput] leave) reads as a nlink-0 node with no entries *)
Lemma abs_of_bare_dir (n : fs_node) :
  fn_bare n -> fn_is_dir n = true -> abs_of n = MkAnode (ADir ∅) 0%nat.
Proof.
  intros Hb Hd. rewrite /abs_of /abs_node Hd (dir_entries_bare n Hb).
  by destruct Hb as (_ & _ & _ & _ & ->).
Qed.

(* THE VIEW-PRESERVING RETAG (app-instances.md section 7, round E1).  A
   kernel move whose reading is unchanged owes the application nothing
   ([InodeRegion.ireg_top_retag_same]), and the shape that recurs at the
   sites is a DIRECTORY whose type, count and entry map all ride -- a
   dirlink that wrote nothing (create's and link's fail bodies, mkdir's
   failing parent append), or a bare directory either side (mkdir's failing
   ["."]).  The block addresses and the bytes past the size may move
   freely: [abs_of] never reads them. *)
Lemma abs_of_dir_same (n n' : fs_node) :
  fn_is_dir n = true ->
  fn_type n = fn_type n' ->
  fn_nlink n = fn_nlink n' ->
  dir_entries n = dir_entries n' ->
  abs_of n = abs_of n'.
Proof.
  intros Hd Hty Hnl He.
  assert (Hd' : fn_is_dir n' = true) by (rewrite /fn_is_dir -Hty; exact Hd).
  rewrite /abs_of /abs_node Hd Hd' He Hnl. reflexivity.
Qed.

(* ...and a directory at size 0 has no entries whatever its bytes say *)
Lemma dir_entries_size_0 (n : fs_node) : fn_size n = 0 -> dir_entries n = ∅.
Proof.
  intros Hsz. rewrite /dir_entries. destruct (fn_is_dir n); [| reflexivity].
  rewrite /fn_nrec Hsz dir_nrec_zero. apply dir_view_nil.
Qed.

(* ---------------------------------------------------------------------
   1a.  THE BRIDGE TO [FsTree.fsnode] -- WALK-ONLY, AND SAID SO

   [abs_fsnode] forgets nlink and the device numbers; it exists for ONE
   purpose, to inherit FsTree's path algebra ([path_at_app], [path_chain],
   ...) at the abstract state instead of re-proving it.  It is never a
   state: a device node lands on [NFile []] because a device has no
   out-edges, which is all a walk asks of it.
   --------------------------------------------------------------------- *)

Definition abs_fsnode (a : anode) : fsnode :=
  match an_node a with
  | ADir ents => NDir ents
  | AFile bs  => NFile bs
  | ADev _ _  => NFile []
  end.

Definition abs_tree (av : aview) (r : Z) : fstree :=
  MkTree (abs_fsnode <$> av) r.

(* [abs_fsnode ∘ abs_of] IS [FsTree.node_of] wherever [node_of] can speak --
   directories and regular files.  Devices are excluded on purpose:
   [node_of] collapses every non-directory onto [NFile], so it cannot see
   the arm [absnode] adds. *)
Lemma abs_fsnode_node_of (n : fs_node) :
  fn_is_dir n = true \/ fn_type n = T_FILE_z ->
  abs_fsnode (abs_of n) = node_of (fn_rec n) (fn_data n).
Proof.
  intros Hn. rewrite /abs_fsnode /node_of /abs_of /abs_node /=.
  destruct (fn_is_dir n) eqn:Hd.
  - rewrite /fn_is_dir bool_decide_eq_true in Hd.
    rewrite (decide_True (P := bv_unsigned (di_type (fn_rec n)) = T_DIR_z));
      [| exact Hd].
    rewrite /dir_entries /fn_is_dir bool_decide_eq_true_2; [| exact Hd].
    by rewrite /fn_nrec /fn_size.
  - rewrite /fn_is_dir bool_decide_eq_false in Hd.
    rewrite (decide_False (P := bv_unsigned (di_type (fn_rec n)) = T_DIR_z));
      [| exact Hd].
    destruct Hn as [Hn | Hn]; [congruence |].
    rewrite (decide_True (P := fn_type n = T_FILE_z)); [| exact Hn].
    by rewrite /fn_file_bytes /fn_size.
Qed.

(* ===================================================================== *)
(*  2.  [apath_at]: THE HOP-BY-HOP FIRST-MATCH LOOKUP                     *)
(* ===================================================================== *)

(* One hop out of a node.  A file, a device and an inum with no row all have
   NO out-edges -- fragments-with-holes is the only consistent top-level
   shape (fs-fragments section 1.4) -- so each is an ordinary [None] and
   never an error.  DOTS ARE ORDINARY NAMES: [dir_entries] contains "." and
   "..", so [apath_at av d [DOTDOT]] is a lookup like any other. *)
Definition anode_ents (a : anode) : option (gmap fname Z) :=
  match an_node a with
  | ADir ents => Some ents
  | _ => None
  end.

Definition aents (av : aview) (d : Z) : option (gmap fname Z) :=
  av !! d ≫= anode_ents.

Definition astep (av : aview) (d : Z) (s : fname) : option Z :=
  aents av d ≫= (fun e => e !! s).

Fixpoint apath_at (av : aview) (d : Z) (ps : list fname) : option Z :=
  match ps with
  | [] => Some d
  | s :: ps' => match astep av d s with
                | Some c => apath_at av c ps'
                | None => None
                end
  end.

Lemma apath_at_nil (av : aview) (d : Z) : apath_at av d [] = Some d.
Proof. reflexivity. Qed.

Lemma apath_at_cons (av : aview) (d : Z) (s : fname) (ps : list fname) :
  apath_at av d (s :: ps)
  = match astep av d s with Some c => apath_at av c ps | None => None end.
Proof. reflexivity. Qed.

(* THE INHERITANCE: one step at the abstract state IS one step in the tree
   reading, so [apath_at] IS [FsTree.path_at] and every lemma of section 7
   of FsTree transports. *)
Lemma abs_tree_ent (av : aview) (r d : Z) (s : fname) :
  tree_ent (abs_tree av r) d s = astep av d s.
Proof.
  rewrite /tree_ent /abs_tree /astep /aents /= lookup_fmap.
  destruct (av !! d) as [a |]; simpl.
  - rewrite /abs_fsnode /anode_ents. destruct (an_node a); reflexivity.
  - reflexivity.
Qed.

Lemma apath_at_tree (av : aview) (r d : Z) (ps : list fname) :
  path_at (abs_tree av r) d ps = apath_at av d ps.
Proof.
  revert d. induction ps as [| s ps IH]; intros d; [reflexivity |].
  rewrite path_at_cons apath_at_cons abs_tree_ent.
  destruct (astep av d s) as [c |]; [apply IH | reflexivity].
Qed.

Lemma apath_at_app (av : aview) (d : Z) (ps qs : list fname) :
  apath_at av d (ps ++ qs)
  = match apath_at av d ps with Some c => apath_at av c qs | None => None end.
Proof.
  revert d. induction ps as [| s ps IH]; intros d; [reflexivity |].
  cbn [app]. rewrite !apath_at_cons.
  destruct (astep av d s) as [c |]; [apply IH | reflexivity].
Qed.

(* ---------------------------------------------------------------------
   2a.  THE RUN: a walk's answer, index by index

   [apath_at] is the ANSWER; a pinned walk needs the inums it VISITS, one
   per hop, because the client's shares are per-inum and the walk's hop
   family is indexed by hop number ([SpecNameiTr.nx_hops_from] is a
   [big_sepL] over the path elements).  [arun av d ps ds] is exactly that
   list: [ds] is [d] followed by each hop's answer, so [length ds =
   S (length ps)] and [ds !!! length ps] is [apath_at]'s answer.
   --------------------------------------------------------------------- *)

Inductive arun (av : aview) : Z -> list fname -> list Z -> Prop :=
| ARun_nil (d : Z) : arun av d [] [d]
| ARun_cons (d c : Z) (s : fname) (ps : list fname) (ds : list Z) :
    astep av d s = Some c -> arun av c ps ds -> arun av d (s :: ps) (d :: ds).

Lemma arun_length (av : aview) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> length ds = S (length ps).
Proof.
  induction 1 as [d0 | d0 c s0 ps0 ds0 Hst Hr IH];
    [reflexivity | by rewrite /= IH].
Qed.

Lemma arun_lookup_0 (av : aview) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> ds !! 0%nat = Some d.
Proof. by destruct 1. Qed.

Lemma arun_head (av : aview) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> ds !!! 0%nat = d.
Proof.
  intros Hr. exact (list_lookup_total_correct _ _ _ (arun_lookup_0 _ _ _ _ Hr)).
Qed.

Lemma arun_apath (av : aview) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> apath_at av d ps = ds !! length ps.
Proof.
  induction 1 as [| d0 c s0 ps0 ds0 Hst Hr IH]; [reflexivity |].
  by rewrite apath_at_cons Hst IH.
Qed.

Lemma arun_apath_tot (av : aview) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> apath_at av d ps = Some (ds !!! length ps).
Proof.
  intros Hr. rewrite (arun_apath _ _ _ _ Hr).
  destruct (ds !! length ps) as [c |] eqn:Hl.
  - by rewrite (list_lookup_total_correct _ _ _ Hl).
  - apply lookup_ge_None in Hl. rewrite (arun_length _ _ _ _ Hr) in Hl. lia.
Qed.

Lemma arun_step (av : aview) (d : Z) (ps : list fname) (ds : list Z)
    (k : nat) (s : fname) :
  arun av d ps ds -> ps !! k = Some s ->
  exists c1 c2, ds !! k = Some c1 /\ ds !! S k = Some c2
                /\ astep av c1 s = Some c2.
Proof.
  intros Hr. revert k.
  induction Hr as [d0 | d0 c s0 ps0 ds0 Hst Hr IH]; intros k Hk.
  - destruct k; discriminate.
  - destruct k as [| k'].
    + cbn in Hk. apply Some_inj in Hk. subst s0.
      exists d0, c. split; [reflexivity |]. split; [| exact Hst].
      cbn. exact (arun_lookup_0 _ _ _ _ Hr).
    + cbn in Hk. destruct (IH k' Hk) as (c1 & c2 & H1 & H2 & H3).
      exists c1, c2. by cbn.
Qed.

Lemma arun_step_tot (av : aview) (d : Z) (ps : list fname) (ds : list Z)
    (k : nat) (s : fname) :
  arun av d ps ds -> ps !! k = Some s ->
  astep av (ds !!! k) s = Some (ds !!! S k).
Proof.
  intros Hr Hk. destruct (arun_step _ _ _ _ _ _ Hr Hk) as (c1 & c2 & H1 & H2 & H3).
  by rewrite (list_lookup_total_correct _ _ _ H1)
             (list_lookup_total_correct _ _ _ H2).
Qed.

(* the converse: an answer HAS a run, so nothing is lost by stating the
   pinned walk over [arun] rather than over [apath_at] *)
Lemma apath_at_arun (av : aview) (d : Z) (ps : list fname) (i : Z) :
  apath_at av d ps = Some i ->
  exists ds, arun av d ps ds /\ ds !!! length ps = i.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hp.
  - exists [d]. split; [constructor |]. cbn in Hp. by apply Some_inj in Hp.
  - rewrite apath_at_cons in Hp.
    destruct (astep av d s) as [c |] eqn:Hst; [| discriminate].
    destruct (IH c Hp) as (ds & Hr & _).
    assert (Hr' : arun av d (s :: ps) (d :: ds)) by (econstructor; eauto).
    exists (d :: ds). split; [exact Hr' |].
    pose proof (arun_apath_tot _ _ _ _ Hr') as He.
    rewrite apath_at_cons Hst Hp in He.
    symmetry. by apply Some_inj in He.
Qed.

(* ===================================================================== *)
(*  3a'. [abs_view]: THE RAW γtop MAP, READ THROUGH [abs_of]             *)
(* ===================================================================== *)

(* Hoisted out of FsAbs.v's [FsAbsCarrier] section (it mentioned no section
   variable, so the closed constant is the same term with the same
   arguments).  [astate] -- the iProp that reads the authority through
   this -- stays in FsAbs.v. *)
(* OVER THE RAW MAP since durable-disk EV (header, consequence (1)): it is
   the form [InodeRegion.ftop_body] holds, and at [I := fss_inodes S] it is
   the old function on the nose. *)
Definition abs_view (I : gmap Z fs_node) : aview := abs_of <$> I.

Lemma abs_view_lookup I i n :
  I !! i = Some n -> abs_view I !! i = Some (abs_of n).
Proof. intros Hi. by rewrite /abs_view lookup_fmap Hi. Qed.

Lemma abs_view_lookup_is_Some (I : gmap Z fs_node) (i : Z) (a : anode) :
  abs_view I !! i = Some a -> is_Some (I !! i).
Proof.
  rewrite /abs_view lookup_fmap. intros Ha.
  destruct (I !! i) as [n |]; [by exists n | discriminate].
Qed.

(* A RETAG THAT KEEPS THE READING KEEPS THE VIEW (app-instances.md section 7,
   the [_same] mover form): block addresses and records are invisible to
   user code, so a node moved to another node with the same [abs_of] moves
   nothing an application can see. *)
Lemma abs_view_insert_same (I : gmap Z fs_node) (i : Z) (n n' : fs_node) :
  I !! i = Some n -> abs_of n = abs_of n' ->
  abs_view (<[i := n']> I) = abs_view I.
Proof.
  intros Hi Heq. rewrite /abs_view fmap_insert -Heq.
  apply insert_id. by rewrite lookup_fmap Hi.
Qed.
