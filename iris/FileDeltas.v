(* ====================================================================== *)
(*  FileDeltas.v -- THE FILE APPLICATION'S PURE DELTA ALGEBRA: [f_ok] and  *)
(*  the pins under every leg of `f`'s own moves and of the console's.      *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.  [AppFile.v] states the claim; every supplier of a
    write-kind AU ([FileOpen.v], and the program lanes after it) has to
    hand each fire an [AppInv.app_step], and each of those reduces to a
    PURE sentence about the three conjuncts of [AppFile.file_pred] under
    one of [FsAbsDelta]'s legs.  This file is those sentences.

    IT IS [FsConsPin] SECTION 5 AT A NON-DIRECTORY CHILD.  FsConsPin's
    delta lemmas are stated at a DEVICE child -- init's mknod is the only
    create the echo application sees -- and they collapse the fused delta
    by [FsAbsDelta.delta_create_dev].  open(O_CREATE)'s child is
    [AFile []], which collapses by [delta_create_armed] instead, so the
    legs are re-proved here ONCE over a common shape that covers both:

      [name_absent nm av]        the root has no entry [nm]
                                 ([FsConsPin.cons_absent] and
                                  [FsFPin.f_absent] are this, definitionally)
      [node_pin nm ino a av]     the root's [nm] resolves to [ino] and
                                 [ino]'s row is [a]
                                 ([FsConsPin.file_pin] and [cons_present_at]
                                  are this, through their own [_astep] /
                                  [_of_parts] pair)

    so each leg is proved once and read four ways (the file pin, the
    console's present state, `f`'s own present state, and the two absent
    states).

    THE ONE ARITHMETIC FACT (section 5).  `f`'s row and the four pinned
    binaries' rows are at DIFFERENT inums, and nothing in the view says so:
    what says it is the LENGTH.  A typed content is a chunk subset of an
    ADMISSIBLE line ([EchoDisc.line_ok]), hence shorter than
    [EchoDisc.line_max] = 100 bytes, while every pinned binary is 35 KB and
    more.  Two rows with different contents are different rows, hence
    different inums -- which is the side condition [FsConsPin.file_pin_trunc]
    asks of a truncate and its twin asks of an append.                    *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sorting bitvector.definitions.
From iris.proofmode Require Import proofmode.

Require Import FsTree.             (* [DOT], [DOTDOT]                     *)
Require Import FsImg.              (* [ROOTINO]                           *)
Require Import FsImgCheck.         (* [fname_f] and its four peers        *)
Require Import FsAbsDefs.          (* [aview], [astep], [anode]           *)
Require Import FsAbsDelta.         (* the legs                            *)
Require Import FsBlocks.           (* [blk_splice]                        *)
Require Import FsInitPin.          (* [INIT_INO], [init_bytes]            *)
Require Import FsShPin.            (* [SH_INO], [sh_bytes]                *)
Require Import FsEchoPin.          (* [ECHO_INO], [echo_bytes]            *)
Require Import FsCatPin.           (* [CAT_INO], [cat_bytes]              *)
Require Import FsGrepPin.          (* [GREP_INO], [grep_bytes]            *)
Require Import ConsoleInv.         (* [CONSOLE]                           *)
Require Import FsConsPin.          (* [file_pin], [cons_absent/_present]  *)
Require Import FsFPin.             (* [f_absent], [fname_f_ne_*]          *)
Require Import FileFsPure.         (* [file_fs_pure]                      *)
Require Import ElfUser.            (* the four binaries' lengths          *)
Require Import LineWords.
Require Import EchoDisc.           (* [line_ok], [line_max]               *)
Require Import FileState.          (* [fstate], [subseq], [sel_ok]           *)
Require Import AppFile.            (* [f_ok], [f_bytes_typed]             *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  THE NAME `f` AGAINST THE OTHER NAMES A DELTA CAN CARRY             *)
(* ====================================================================== *)

Lemma fname_f_ne_dot : fname_f <> DOT.
Proof using . vm_compute. discriminate. Qed.

Lemma fname_f_ne_dotdot : fname_f <> DOTDOT.
Proof using . vm_compute. discriminate. Qed.

Lemma fname_f_ne_console : fname_f <> fname_console.
Proof using . vm_compute. discriminate. Qed.

Lemma fname_console_ne_f : fname_console <> fname_f.
Proof using . intros H. exact (fname_f_ne_console (eq_sym H)). Qed.

(* THE NAMES sh MAY CREATE (the owner's ruling of 2026-09-22).  The create
   the kernel asks the file claim to absorb is at a name of THIS shape and
   nowhere else ([FsAbsCreateNm]'s name predicate, threaded through
   open(O_CREATE)) -- a PREFIX PATTERN, so that the model's one file is an
   inhabitant and the console's name is not, whichever the prefix.  Today
   the prefix is the file name itself; a wider one ("out*") is a change
   of this one constant and of nothing below it. *)
Definition redir_prefix : fname := fname_f.
Definition redir_name_ok (nm : fname) : Prop := prefix redir_prefix nm.

Lemma redir_name_ok_f : redir_name_ok fname_f.
Proof using . exists []. by rewrite app_nil_r. Qed.

Lemma redir_name_ok_ne_console (nm : fname) :
  redir_name_ok nm -> nm <> fname_console.
Proof using . intros [k ->] H. vm_compute in H. discriminate H. Qed.

(* ====================================================================== *)
(*  1.  THE TWO SHAPES, AND THE FOUR READINGS OF THEM                      *)
(* ====================================================================== *)

Definition name_absent (nm : fname) (av : aview) : Prop :=
  astep av ROOTINO nm = None.

Definition node_pin (nm : fname) (ino : Z) (a : anode) (av : aview) : Prop :=
  astep av ROOTINO nm = Some ino /\ av !! ino = Some a.

(* ---- the readings ---------------------------------------------------- *)

Lemma name_absent_cons (av : aview) : name_absent fname_console av <-> cons_absent av.
Proof using . reflexivity. Qed.

Lemma name_absent_f (av : aview) : name_absent fname_f av <-> f_absent av.
Proof using . reflexivity. Qed.

Lemma node_pin_of_file_pin (nm : fname) (ino : Z) (bs : list (bv 8))
    (av : aview) :
  file_pin nm ino bs av -> node_pin nm ino (MkAnode (AFile bs) 1%nat) av.
Proof using .
  intros Hp. split; [ exact (file_pin_astep nm ino bs av Hp) |].
  by destruct Hp as (_ & H & _).
Qed.

Lemma file_pin_of_node_pin (nm : fname) (ino : Z) (bs : list (bv 8))
    (av : aview) :
  node_pin nm ino (MkAnode (AFile bs) 1%nat) av -> file_pin nm ino bs av.
Proof using . intros [Hs Hr]. exact (file_pin_of_parts nm ino bs av Hs Hr). Qed.

Lemma node_pin_of_cons (i : Z) (av : aview) :
  cons_present_at i av -> node_pin fname_console i cons_dev av.
Proof using .
  intros Hp. split; [ exact (cons_present_astep i av Hp) |].
  by destruct Hp as (_ & H & _).
Qed.

Lemma cons_of_node_pin (i : Z) (av : aview) :
  node_pin fname_console i cons_dev av -> cons_present_at i av.
Proof using . intros [Hs Hr]. exact (cons_present_of_parts i av Hs Hr). Qed.

(* ---- the two structural consequences every leg below uses ------------- *)

(* a pinned name's root IS a directory holding it *)
Lemma node_pin_root (nm : fname) (ino : Z) (a : anode) (av : aview) :
  node_pin nm ino a av ->
  exists (ents : gmap fname Z) (nl : nat),
    av !! ROOTINO = Some (MkAnode (ADir ents) nl) /\ ents !! nm = Some ino.
Proof using .
  intros [Hst _]. rewrite /astep /aents in Hst.
  destruct (av !! ROOTINO) as [a0 |] eqn:Ha; [| discriminate Hst].
  rewrite /= /anode_ents in Hst.
  destruct a0 as [n nl]. destruct n as [b | ents | ma mi]; try discriminate Hst.
  exists ents, nl. split; [reflexivity | exact Hst].
Qed.

Lemma node_pin_of_parts (nm : fname) (ino : Z) (a : anode) (av : aview) :
  astep av ROOTINO nm = Some ino -> av !! ino = Some a -> node_pin nm ino a av.
Proof using . by split. Qed.

(* the two shape side conditions every leg below asks of a pinned node,
   hoisted so no proof re-runs [cbn] on the record projection *)
Lemma file_row_nondir (bs : list (bv 8)) (nl : nat) :
  forall e : gmap fname Z, an_node (MkAnode (AFile bs) nl) <> ADir e.
Proof using . intros e Hc. cbn in Hc. discriminate Hc. Qed.

Lemma dir_row_nonfile (ents : gmap fname Z) (nl : nat) :
  forall bs : list (bv 8), an_node (MkAnode (ADir ents) nl) <> AFile bs.
Proof using . intros bs Hc. cbn in Hc. discriminate Hc. Qed.

Lemma dev_row_nondir (ma mi : Z) (nl : nat) :
  forall e : gmap fname Z, an_node (MkAnode (ADev ma mi) nl) <> ADir e.
Proof using . intros e Hc. cbn in Hc. discriminate Hc. Qed.

Lemma dev_row_nonfile (ma mi : Z) (nl : nat) :
  forall bs : list (bv 8), an_node (MkAnode (ADev ma mi) nl) <> AFile bs.
Proof using . intros bs Hc. cbn in Hc. discriminate Hc. Qed.

(* ====================================================================== *)
(*  2.  THE LEGS                                                           *)
(* ====================================================================== *)

(* ---- 2a.  THE ARM ---------------------------------------------------- *)

Lemma name_absent_arm (nm : fname) (i : Z) (c : absnode) (av : aview) :
  (forall e : gmap fname Z, c <> ADir e) ->
  name_absent nm av -> name_absent nm (delta_arm i c av).
Proof using .
  intros Hnd. rewrite /name_absent /astep /aents /delta_arm. intros Habs.
  destruct (decide (i = ROOTINO)) as [-> | Hne].
  - rewrite lookup_insert /= /anode_ents /=.
    destruct c as [bs | e | ma mi]; [reflexivity | | reflexivity].
    exfalso. exact (Hnd e eq_refl).
  - rewrite lookup_insert_ne; [exact Habs | congruence].
Qed.

Lemma node_pin_arm (nm : fname) (ino : Z) (a : anode) (i : Z) (c : absnode)
    (av : aview) :
  av !! i = None ->
  node_pin nm ino a av -> node_pin nm ino a (delta_arm i c av).
Proof using .
  intros Hfree Hp.
  destruct (node_pin_root nm ino a av Hp) as (ents & nl & Hroot & Hnm).
  destruct Hp as (_ & Hrow).
  assert (Hne_root : i <> ROOTINO) by (intros ->; by rewrite Hroot in Hfree).
  assert (Hne_ino : i <> ino) by (intros ->; by rewrite Hrow in Hfree).
  apply node_pin_of_parts.
  - rewrite /astep /aents (delta_arm_lookup_same av i c ROOTINO
                             ltac:(congruence)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_arm_lookup_same av i c ino ltac:(congruence)). exact Hrow.
Qed.

(* ---- 2b.  THE UNARM -------------------------------------------------- *)

Lemma name_absent_unarm (nm : fname) (i : Z) (av : aview) :
  name_absent nm av -> name_absent nm (delta_unarm i av).
Proof using .
  rewrite /name_absent /astep /aents /delta_unarm. intros Habs.
  destruct (decide (i = ROOTINO)) as [-> | Hne].
  - by rewrite lookup_delete /=.
  - rewrite lookup_delete_ne; [exact Habs | congruence].
Qed.

Lemma node_pin_unarm (nm : fname) (ino : Z) (a : anode) (i : Z) (av : aview) :
  i <> ROOTINO -> i <> ino ->
  node_pin nm ino a av -> node_pin nm ino a (delta_unarm i av).
Proof using .
  intros Hr Hi Hp.
  destruct (node_pin_root nm ino a av Hp) as (ents & nl & Hroot & Hnm).
  destruct Hp as (_ & Hrow).
  apply node_pin_of_parts.
  - rewrite /astep /aents (delta_unarm_lookup_ne av i ROOTINO
                             ltac:(congruence)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_unarm_lookup_ne av i ino ltac:(congruence)). exact Hrow.
Qed.

(* ...at an inum the ARM's own view did not have, which is what
   [FsAbsCreateFire.cre_arm_fired] hands its consumer *)
Lemma node_pin_unarm_fresh (nm : fname) (ino : Z) (a : anode) (i : Z)
    (av0 av : aview) :
  av0 !! i = None ->
  node_pin nm ino a av0 ->
  node_pin nm ino a av -> node_pin nm ino a (delta_unarm i av).
Proof using .
  intros Hfree Hp0 Hp.
  destruct (node_pin_root nm ino a av0 Hp0) as (ents & nl & Hroot & _).
  destruct Hp0 as (_ & Hrow0).
  assert (Hne_root : i <> ROOTINO) by (intros ->; by rewrite Hroot in Hfree).
  assert (Hne_ino : i <> ino) by (intros ->; by rewrite Hrow0 in Hfree).
  exact (node_pin_unarm nm ino a i av Hne_root Hne_ino Hp).
Qed.

(* ---- 2c.  THE PARENT LEG (create), AT A NON-DIRECTORY CHILD ---------- *)

(* [FsAbsDelta.delta_create_armed]'s collapse: with the child ARMED and
   distinct from its parent, the fused delta is the one-row parent insert.
   [cre_pre_ne] supplies [d <> i] at every non-directory child. *)
Lemma delta_create_nd (av : aview) (d : Z) (nmn : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  delta_create d nmn i c av
  = <[d := MkAnode (ADir (<[nmn := i]> ents)) nl]> av.
Proof using .
  intros Hpre Hnd.
  assert (Hne : d <> i) by (eapply cre_pre_ne; [exact Hpre | exact Hnd]).
  rewrite (delta_create_armed av d nmn ents nl i c Hpre Hne).
  destruct c as [bs | e | ma mi]; cbn [acre_bump];
    [ by rewrite Nat.add_0_r | exfalso; exact (Hnd e eq_refl)
    | by rewrite Nat.add_0_r ].
Qed.

Lemma name_absent_create (nm : fname) (d : Z) (nmn : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) (av : aview) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  (d <> ROOTINO \/ nmn <> nm) ->
  name_absent nm av -> name_absent nm (delta_create d nmn i c av).
Proof using .
  intros Hpre Hnd Hother Habs. pose proof Hpre as (Hd & _ & _).
  rewrite (delta_create_nd av d nmn ents nl i c Hpre Hnd).
  rewrite /name_absent /astep /aents.
  destruct (decide (d = ROOTINO)) as [-> | Hdne].
  - rewrite lookup_insert /= /anode_ents /=.
    rewrite /name_absent /astep /aents Hd /= /anode_ents /= in Habs.
    rewrite lookup_insert_ne; [exact Habs |].
    intros ->. destruct Hother as [Hc | Hc];
      [ exact (Hc eq_refl) | exact (Hc eq_refl) ].
  - rewrite lookup_insert_ne; [| congruence]. exact Habs.
Qed.

Lemma node_pin_create (nm : fname) (ino : Z) (a : anode) (d : Z)
    (nmn : fname) (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode)
    (av : aview) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  (forall e : gmap fname Z, an_node a <> ADir e) ->
  node_pin nm ino a av -> node_pin nm ino a (delta_create d nmn i c av).
Proof using .
  intros Hpre Hnd Hand Hp. pose proof Hpre as (Hd & Hfresh & _).
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow).
  assert (Hd_ino : d <> ino).
  { intros ->. rewrite Hrow in Hd. injection Hd as Hc'.
    exact (Hand ents (f_equal an_node Hc')). }
  rewrite (delta_create_nd av d nmn ents nl i c Hpre Hnd).
  apply node_pin_of_parts.
  - rewrite /astep /aents.
    destruct (decide (d = ROOTINO)) as [-> | Hdne].
    + rewrite lookup_insert /= /anode_ents /=.
      rewrite Hroot in Hd. injection Hd as Hents Hnl. subst rents.
      rewrite lookup_insert_ne; [exact Hnm |].
      intros <-. by rewrite Hnm in Hfresh.
    + rewrite lookup_insert_ne; [| congruence].
      rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite lookup_insert_ne; [exact Hrow | congruence].
Qed.

(* ...AND THE MOVE ITSELF: at the root, under [nmn], the name goes from
   ABSENT to PRESENT at the child the create armed. *)
Lemma node_pin_create_at (nmn : fname) (ents : gmap fname Z) (nl : nat)
    (i : Z) (c : absnode) (av : aview) :
  cre_pre av ROOTINO nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  node_pin nmn i (MkAnode c 1%nat) (delta_create ROOTINO nmn i c av).
Proof using .
  intros Hpre Hnd. pose proof Hpre as (Hd & _ & Hchild).
  assert (Hne : ROOTINO <> i) by (eapply cre_pre_ne; [exact Hpre | exact Hnd]).
  rewrite (delta_create_nd av ROOTINO nmn ents nl i c Hpre Hnd).
  apply node_pin_of_parts.
  - rewrite /astep /aents lookup_insert /= /anode_ents /=. apply lookup_insert.
  - rewrite lookup_insert_ne; [exact Hchild | congruence].
Qed.

(* ---- 2d.  THE DOTS --------------------------------------------------- *)

Lemma name_absent_dots (nm : fname) (i d : Z) (full : bool) (av : aview) :
  nm <> DOT -> nm <> DOTDOT ->
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  name_absent nm av -> name_absent nm (dots_delta full i d av).
Proof using .
  intros Hd1 Hd2 Hi Habs.
  rewrite (dots_delta_fresh av i d full Hi).
  rewrite /name_absent /astep /aents.
  destruct (decide (i = ROOTINO)) as [-> | Hne].
  - rewrite lookup_insert /= /anode_ents /= /dots_ents.
    destruct full.
    + rewrite lookup_insert_ne; [| congruence].
      rewrite lookup_insert_ne; [| congruence]. apply lookup_empty.
    + rewrite lookup_insert_ne; [| congruence]. apply lookup_empty.
  - rewrite lookup_insert_ne; [exact Habs | congruence].
Qed.

Lemma node_pin_dots (nm : fname) (ino : Z) (a : anode) (i d : Z)
    (full : bool) (av : aview) :
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  (forall e : gmap fname Z, an_node a <> ADir e) ->
  node_pin nm ino a av -> node_pin nm ino a (dots_delta full i d av).
Proof using .
  intros Hi Hand Hp.
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (Hst & Hrow).
  assert (Hne_root : i <> ROOTINO).
  { intros ->. rewrite Hroot in Hi. injection Hi as Hents _. subst rents.
    rewrite lookup_empty in Hnm. discriminate Hnm. }
  assert (Hne_ino : i <> ino).
  { intros ->. rewrite Hrow in Hi. injection Hi as Hc'.
    exact (Hand ∅ (f_equal an_node Hc')). }
  rewrite (dots_delta_fresh av i d full Hi).
  apply node_pin_of_parts.
  - rewrite /astep /aents lookup_insert_ne; [| congruence].
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite lookup_insert_ne; [exact Hrow | congruence].
Qed.

(* ---- 2e.  THE TRUNCATE ----------------------------------------------- *)

Lemma name_absent_trunc (nm : fname) (i : Z) (av : aview) :
  name_absent nm av -> name_absent nm (delta_trunc i av).
Proof using .
  intros Habs. rewrite /name_absent /astep in Habs |- *.
  destruct (delta_trunc_aents av i ROOTINO) as [He | He];
    rewrite He; [exact Habs | reflexivity].
Qed.

Lemma node_pin_trunc_ne (nm : fname) (ino : Z) (a : anode) (i : Z)
    (av : aview) :
  i <> ino ->
  (forall e : gmap fname Z, an_node a <> ADir e) ->
  node_pin nm ino a av -> node_pin nm ino a (delta_trunc i av).
Proof using .
  intros Hne Hand Hp.
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow).
  apply node_pin_of_parts.
  - rewrite /astep /aents
      (delta_trunc_nonfile av i ROOTINO (ADir rents) rnl Hroot
         (dir_row_nonfile rents rnl)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_trunc_lookup_ne av i ino ltac:(congruence)). exact Hrow.
Qed.

(* ...and at a NON-FILE row the truncate is the identity whatever [i] is:
   [FsConsPin.cons_present_trunc]'s reason, stated once. *)
Lemma node_pin_trunc_nonfile (nm : fname) (ino : Z) (a : anode) (i : Z)
    (av : aview) :
  (forall bs : list (bv 8), an_node a <> AFile bs) ->
  node_pin nm ino a av -> node_pin nm ino a (delta_trunc i av).
Proof using .
  intros Hanf Hp.
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow). destruct a as [n nl].
  apply node_pin_of_parts.
  - rewrite /astep /aents
      (delta_trunc_nonfile av i ROOTINO (ADir rents) rnl Hroot
         (dir_row_nonfile rents rnl)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_trunc_nonfile av i ino n nl Hrow Hanf). exact Hrow.
Qed.

(* ---- 2f.  THE WRITE -------------------------------------------------- *)

Lemma delta_write_nonfile (av : aview) (i k : Z) (off : nat)
    (new : list (bv 8)) (n : absnode) (nl : nat) :
  av !! k = Some (MkAnode n nl) ->
  (forall bs : list (bv 8), n <> AFile bs) ->
  delta_write i off new av !! k = av !! k.
Proof using .
  intros Hk Hn.
  destruct (decide (k = i)) as [-> | Hne]; [| by apply delta_write_other].
  rewrite /delta_write Hk /=.
  destruct n as [bs | e | ma mi];
    [ exfalso; exact (Hn bs eq_refl) | congruence | congruence ].
Qed.

Lemma delta_write_aents (av : aview) (j : Z) (off : nat)
    (new : list (bv 8)) (d : Z) :
  aents (delta_write j off new av) d = aents av d
  \/ aents (delta_write j off new av) d = None.
Proof using .
  destruct (decide (d = j)) as [-> | Hne]; last first.
  { left. rewrite /aents (delta_write_other av j off new d Hne). reflexivity. }
  destruct (av !! j) as [a |] eqn:Hj; last first.
  { left. rewrite /delta_write Hj. reflexivity. }
  destruct a as [n nl]. destruct n as [bs | e | ma mi].
  - right. rewrite /aents /delta_write Hj /= lookup_insert /= /anode_ents /=.
    reflexivity.
  - left. rewrite /delta_write Hj /=. reflexivity.
  - left. rewrite /delta_write Hj /=. reflexivity.
Qed.

Lemma name_absent_write (nm : fname) (i : Z) (off : nat)
    (new : list (bv 8)) (av : aview) :
  name_absent nm av -> name_absent nm (delta_write i off new av).
Proof using .
  intros Habs. rewrite /name_absent /astep in Habs |- *.
  destruct (delta_write_aents av i off new ROOTINO) as [He | He];
    rewrite He; [exact Habs | reflexivity].
Qed.

Lemma node_pin_write_ne (nm : fname) (ino : Z) (a : anode) (i : Z)
    (off : nat) (new : list (bv 8)) (av : aview) :
  i <> ino ->
  (forall e : gmap fname Z, an_node a <> ADir e) ->
  node_pin nm ino a av -> node_pin nm ino a (delta_write i off new av).
Proof using .
  intros Hne Hand Hp.
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow).
  apply node_pin_of_parts.
  - rewrite /astep /aents
      (delta_write_nonfile av i ROOTINO off new (ADir rents) rnl Hroot
         (dir_row_nonfile rents rnl)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_write_other av i off new ino ltac:(congruence)). exact Hrow.
Qed.

Lemma node_pin_write_nonfile (nm : fname) (ino : Z) (a : anode) (i : Z)
    (off : nat) (new : list (bv 8)) (av : aview) :
  (forall bs : list (bv 8), an_node a <> AFile bs) ->
  node_pin nm ino a av -> node_pin nm ino a (delta_write i off new av).
Proof using .
  intros Hanf Hp.
  destruct (node_pin_root nm ino a av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow). destruct a as [n nl].
  apply node_pin_of_parts.
  - rewrite /astep /aents
      (delta_write_nonfile av i ROOTINO off new (ADir rents) rnl Hroot
         (dir_row_nonfile rents rnl)).
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite (delta_write_nonfile av i ino off new n nl Hrow Hanf). exact Hrow.
Qed.

(* ====================================================================== *)
(*  3.  [f_ok] UNDER EVERY LEG                                             *)
(*                                                                        *)
(*  [AppFile.f_ok av s] is [name_absent fname_f av] at [s = None] and      *)
(*  [node_pin fname_f i (MkAnode (AFile bs) 1) av] at [s = Some (i, bs)] --*)
(*  THE INUM IS IN THE STATE (lane F-WRITE's relay 1), so every leg below  *)
(*  is section 2 read at that name and at the state's own inum, and a free *)
(*  step can no longer relocate `f`.                                       *)
(* ====================================================================== *)

Lemma f_ok_none (av : aview) : f_ok av None <-> name_absent fname_f av.
Proof using . reflexivity. Qed.

Lemma f_ok_some_iff (av : aview) (i : Z) (bs : list (bv 8)) :
  f_ok av (Some (i, bs)) <-> node_pin fname_f i (MkAnode (AFile bs) 1%nat) av.
Proof using . reflexivity. Qed.

Lemma f_ok_some (av : aview) (i : Z) (bs : list (bv 8)) :
  astep av ROOTINO fname_f = Some i ->
  av !! i = Some (MkAnode (AFile bs) 1%nat) -> f_ok av (Some (i, bs)).
Proof using . by split. Qed.

(* THE STATE IS THE VIEW'S OWN READING: one view admits at most one [s]
   ([AppFile.f_ok_fcontent] read as determinacy). *)
Lemma f_ok_det (av : aview) (s s' : dst) : f_ok av s -> f_ok av s' -> s = s'.
Proof using .
  intros H H'. rewrite -(f_ok_fcontent av s H) -(f_ok_fcontent av s' H') //.
Qed.

(* a create at `f` in the root has `f` absent at the instant it fires --
   [cre_pre]'s middle conjunct read at this name, and the fact that turns
   the create's own leg into a REFUTATION at a present deed *)
Lemma cre_pre_f_absent (av : aview) (ents : gmap fname Z) (nl : nat)
    (i : Z) (c : absnode) :
  cre_pre av ROOTINO fname_f ents nl i c -> f_ok av None.
Proof using .
  intros (Hd & Hfresh & _).
  rewrite /f_ok /f_absent /astep /aents Hd /= /anode_ents /=. exact Hfresh.
Qed.

(* the root is a DIRECTORY, so `f`'s own row is never at [ROOTINO] *)
Lemma f_row_ne_root (av : aview) (i : Z) (bs : list (bv 8)) (nl : nat) :
  astep av ROOTINO fname_f = Some i ->
  av !! i = Some (MkAnode (AFile bs) nl) -> ROOTINO <> i.
Proof using .
  intros Hst Hrow Heq. rewrite -Heq in Hrow.
  rewrite /astep /aents Hrow /= /anode_ents /= in Hst. discriminate Hst.
Qed.

(* ---- 3a.  THE LEGS THAT LEAVE `f` ALONE ------------------------------ *)

Lemma f_ok_arm (i : Z) (c : absnode) (av : aview) (s : dst) :
  av !! i = None -> (forall e : gmap fname Z, c <> ADir e) ->
  f_ok av s -> f_ok (delta_arm i c av) s.
Proof using .
  intros Hfree Hnd. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_arm fname_f i c av Hnd). }
  intros Hp. exact (node_pin_arm fname_f i0 _ i c av Hfree Hp).
Qed.

Lemma f_ok_unarm (i : Z) (av : aview) (s : dst) :
  i <> ROOTINO ->
  (forall (j : Z) (bs : list (bv 8)), s = Some (j, bs) -> i <> j) ->
  f_ok av s -> f_ok (delta_unarm i av) s.
Proof using .
  intros Hr Hj. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_unarm fname_f i av). }
  intros Hp.
  exact (node_pin_unarm fname_f i0 _ i av Hr (Hj i0 bs eq_refl) Hp).
Qed.

(* THE ABSENT DEED PAYS NOTHING: a row disappearing cannot make a name
   appear.  This is the whole unarm leg at [s = None]. *)
Lemma f_ok_unarm_none (i : Z) (av : aview) :
  f_ok av None -> f_ok (delta_unarm i av) None.
Proof using . apply (name_absent_unarm fname_f i av). Qed.

(* ...AND AT A PRESENT DEED THE LEG IS FREE TOO, which is what the INUM in
   the state buys (lane F-WRITE's relay 1).  The arm's own receipt carries
   [av0 !! i = None] and the claim read at [av0] carries `f`'s row AT THE
   DEED'S INUM, so the armed inum is neither the root's nor `f`'s -- and
   the deed's inum does not move between the two views, because it is the
   deed's and the deed is in the holder's hand. *)
Lemma f_ok_unarm_fresh (i : Z) (av0 av : aview) (s : dst) :
  av0 !! i = None -> f_ok av0 s -> f_ok av s -> f_ok (delta_unarm i av) s.
Proof using .
  intros Hfree. destruct s as [[i0 bs] |]; last first.
  { intros _ H. exact (name_absent_unarm fname_f i av H). }
  intros Hp0 Hp.
  exact (node_pin_unarm_fresh fname_f i0 _ i av0 av Hfree Hp0 Hp).
Qed.

Lemma f_ok_create_other (d : Z) (nmn : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (c : absnode) (av : aview) (s : dst) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  (d <> ROOTINO \/ nmn <> fname_f) ->
  f_ok av s -> f_ok (delta_create d nmn i c av) s.
Proof using .
  intros Hpre Hnd Hother. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_create fname_f d nmn ents nl i c av Hpre Hnd Hother). }
  intros Hp.
  exact (node_pin_create fname_f i0 _ d nmn ents nl i c av Hpre Hnd
           (file_row_nondir _ _) Hp).
Qed.

Lemma f_ok_dots (i d : Z) (full : bool) (av : aview) (s : dst) :
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  f_ok av s -> f_ok (dots_delta full i d av) s.
Proof using .
  intros Hi. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_dots fname_f i d full av fname_f_ne_dot
             fname_f_ne_dotdot Hi). }
  intros Hp.
  exact (node_pin_dots fname_f i0 _ i d full av Hi
           (file_row_nondir _ _) Hp).
Qed.

Lemma f_ok_trunc_ne (i : Z) (av : aview) (s : dst) :
  (forall (j : Z) (bs : list (bv 8)), s = Some (j, bs) -> i <> j) ->
  f_ok av s -> f_ok (delta_trunc i av) s.
Proof using .
  intros Hj. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_trunc fname_f i av). }
  intros Hp.
  exact (node_pin_trunc_ne fname_f i0 _ i av (Hj i0 bs eq_refl)
           (file_row_nondir _ _) Hp).
Qed.

(* TRUNCATING AN EMPTY `f` IS THE IDENTITY, whatever inum the call reached:
   off `f`'s own row the leg is [f_ok_trunc_ne], and at it the row is
   already [AFile []].  This is what makes open(O_CREATE|O_TRUNC)'s
   truncate free on the FRESH arm. *)
Lemma f_ok_trunc_nil (i i0 : Z) (av : aview) :
  f_ok av (Some (i0, [])) -> f_ok (delta_trunc i av) (Some (i0, [])).
Proof using .
  intros Hp.
  destruct (decide (i = i0)) as [-> | Hne].
  - destruct (node_pin_root fname_f i0 (MkAnode (AFile []) 1%nat) av Hp)
      as (rents & rnl & Hroot & Hnm).
    destruct Hp as (Hst & Hrow). split.
    + rewrite /astep /aents
        (delta_trunc_nonfile av i0 ROOTINO (ADir rents) rnl Hroot
           (dir_row_nonfile rents rnl)).
      exact Hst.
    + exact (delta_trunc_lookup av i0 [] 1%nat Hrow).
  - exact (node_pin_trunc_ne fname_f i0 (MkAnode (AFile []) 1%nat) i av
             ltac:(congruence) (file_row_nondir _ _) Hp).
Qed.

Lemma f_ok_write_ne (i : Z) (off : nat) (new : list (bv 8)) (av : aview)
    (s : dst) :
  (forall (j : Z) (bs : list (bv 8)), s = Some (j, bs) -> i <> j) ->
  f_ok av s -> f_ok (delta_write i off new av) s.
Proof using .
  intros Hj. destruct s as [[i0 bs] |]; last first.
  { apply (name_absent_write fname_f i off new av). }
  intros Hp.
  exact (node_pin_write_ne fname_f i0 _ i off new av (Hj i0 bs eq_refl)
           (file_row_nondir _ _) Hp).
Qed.

(* ---- 3b.  `f`'s OWN THREE MOVES -------------------------------------- *)

(* THE CREATE: the root gains `f`, at the child the arm minted -- an empty
   file at one link, and the deed's new inum IS that child. *)
Lemma f_ok_create_f (ents : gmap fname Z) (nl : nat) (i : Z) (av : aview) :
  cre_pre av ROOTINO fname_f ents nl i (AFile []) ->
  f_ok (delta_create ROOTINO fname_f i (AFile []) av) (Some (i, [])).
Proof using .
  intros Hpre.
  exact (node_pin_create_at fname_f ents nl i (AFile []) av Hpre
           ltac:(intros e Hc; discriminate Hc)).
Qed.

(* THE TRUNCATE, AT `f`'s OWN INUM: the deed names it, so the leg needs no
   walk to identify the row. *)
Lemma f_ok_trunc_f (i : Z) (bs : list (bv 8)) (av : aview) :
  f_ok av (Some (i, bs)) -> f_ok (delta_trunc i av) (Some (i, [])).
Proof using .
  intros (Hst & Hrow).
  pose proof (f_row_ne_root av i bs 1%nat Hst Hrow) as Hr.
  split.
  - rewrite /astep /aents (delta_trunc_lookup_ne av i ROOTINO Hr). exact Hst.
  - exact (delta_trunc_lookup av i bs 1%nat Hrow).
Qed.

(* THE WRITE, AT `f`'s OWN INUM *)
Lemma f_ok_write_f (i : Z) (off : nat) (new bs0 : list (bv 8)) (av : aview) :
  f_ok av (Some (i, bs0)) ->
  f_ok (delta_write i off new av) (Some (i, blk_splice off new bs0)).
Proof using .
  intros (Hst & Hrow).
  pose proof (f_row_ne_root av i bs0 1%nat Hst Hrow) as Hr.
  split.
  - rewrite /astep /aents (delta_write_other av i off new ROOTINO Hr). exact Hst.
  - exact (delta_write_lookup av i off new bs0 1%nat Hrow).
Qed.

(* ...and the APPEND is the write at the end: echo's chunk lands at
   [off = |bs0|] and the content is the concatenation. *)
Lemma blk_splice_append (off : nat) (new bs0 : list (bv 8)) :
  off = length bs0 -> blk_splice off new bs0 = bs0 ++ new.
Proof using .
  intros ->. rewrite /blk_splice take_ge; [| lia].
  rewrite drop_ge; [| lia]. by rewrite app_nil_r.
Qed.

Lemma f_ok_append_f (i : Z) (new bs0 : list (bv 8)) (av : aview) :
  f_ok av (Some (i, bs0)) ->
  f_ok (delta_write i (length bs0) new av) (Some (i, bs0 ++ new)).
Proof using .
  intros Hok.
  rewrite -(blk_splice_append (length bs0) new bs0 eq_refl).
  exact (f_ok_write_f i (length bs0) new bs0 av Hok).
Qed.

(* ====================================================================== *)
(*  4.  THE PINS AND THE CONSOLE UNDER `f`'s MOVES                         *)
(*                                                                        *)
(*  [FileFsPure.file_fs_pure] is five [FsConsPin.file_pin]s and            *)
(*  [AppEcho.cons_state]'s guards are [cons_absent] / [cons_present_at],   *)
(*  so section 2's two shapes carry all of them.                           *)
(* ====================================================================== *)

Lemma file_pin_cat (av : aview) :
  file_pin fname_cat CAT_INO cat_bytes av <-> era0_cat_pins av.
Proof using . rewrite /file_pin /era0_cat_pins /cat_path. reflexivity. Qed.

Lemma file_pin_grep (av : aview) :
  file_pin fname_grep GREP_INO grep_bytes av <-> era0_grep_pins av.
Proof using . rewrite /file_pin /era0_grep_pins /grep_path. reflexivity. Qed.

(* the five pins, as one list of [node_pin]s *)
Lemma file_fs_pure_pins (av : aview) :
  file_fs_pure av ->
  node_pin fname_init INIT_INO (MkAnode (AFile init_bytes) 1%nat) av
  /\ node_pin fname_sh SH_INO (MkAnode (AFile sh_bytes) 1%nat) av
  /\ node_pin fname_echo ECHO_INO (MkAnode (AFile echo_bytes) 1%nat) av
  /\ node_pin fname_cat CAT_INO (MkAnode (AFile cat_bytes) 1%nat) av
  /\ node_pin fname_grep GREP_INO (MkAnode (AFile grep_bytes) 1%nat) av.
Proof using .
  intros [[Hi [Hs He]] [Hc Hg]]. split_and!; apply node_pin_of_file_pin.
  - by apply file_pin_init.
  - by apply file_pin_sh.
  - by apply file_pin_echo.
  - by apply file_pin_cat.
  - by apply file_pin_grep.
Qed.

Lemma file_fs_pure_of_pins (av : aview) :
  node_pin fname_init INIT_INO (MkAnode (AFile init_bytes) 1%nat) av ->
  node_pin fname_sh SH_INO (MkAnode (AFile sh_bytes) 1%nat) av ->
  node_pin fname_echo ECHO_INO (MkAnode (AFile echo_bytes) 1%nat) av ->
  node_pin fname_cat CAT_INO (MkAnode (AFile cat_bytes) 1%nat) av ->
  node_pin fname_grep GREP_INO (MkAnode (AFile grep_bytes) 1%nat) av ->
  file_fs_pure av.
Proof using .
  intros Hi Hs He Hc Hg. split; [split; [| split] | split].
  - apply file_pin_init. by apply file_pin_of_node_pin.
  - apply file_pin_sh. by apply file_pin_of_node_pin.
  - apply file_pin_echo. by apply file_pin_of_node_pin.
  - apply file_pin_cat. by apply file_pin_of_node_pin.
  - apply file_pin_grep. by apply file_pin_of_node_pin.
Qed.

(* the five pinned rows are FILES, which is the side condition every
   [node_pin] leg below asks of the pinned node *)
Definition pinned_row_nondir (bs : list (bv 8))
  : forall e : gmap fname Z, an_node (MkAnode (AFile bs) 1%nat) <> ADir e
  := file_row_nondir bs 1%nat.

Lemma cons_dev_nondir : forall e : gmap fname Z, an_node cons_dev <> ADir e.
Proof using . rewrite /cons_dev. exact (dev_row_nondir CONSOLE 0 1%nat). Qed.

Lemma cons_dev_nonfile : forall bs : list (bv 8), an_node cons_dev <> AFile bs.
Proof using . rewrite /cons_dev. exact (dev_row_nonfile CONSOLE 0 1%nat). Qed.

(* ---- 4a.  THE ARM ---------------------------------------------------- *)

Lemma file_fs_pure_arm (i : Z) (c : absnode) (av : aview) :
  av !! i = None -> file_fs_pure av -> file_fs_pure (delta_arm i c av).
Proof using .
  intros Hfree Hp.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_arm _ _ _ i c av Hfree H1).
  - exact (node_pin_arm _ _ _ i c av Hfree H2).
  - exact (node_pin_arm _ _ _ i c av Hfree H3).
  - exact (node_pin_arm _ _ _ i c av Hfree H4).
  - exact (node_pin_arm _ _ _ i c av Hfree H5).
Qed.

Lemma cons_absent_arm_nd (i : Z) (c : absnode) (av : aview) :
  (forall e : gmap fname Z, c <> ADir e) ->
  cons_absent av -> cons_absent (delta_arm i c av).
Proof using . apply (name_absent_arm fname_console i c av). Qed.

Lemma cons_present_arm_nd (j i : Z) (c : absnode) (av : aview) :
  av !! i = None ->
  cons_present_at j av -> cons_present_at j (delta_arm i c av).
Proof using .
  intros Hfree Hp. apply cons_of_node_pin.
  exact (node_pin_arm fname_console j cons_dev i c av Hfree
           (node_pin_of_cons j av Hp)).
Qed.

(* ---- 4b.  THE UNARM -------------------------------------------------- *)

Lemma file_fs_pure_unarm_fresh (i : Z) (av0 av : aview) :
  av0 !! i = None -> file_fs_pure av0 -> file_fs_pure av ->
  file_fs_pure (delta_unarm i av).
Proof using .
  intros Hfree Hp0 Hp.
  destruct (file_fs_pure_pins av0 Hp0) as (K1 & K2 & K3 & K4 & K5).
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_unarm_fresh _ _ _ i av0 av Hfree K1 H1).
  - exact (node_pin_unarm_fresh _ _ _ i av0 av Hfree K2 H2).
  - exact (node_pin_unarm_fresh _ _ _ i av0 av Hfree K3 H3).
  - exact (node_pin_unarm_fresh _ _ _ i av0 av Hfree K4 H4).
  - exact (node_pin_unarm_fresh _ _ _ i av0 av Hfree K5 H5).
Qed.

Lemma cons_present_unarm_fresh_nd (j i : Z) (av0 av : aview) :
  av0 !! i = None -> cons_present_at j av0 -> cons_present_at j av ->
  cons_present_at j (delta_unarm i av).
Proof using .
  intros Hfree Hp0 Hp. apply cons_of_node_pin.
  exact (node_pin_unarm_fresh fname_console j cons_dev i av0 av Hfree
           (node_pin_of_cons j av0 Hp0) (node_pin_of_cons j av Hp)).
Qed.

(* ---- 4c.  THE CREATE, AT ANY NAME ------------------------------------ *)

Lemma file_fs_pure_create (d : Z) (nmn : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (c : absnode) (av : aview) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  file_fs_pure av -> file_fs_pure (delta_create d nmn i c av).
Proof using .
  intros Hpre Hnd Hp.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_create _ _ _ d nmn ents nl i c av Hpre Hnd
             (pinned_row_nondir init_bytes) H1).
  - exact (node_pin_create _ _ _ d nmn ents nl i c av Hpre Hnd
             (pinned_row_nondir sh_bytes) H2).
  - exact (node_pin_create _ _ _ d nmn ents nl i c av Hpre Hnd
             (pinned_row_nondir echo_bytes) H3).
  - exact (node_pin_create _ _ _ d nmn ents nl i c av Hpre Hnd
             (pinned_row_nondir cat_bytes) H4).
  - exact (node_pin_create _ _ _ d nmn ents nl i c av Hpre Hnd
             (pinned_row_nondir grep_bytes) H5).
Qed.

Lemma cons_absent_create_nd (d : Z) (nmn : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (c : absnode) (av : aview) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  (d <> ROOTINO \/ nmn <> fname_console) ->
  cons_absent av -> cons_absent (delta_create d nmn i c av).
Proof using .
  apply (name_absent_create fname_console d nmn ents nl i c av).
Qed.

Lemma cons_present_create_nd (j d : Z) (nmn : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (c : absnode) (av : aview) :
  cre_pre av d nmn ents nl i c ->
  (forall e : gmap fname Z, c <> ADir e) ->
  cons_present_at j av -> cons_present_at j (delta_create d nmn i c av).
Proof using .
  intros Hpre Hnd Hp. apply cons_of_node_pin.
  exact (node_pin_create fname_console j cons_dev d nmn ents nl i c av
           Hpre Hnd cons_dev_nondir (node_pin_of_cons j av Hp)).
Qed.

(* ---- 4d.  THE DOTS --------------------------------------------------- *)

Lemma file_fs_pure_dots (i d : Z) (full : bool) (av : aview) :
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  file_fs_pure av -> file_fs_pure (dots_delta full i d av).
Proof using .
  intros Hi Hp.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_dots _ _ _ i d full av Hi (pinned_row_nondir _) H1).
  - exact (node_pin_dots _ _ _ i d full av Hi (pinned_row_nondir _) H2).
  - exact (node_pin_dots _ _ _ i d full av Hi (pinned_row_nondir _) H3).
  - exact (node_pin_dots _ _ _ i d full av Hi (pinned_row_nondir _) H4).
  - exact (node_pin_dots _ _ _ i d full av Hi (pinned_row_nondir _) H5).
Qed.

Lemma cons_absent_dots (i d : Z) (full : bool) (av : aview) :
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  cons_absent av -> cons_absent (dots_delta full i d av).
Proof using .
  intros Hi. apply (name_absent_dots fname_console i d full av);
    [ vm_compute; discriminate | vm_compute; discriminate | exact Hi ].
Qed.

Lemma cons_present_dots (j i d : Z) (full : bool) (av : aview) :
  av !! i = Some (MkAnode (ADir ∅) 1%nat) ->
  cons_present_at j av -> cons_present_at j (dots_delta full i d av).
Proof using .
  intros Hi Hp. apply cons_of_node_pin.
  exact (node_pin_dots fname_console j cons_dev i d full av Hi
           cons_dev_nondir (node_pin_of_cons j av Hp)).
Qed.

(* ---- 4e.  THE TRUNCATE AND THE WRITE --------------------------------- *)

(* the console's row is a DEVICE, so a truncate or a write costs it
   nothing at all whatever inum the call reached *)
Lemma cons_absent_trunc_any (i : Z) (av : aview) :
  cons_absent av -> cons_absent (delta_trunc i av).
Proof using . apply (name_absent_trunc fname_console i av). Qed.

Lemma cons_present_trunc_any (j i : Z) (av : aview) :
  cons_present_at j av -> cons_present_at j (delta_trunc i av).
Proof using .
  intros Hp. apply cons_of_node_pin.
  exact (node_pin_trunc_nonfile fname_console j cons_dev i av
           cons_dev_nonfile (node_pin_of_cons j av Hp)).
Qed.

Lemma cons_absent_write_any (i : Z) (off : nat) (new : list (bv 8))
    (av : aview) :
  cons_absent av -> cons_absent (delta_write i off new av).
Proof using . apply (name_absent_write fname_console i off new av). Qed.

Lemma cons_present_write_any (j i : Z) (off : nat) (new : list (bv 8))
    (av : aview) :
  cons_present_at j av -> cons_present_at j (delta_write i off new av).
Proof using .
  intros Hp. apply cons_of_node_pin.
  exact (node_pin_write_nonfile fname_console j cons_dev i off new av
           cons_dev_nonfile (node_pin_of_cons j av Hp)).
Qed.

(* ...and the five pinned rows ARE files, so they owe the inequality --
   which section 5 pays out of the length. *)
Lemma file_fs_pure_trunc_ne (i : Z) (av : aview) :
  i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
  i <> GREP_INO ->
  file_fs_pure av -> file_fs_pure (delta_trunc i av).
Proof using .
  intros N1 N2 N3 N4 N5 Hp.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_trunc_ne _ _ _ i av N1 (pinned_row_nondir _) H1).
  - exact (node_pin_trunc_ne _ _ _ i av N2 (pinned_row_nondir _) H2).
  - exact (node_pin_trunc_ne _ _ _ i av N3 (pinned_row_nondir _) H3).
  - exact (node_pin_trunc_ne _ _ _ i av N4 (pinned_row_nondir _) H4).
  - exact (node_pin_trunc_ne _ _ _ i av N5 (pinned_row_nondir _) H5).
Qed.

Lemma file_fs_pure_write_ne (i : Z) (off : nat) (new : list (bv 8))
    (av : aview) :
  i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
  i <> GREP_INO ->
  file_fs_pure av -> file_fs_pure (delta_write i off new av).
Proof using .
  intros N1 N2 N3 N4 N5 Hp.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  apply file_fs_pure_of_pins.
  - exact (node_pin_write_ne _ _ _ i off new av N1 (pinned_row_nondir _) H1).
  - exact (node_pin_write_ne _ _ _ i off new av N2 (pinned_row_nondir _) H2).
  - exact (node_pin_write_ne _ _ _ i off new av N3 (pinned_row_nondir _) H3).
  - exact (node_pin_write_ne _ _ _ i off new av N4 (pinned_row_nondir _) H4).
  - exact (node_pin_write_ne _ _ _ i off new av N5 (pinned_row_nondir _) H5).
Qed.

(* ====================================================================== *)
(*  5.  `f`'s INUM IS NONE OF THE PINNED ONES                              *)
(*                                                                        *)
(*  The truncate and the write at `f`'s own inum owe                       *)
(*  [file_fs_pure_trunc_ne] / [_write_ne] five inequalities, and nothing   *)
(*  in the view supplies them: what does is the LENGTH.  A typed content   *)
(*  is a chunk subset of an ADMISSIBLE line, hence shorter than            *)
(*  [line_max] = 100; every pinned binary is 35 KB and more; two rows with *)
(*  different contents are different rows.                                 *)
(* ====================================================================== *)

(* ---- 5a.  A SUBSET IS NO LONGER THAN THE WHOLE ----------------------- *)

Lemma sum_list_with_perm {A : Type} (g : A -> nat) (l k : list A) :
  l ≡ₚ k -> sum_list_with g l = sum_list_with g k.
Proof using . induction 1; cbn [sum_list_with]; lia. Qed.

Lemma sum_list_with_submseteq {A : Type} (g : A -> nat) (l k : list A) :
  l ⊆+ k -> (sum_list_with g l <= sum_list_with g k)%nat.
Proof using .
  intros Hsub. destruct (submseteq_Permutation l k Hsub) as [k' Hk].
  rewrite (sum_list_with_perm g k (l ++ k') Hk) sum_list_with_app. lia.
Qed.

Lemma StronglySorted_lt_NoDup (sel : list nat) :
  StronglySorted lt sel -> NoDup sel.
Proof using .
  induction 1 as [| a l Hs IH Hall]; [constructor |].
  constructor; [| exact IH]. intros Hin.
  rewrite ->Forall_forall in Hall. pose proof (Hall a Hin). lia.
Qed.

Lemma subseq_length_sum (cs : list (list (bv 8))) (sel : list nat) :
  length (subseq cs sel)
  = sum_list_with (fun j : nat => length (cs !!! j)) sel.
Proof using .
  rewrite /subseq. induction sel as [| j sel IH]; [reflexivity |].
  cbn [fmap list_fmap concat sum_list_with]. rewrite length_app IH. reflexivity.
Qed.

Lemma concat_length_sum (cs : list (list (bv 8))) :
  length (concat cs) = sum_list_with (fun c : list (bv 8) => length c) cs.
Proof using .
  induction cs as [| c cs IH]; [reflexivity |].
  cbn [concat sum_list_with]. rewrite length_app IH. reflexivity.
Qed.

Lemma sum_list_with_lookup_total (cs : list (list (bv 8))) (l : list nat) :
  sum_list_with (fun j : nat => length (cs !!! j)) l
  = sum_list_with (fun c : list (bv 8) => length c)
      ((fun j : nat => cs !!! j) <$> l).
Proof using .
  induction l as [| j l IH]; [reflexivity |].
  cbn [fmap list_fmap sum_list_with]. by rewrite IH.
Qed.

Lemma sum_seq_lookup_total (cs : list (list (bv 8))) :
  sum_list_with (fun j : nat => length (cs !!! j)) (seq 0 (length cs))
  = sum_list_with (fun c : list (bv 8) => length c) cs.
Proof using .
  rewrite (sum_list_with_lookup_total cs (seq 0 (length cs))).
  by rewrite fmap_lookup_total_seq.
Qed.

Lemma subseq_length_le (cs : list (list (bv 8))) (sel : list nat) :
  sel_ok cs sel -> (length (subseq cs sel) <= length (concat cs))%nat.
Proof using .
  intros [Hs Hr].
  assert (Hsub : sel ⊆+ seq 0 (length cs)).
  { apply NoDup_submseteq; [ exact (StronglySorted_lt_NoDup sel Hs) |].
    intros x Hx. apply elem_of_seq. rewrite ->Forall_forall in Hr.
    pose proof (Hr x Hx). lia. }
  rewrite subseq_length_sum concat_length_sum -sum_seq_lookup_total.
  exact (sum_list_with_submseteq (fun j : nat => length (cs !!! j))
           sel (seq 0 (length cs)) Hsub).
Qed.

(* ---- 5b.  A TYPED CONTENT IS SHORTER THAN A LINE --------------------- *)

Lemma wl_line_drop1_le (ws : list (list (bv 8))) :
  (length (wl_line (drop 1 ws)) <= length (wl_line ws))%nat.
Proof using .
  destruct ws as [| w r]; [reflexivity |].
  replace (drop 1 (w :: r)) with r by reflexivity.
  rewrite !wl_line_length.
  assert (Hb : (length (wl_body r) <= length (wl_body (w :: r)))%nat).
  { rewrite wl_body_cons length_app.
    destruct r as [| w0 r0]; cbn [wl_body wl_tail length]; lia. }
  lia.
Qed.

Lemma echo_chunks_concat (ws : list (list (bv 8))) :
  drop 1 ws <> [] -> concat (echo_chunks ws) = wl_line (drop 1 ws).
Proof using . rewrite /echo_chunks. apply echo_args_chunks_concat. Qed.

Lemma f_bytes_typed_short (ls : list wordline) (bs : list (bv 8)) :
  f_bytes_typed ls bs -> (length bs < EchoDisc.line_max)%nat.
Proof using .
  intros (ws & sel & _ & Hok & Hsel & ->).
  pose proof (subseq_length_le (echo_chunks ws) sel Hsel) as Hle.
  assert (Hne : drop 1 ws <> []).
  { pose proof (line_ok_ge2 ws Hok) as H2. intros Hnil.
    assert (Hz : length (drop 1 ws) = 0%nat) by (rewrite Hnil; reflexivity).
    rewrite length_drop in Hz. lia. }
  rewrite (echo_chunks_concat ws Hne) in Hle.
  pose proof (wl_line_drop1_le ws) as Hd.
  pose proof (line_ok_len ws Hok) as Hm. lia.
Qed.

(* ---- 5c.  ...SO ITS ROW IS NOT A PINNED BINARY'S --------------------- *)

Lemma init_bytes_length : Z.of_nat (length init_bytes) = 35976.
Proof using . exact ElfUser.init_elf_length. Qed.

Lemma sh_bytes_length : Z.of_nat (length sh_bytes) = 58312.
Proof using . exact ElfUser.sh_elf_length. Qed.

Lemma echo_bytes_length : Z.of_nat (length echo_bytes) = 35592.
Proof using . exact ElfUser.echo_elf_length. Qed.

Lemma cat_bytes_length : Z.of_nat (length cat_bytes) = 36728.
Proof using . exact ElfUser.cat_elf_length. Qed.

Lemma grep_bytes_length : Z.of_nat (length grep_bytes) = 44440.
Proof using . exact ElfUser.grep_elf_length. Qed.

(* THE ROW'S CONTENT LENGTH, WITHOUT [injection].  Two rows at one inum
   are one row, and what section 5c needs of them is the LENGTH -- but
   [injection] on [Some (MkAnode (AFile bs) 1) = Some (MkAnode (AFile
   init_bytes) 1)] NORMALISES the 35,976-byte literal and does not come
   back (durable-notes: a large literal is an opaque [Nat.of_num_uint] and
   every route through it materialises the list).  The reading below goes
   through a total projection instead, so the only conversion is a beta and
   an iota on the constructor. *)
Definition row_flen (o : option anode) : Z :=
  match o with
  | Some (MkAnode (AFile b) _) => Z.of_nat (length b)
  | _ => 0
  end.

Lemma row_flen_eq (av : aview) (i : Z) (bs bs' : list (bv 8)) (nl nl' : nat) :
  av !! i = Some (MkAnode (AFile bs) nl) ->
  av !! i = Some (MkAnode (AFile bs') nl') ->
  Z.of_nat (length bs) = Z.of_nat (length bs').
Proof using .
  intros H1 H2. transitivity (row_flen (av !! i)).
  - rewrite H1. reflexivity.
  - rewrite H2. reflexivity.
Qed.

(* THE SEPARATION.  Stated at the ROW rather than at [f_ok] so both the
   truncate (which knows `f`'s inum off the deed) and the write (which
   knows it off the descriptor) read the same sentence.  The comparison is
   at [Z]: a [nat] literal past Rocq's abstraction threshold is an opaque
   [Nat.of_num_uint] and [lia] cannot see through it (durable-notes). *)
Lemma f_inum_not_pinned (av : aview) (i : Z) (bs : list (bv 8)) :
  file_fs_pure av ->
  av !! i = Some (MkAnode (AFile bs) 1%nat) ->
  (length bs < EchoDisc.line_max)%nat ->
  i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO /\ i <> CAT_INO
  /\ i <> GREP_INO.
Proof using .
  intros Hp Hrow Hlen.
  destruct (file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
  destruct H1 as (_ & R1). destruct H2 as (_ & R2).
  destruct H3 as (_ & R3). destruct H4 as (_ & R4). destruct H5 as (_ & R5).
  rewrite /EchoDisc.line_max in Hlen.
  assert (HlenZ : Z.of_nat (length bs) < 100) by lia.
  split_and!; intros Heq; rewrite Heq in Hrow.
  - pose proof (row_flen_eq av INIT_INO bs init_bytes 1%nat 1%nat Hrow R1) as Hl.
    rewrite init_bytes_length in Hl. lia.
  - pose proof (row_flen_eq av SH_INO bs sh_bytes 1%nat 1%nat Hrow R2) as Hl.
    rewrite sh_bytes_length in Hl. lia.
  - pose proof (row_flen_eq av ECHO_INO bs echo_bytes 1%nat 1%nat Hrow R3) as Hl.
    rewrite echo_bytes_length in Hl. lia.
  - pose proof (row_flen_eq av CAT_INO bs cat_bytes 1%nat 1%nat Hrow R4) as Hl.
    rewrite cat_bytes_length in Hl. lia.
  - pose proof (row_flen_eq av GREP_INO bs grep_bytes 1%nat 1%nat Hrow R5) as Hl.
    rewrite grep_bytes_length in Hl. lia.
Qed.

(* ...and `f`'s row is not the console's either: one is a file, the other
   a device. *)
Lemma f_inum_ne_cons (av : aview) (i j : Z) (bs : list (bv 8)) :
  av !! i = Some (MkAnode (AFile bs) 1%nat) -> cons_present_at j av -> i <> j.
Proof using .
  intros Hrow (_ & Hc & _) Heq. rewrite Heq in Hrow. rewrite Hrow in Hc.
  rewrite /cons_dev in Hc. discriminate Hc.
Qed.

(* ---- 5d.  THE THREE COMPOSITE STEPS THE SUPPLIERS SPEND -------------- *)

(* THE CREATE AT `f`: the arm's child is an EMPTY FILE, so the pins and the
   console are untouched and `f` goes from ABSENT to [Some (i, [])] at the
   inum the arm chose. *)
Lemma file_create_at_f (av : aview) (ents : gmap fname Z) (nl : nat) (i : Z) :
  cre_pre av ROOTINO fname_f ents nl i (AFile []) ->
  file_fs_pure av ->
  file_fs_pure (delta_create ROOTINO fname_f i (AFile []) av)
  /\ (cons_absent av ->
      cons_absent (delta_create ROOTINO fname_f i (AFile []) av))
  /\ (forall j, cons_present_at j av ->
        cons_present_at j (delta_create ROOTINO fname_f i (AFile []) av))
  /\ f_ok (delta_create ROOTINO fname_f i (AFile []) av) (Some (i, [])).
Proof using .
  intros Hpre Hpure.
  assert (Hnd : forall e : gmap fname Z, AFile [] <> ADir e)
    by (intros e Hc; discriminate Hc).
  split_and!.
  - exact (file_fs_pure_create ROOTINO fname_f ents nl i (AFile []) av Hpre
             Hnd Hpure).
  - apply (cons_absent_create_nd ROOTINO fname_f ents nl i (AFile []) av
             Hpre Hnd). right. exact fname_f_ne_console.
  - intros j. exact (cons_present_create_nd j ROOTINO fname_f ents nl i
                       (AFile []) av Hpre Hnd).
  - exact (f_ok_create_f ents nl i av Hpre).
Qed.

(* THE TRUNCATE AT `f`, at the deed's own inum *)
Lemma file_trunc_at_f (av : aview) (i : Z) (bs : list (bv 8))
    (ls : list wordline) :
  file_fs_pure av ->
  f_ok av (Some (i, bs)) -> f_bytes_typed ls bs ->
  file_fs_pure (delta_trunc i av)
  /\ (cons_absent av -> cons_absent (delta_trunc i av))
  /\ (forall j, cons_present_at j av -> cons_present_at j (delta_trunc i av))
  /\ f_ok (delta_trunc i av) (Some (i, [])).
Proof using .
  intros Hpure Hok Hty. pose proof Hok as (Hst & Hrow).
  destruct (f_inum_not_pinned av i bs Hpure Hrow
              (f_bytes_typed_short ls bs Hty)) as (N1 & N2 & N3 & N4 & N5).
  split_and!.
  - exact (file_fs_pure_trunc_ne i av N1 N2 N3 N4 N5 Hpure).
  - exact (cons_absent_trunc_any i av).
  - intros j. exact (cons_present_trunc_any j i av).
  - exact (f_ok_trunc_f i bs av Hok).
Qed.

(* THE WRITE AT `f`, at the deed's own inum *)
Lemma file_write_at_f (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (ls : list wordline) :
  file_fs_pure av ->
  f_ok av (Some (i, bs0)) -> f_bytes_typed ls bs0 ->
  file_fs_pure (delta_write i off new av)
  /\ (cons_absent av -> cons_absent (delta_write i off new av))
  /\ (forall j, cons_present_at j av ->
                cons_present_at j (delta_write i off new av))
  /\ f_ok (delta_write i off new av) (Some (i, blk_splice off new bs0)).
Proof using .
  intros Hpure Hok Hty. pose proof Hok as (Hst & Hrow).
  destruct (f_inum_not_pinned av i bs0 Hpure Hrow
              (f_bytes_typed_short ls bs0 Hty)) as (N1 & N2 & N3 & N4 & N5).
  split_and!.
  - exact (file_fs_pure_write_ne i off new av N1 N2 N3 N4 N5 Hpure).
  - exact (cons_absent_write_any i off new av).
  - intros j. exact (cons_present_write_any j i off new av).
  - exact (f_ok_write_f i off new bs0 av Hok).
Qed.

(* ...and the deed's inum is not the CONSOLE's either, which is what a
   move at `f` owes [AppEcho.cons_state]'s two present arms when they are
   read at a row rather than at a name. *)
Lemma f_deed_inum_ne_cons (av : aview) (i j : Z) (bs : list (bv 8)) :
  f_ok av (Some (i, bs)) -> cons_present_at j av -> i <> j.
Proof using .
  intros (_ & Hrow) Hc. exact (f_inum_ne_cons av i j bs Hrow Hc).
Qed.
