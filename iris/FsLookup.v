(* ======================================================================= *)
(*  FsLookup.v -- F2: ONE dirlookup, READ AT THE TREE.                      *)
(*  design: claude-notes/design/fs-fragments.md, ruling R8 (§5.4)           *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS.

    This is the FRAGMENT CAMPAIGN's F2 increment: the tree-level reading of
    a SINGLE [dirlookup] under a SINGLE directory lock, lifted CALLER-SIDE
    out of the landed byte-level contract [SpecDirlookup.wp_dirlookup_sconf].
    Nothing landed moves -- the byte-stability discipline (R10, §20.18
    ruling 1) forbids it, and nothing here needs it to.

    ---- WHAT IT IS *NOT*, AND WHY (R8) ----------------------------------

    It is NOT a re-derivation of namex's postcondition.  [SpecNamex.v]:113-124
    rules that there is NO path -> inode functional statement: each
    [dirlookup] is atomic under its OWN directory's lock, and no stable
    global tree exists between two iterations of the walk.  [FsRep.v]'s
    §1.4 says the same thing from the resource side -- [fnode i n] requires
    [InodeRegion.dinode_at], which lives behind [i]'s lock, so [fs_rep t]
    over a whole tree is unholdable by any thread.  F2 is therefore a
    statement about ONE call, and the walk is a SEQUENCE of them with
    nothing joining the links.

    ---- WHAT "LOGICALLY ATOMIC" MEANS HERE, EXACTLY ---------------------

    The house atomic-update idiom ([SpecLogWrite.wp_log_write_au],
    [InodeRegion.ireg_write_au]) surrenders the caller's fragment through a
    fupd fired at ONE ghost step inside the callee, so the fragment need
    never sit in the caller's hands across the call.  **That form is
    UNAVAILABLE for the directory's own node here, and the reason is a
    theorem, not an oversight**:

      dirlookup READS THE DIRECTORY'S BYTES FOR THE WHOLE CALL.  Its
      [readi] loop consumes [InodeInv.inode_blocks γfs bm data] from entry
      to return, and the call SLEEPS.  A mask-changing fupd cannot be held
      open across a [WP Loop] step, so the bytes half cannot arrive at one
      point and leave at another; it must be in hand throughout.  And the
      record half cannot travel either: the caller ALREADY holds
      [dinode_at] (it is inside [IcacheEscrow.ic_loaded], which ilock hands
      out), so a second copy arriving through a client invariant would meet
      [InodeRegion.dinode_at_excl] and prove [False].

    So the directory's node fragment is pinned in the caller's hands for
    the whole call -- **by the lock, which is exactly what makes the call
    atomic in the first place**.  The linearization point is not a ghost
    step to be chosen; it is the entire locked interval, during which the
    node cannot move.  The formal content of R8's "logically atomic" is
    therefore:

      (LP1) the triple's PRE and POST name the SAME [ents] -- the node
            cannot change under the caller, so the answer read out of the
            bytes IS the answer at the linearization point; and
      (LP2) the triple claims NOTHING about any other node.  A client that
            wants to place the answer in a GLOBAL tree does so by opening
            its own AMBIENT-tree resource at one instant -- [dl_au] /
            [dl_au_fire] in §5 -- and that instant is the only one at which
            a global tree may be spoken of at all.

    R3 is respected throughout: no new authority, no new ghost name, no new
    invariant.  [dl_au] is a SHAPE a client may choose, not a resource this
    file allocates.

    ---- WHAT THE LIFTING PAYS FOR ---------------------------------------

    The tree form DISCHARGES one of dirlookup's landed premises rather than
    adding one: [di_type dn = T_DIR] (the premise that refutes
    panic("dirlookup not DIR") at +0x1c) falls straight out of
    [FsTree.node_rep]'s NDir case ([node_rep_T_DIR] below).  Everything
    else it takes is byte-level well-formedness that the tree layer
    deliberately does not carry ([InodeLock.inode_ok], [DirView.dir_ok])
    and that a caller already holds beside the fragment in
    [IcacheEscrow.ic_loaded].

    §2's record deltas are the twin of [FsTree.dir_view_zero]: that lemma
    is the tree delta of an UNLINK and landed with F1a; [dir_view_write] is
    the tree delta of a DIRLINK, and together they are what F3's friendly
    triples read their "lookup after insert" / "lookup after delete"
    obligations off.

    §6 joins the two halves of §20.17.4's owed [".."] fact.                 *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import ProcAvail.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FsStateLink.    (* [fsLinkG] -- capacity class, must be IMPORTed *)
Require Import FsStateInode.
Require Import FsStateEra.
Require Import FsBytesGamma.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import FsTree.
Require Import FsRep.
Require Import DirLinks.
Require Import SpecDirlookup.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE PURE READING: dirlookup's ANSWER *IS* THE NODE'S MAP           *)
(* ====================================================================== *)

(* the record count a directory's record [dn] fixes -- spelled once so the
   statements below do not repeat the projection.  Transparent: every proof
   that has to REWRITE at this count unfolds it first, because [node_rep]
   states the count in the projected form. *)
Definition dnrec (dn : dinode) : nat := dir_nrec (bv_unsigned (di_size dn)).

(* **THE WHOLE OF F2's PURE CONTENT, IN ONE EQUATION.**  Under
   [node_rep (NDir ents) dn data] -- i.e. for a directory node whose
   abstract map [ents] is the reading of the bytes [data] -- the map's
   answer at every name IS the first-match search dirlookup performs.
   [FsTree.dir_view_lookup] is the abstraction theorem; this is it read at
   a NODE rather than at a byte view, and every arm below is a corollary. *)
Lemma node_lookup_first (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) :
  node_rep (NDir ents) dn data ->
  ents !! s
  = (fun k => bv_unsigned (dir_inum data k)) <$> dir_first data (dnrec dn) s.
Proof. intros (_ & _ & ->). apply dir_view_lookup. Qed.

(* THE FOUND ARM, at the tree.  dirlookup stopped at record [k]; the node
   maps the name to that record's inum. *)
Lemma node_lookup_found (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) (k : nat) :
  node_rep (NDir ents) dn data ->
  dir_first data (dnrec dn) s = Some k ->
  ents !! s = Some (bv_unsigned (dir_inum data k)).
Proof.
  intros Hrep Hf. rewrite (node_lookup_first ents dn data s Hrep).
  rewrite Hf. reflexivity.
Qed.

(* THE MISS ARM, at the tree.  dirlookup scanned the whole directory and
   found nothing; the name is not in the node's map. *)
Lemma node_lookup_none (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) :
  node_rep (NDir ents) dn data ->
  dir_first data (dnrec dn) s = None ->
  ents !! s = None.
Proof.
  intros Hrep Hf. rewrite (node_lookup_first ents dn data s Hrep).
  rewrite Hf. reflexivity.
Qed.

(* ...and both converses, which is what makes the reading an EQUIVALENCE
   rather than a one-way implication: a caller that knows the tree can
   predict the scan.  (Bytes -> tree is still the only DEFINITIONAL
   direction -- see [FsTree.v]'s header; these are theorems about a node
   that already has a representation.) *)
Lemma node_lookup_none_inv (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) :
  node_rep (NDir ents) dn data ->
  ents !! s = None ->
  dir_first data (dnrec dn) s = None.
Proof.
  intros Hrep H. rewrite (node_lookup_first ents dn data s Hrep) in H.
  destruct (dir_first data (dnrec dn) s) as [k |];
    cbn [fmap option_fmap option_map] in H; [discriminate | reflexivity].
Qed.

Lemma node_lookup_some_inv (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) (s : fname) (z : Z) :
  node_rep (NDir ents) dn data ->
  ents !! s = Some z ->
  exists k : nat,
    dir_first data (dnrec dn) s = Some k
    /\ (k < dnrec dn)%nat /\ dir_live data k /\ dir_bname data k = s
    /\ bv_unsigned (dir_inum data k) = z.
Proof.
  intros Hrep H. rewrite (node_lookup_first ents dn data s Hrep) in H.
  destruct (dir_first data (dnrec dn) s) as [k |] eqn:Hf;
    cbn [fmap option_fmap option_map] in H; [| discriminate].
  exists k.
  split; [reflexivity |].
  split; [exact (dir_first_lt _ _ _ _ Hf) |].
  split; [exact (dir_first_live _ _ _ _ Hf) |].
  split; [exact (dir_first_name _ _ _ _ Hf) | congruence].
Qed.

(* THE PREMISE THE TREE FORM DISCHARGES RATHER THAN ADDS.  dirlookup's
   [di_type dn = T_DIR] refutes panic("dirlookup not DIR") at +0x1c; a
   directory NODE has it by construction ([FsTree.node_rep_dir]). *)
Lemma node_rep_T_DIR (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep (NDir ents) dn data -> di_type dn = T_DIR.
Proof.
  intros Hrep. apply bv_eq. rewrite (node_rep_dir ents dn data Hrep).
  vm_compute. reflexivity.
Qed.

(* ====================================================================== *)
(*  2.  THE RECORD DELTAS THE FRIENDLY LAYER READS ITS TREE DELTAS OFF     *)
(* ====================================================================== *)

(* **MOVED DOWN TO [FsTree.v]** (the [dir_uniq] increment, fs-fragments
   S2-0).  [dir_written_at] and [dir_names_unique_write] are stated in
   [FsTree]/[DirView] vocabulary alone, and the payload clause [dir_uniq]
   -- which rides in [IcacheEscrow]'s two payloads, far below this file --
   is what needs them.  They are still in scope here, unqualified, through
   this file's own [Require Import FsTree]; nothing else moved. *)

(* **THE TREE DELTA OF A DIRLINK**, and the twin of [FsTree.dir_view_zero].
   Writing name [s] at inum [z] into a FREE slot inserts exactly that one
   binding and moves nothing else.  Like its twin it is FALSE without the
   uniqueness invariant on the way in -- a duplicate hiding behind the
   written slot would make the "moves nothing else" half wrong. *)
Lemma dir_view_write (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) :
  dir_names_unique data nrec ->
  (nrec <= nrec')%nat -> (k0 < nrec')%nat ->
  (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r) ->
  ((k0 < nrec)%nat -> ~ dir_live data k0) ->
  z <> bv_0 16 ->
  dir_first data nrec s = None ->
  dir_written_at data data' k0 s z ->
  dir_view data' nrec' = <[s := bv_unsigned z]> (dir_view data nrec).
Proof.
  intros Hu Hle Hk0 Hdead Hfree Hz Hnone Hw.
  pose proof (dir_names_unique_write data data' nrec nrec' k0 s z
                Hu Hle Hk0 Hdead Hnone Hw) as Hu'.
  pose proof (dir_written_live0 data data' k0 s z Hw Hz) as Hl0.
  apply map_eq. intros x.
  destruct (decide (x = s)) as [-> | Hne].
  - rewrite lookup_insert.
    pose proof (dir_view_live data' nrec' k0 Hu' Hk0 Hl0) as H.
    rewrite (proj1 (proj2 Hw)) in H. rewrite H.
    rewrite (proj1 Hw). reflexivity.
  - assert (Hsx : s <> x) by congruence.
    (* [rewrite lem by tac] is rejected under the proofmode's ssreflect
       [rewrite] (BvShift.v's note); the side condition goes to [//]. *)
    rewrite lookup_insert_ne //.
    destruct (dir_view data nrec !! x) as [w |] eqn:Hx.
    + (* an OLD binding: its record survives, unmoved *)
      destruct (dir_view_lookup_rec data nrec x w Hx)
        as (q & Hq & Hlq & Hnq & Hwq).
      assert (Hqk0 : q <> k0) by (intros ->; exact (Hfree Hq Hlq)).
      assert (Hlq' : dir_live data' q)
        by exact (proj2 (dir_written_live data data' k0 s z q Hw Hqk0) Hlq).
      assert (Hqlt : (q < nrec')%nat) by lia.
      pose proof (dir_view_live data' nrec' q Hu' Hqlt Hlq') as H.
      assert (Hbq : dir_bname data' q = x).
      { rewrite (dir_written_bname data data' k0 s z q Hw Hqk0). exact Hnq. }
      rewrite Hbq in H. rewrite H.
      rewrite (dir_written_inum data data' k0 s z q Hw Hqk0).
      rewrite Hwq. reflexivity.
    + (* an ABSENT name stays absent *)
      apply dir_view_lookup_None_match. intros q Hq [Hlq' Hnq'].
      destruct (decide (q = k0)) as [-> | Hqk0].
      * apply Hne. rewrite <- Hnq'. exact (proj1 (proj2 Hw)).
      * destruct (dir_written_class data data' nrec nrec' k0 s z q Hw Hdead
                    Hq Hlq' Hqk0) as [Hqlt Hlq].
        pose proof (dir_view_live data nrec q Hu Hqlt Hlq) as H.
        assert (Hbq : dir_bname data q = x).
        { rewrite <- (dir_written_bname data data' k0 s z q Hw Hqk0).
          exact Hnq'. }
        rewrite Hbq in H. rewrite H in Hx. discriminate.
Qed.

(* ---- the same two, lifted to a NODE ---------------------------------- *)

(* **LOOKUP AFTER INSERT.**  After the write the node's map is the old one
   with [s] bound to [z] -- so the very next dirlookup of [s] finds it
   ([dir_first_after_write] below).  The size premise is a bound on the two
   record counts, which is what both of dirlink's arms deliver: the append
   arm grows [di_size] by 16, the reuse arm leaves it alone. *)
Lemma node_rep_insert (ents : gmap fname Z) (dn dn' : dinode)
    (data data' : nat -> list (bv 8)) (k0 : nat) (s : fname) (z : bv 16) :
  node_rep (NDir ents) dn data ->
  bv_unsigned (di_type dn') = T_DIR_z ->
  (dnrec dn <= dnrec dn')%nat ->
  (k0 < dnrec dn')%nat ->
  (forall r : nat, (dnrec dn <= r < dnrec dn')%nat -> r <> k0 ->
     ~ dir_live data' r) ->
  ((k0 < dnrec dn)%nat -> ~ dir_live data k0) ->
  z <> bv_0 16 ->
  dir_first data (dnrec dn) s = None ->
  dir_written_at data data' k0 s z ->
  node_rep (NDir (<[s := bv_unsigned z]> ents)) dn' data'.
Proof.
  unfold dnrec. intros Hrep Hty Hle Hk0 Hdead Hfree Hz Hnone Hw.
  destruct Hrep as (_ & Hu & ->).
  split; [exact Hty |].
  split.
  - exact (dir_names_unique_write data data' _ _ k0 s z
             Hu Hle Hk0 Hdead Hnone Hw).
  - symmetry.
    exact (dir_view_write data data' _ _ k0 s z
             Hu Hle Hk0 Hdead Hfree Hz Hnone Hw).
Qed.

(* **LOOKUP AFTER DELETE -- THE UNMASKING LEMMA MADE OPERATIONAL.**  After
   sys_unlink's memset+writei the node's map is the old one with the
   record's name DELETED, so the next dirlookup of that name MISSES
   ([dir_first_after_zero] below).  It is FALSE without
   [dir_names_unique], which rides inside [node_rep]'s NDir case: a hidden
   duplicate behind the zeroed record would be UNMASKED and the name would
   still be mapped, to a DIFFERENT inum (R2's unmasking argument). *)
Lemma node_rep_delete (ents : gmap fname Z) (dn dn' : dinode)
    (data data' : nat -> list (bv 8)) (k0 : nat) :
  node_rep (NDir ents) dn data ->
  bv_unsigned (di_type dn') = T_DIR_z ->
  dnrec dn' = dnrec dn ->
  (k0 < dnrec dn)%nat ->
  dir_live data k0 ->
  dir_zeroed_at data data' k0 ->
  node_rep (NDir (delete (dir_bname data k0) ents)) dn' data'.
Proof.
  unfold dnrec. intros Hrep Hty Hsz Hk0 Hl0 Hzer.
  destruct Hrep as (_ & Hu & ->).
  split; [exact Hty |]. rewrite Hsz.
  split.
  - exact (dir_names_unique_zero data data' _ k0 Hzer Hu).
  - symmetry. exact (dir_view_zero data data' _ k0 Hu Hk0 Hl0 Hzer).
Qed.

(* ---- ...and the two OPERATIONAL statements: what the NEXT scan does --- *)

(* THE NEXT dirlookup FINDS THE WRITTEN RECORD, at the slot dirlink used.
   Not merely "some record": uniqueness pins it to [k0], which is what a
   caller that wants to name the offset needs. *)
Lemma dir_first_after_write (data data' : nat -> list (bv 8))
    (nrec nrec' k0 : nat) (s : fname) (z : bv 16) :
  dir_names_unique data nrec ->
  (nrec <= nrec')%nat -> (k0 < nrec')%nat ->
  (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r) ->
  z <> bv_0 16 ->
  dir_first data nrec s = None ->
  dir_written_at data data' k0 s z ->
  dir_first data' nrec' s = Some k0.
Proof.
  intros Hu Hle Hk0 Hdead Hz Hnone Hw.
  pose proof (dir_names_unique_write data data' nrec nrec' k0 s z
                Hu Hle Hk0 Hdead Hnone Hw) as Hu'.
  pose proof (dir_written_live0 data data' k0 s z Hw Hz) as Hl0.
  apply dir_first_Some. split; [exact Hk0 | split].
  - split; [exact Hl0 | exact (proj1 (proj2 Hw))].
  - intros q Hq [Hlq Hnq].
    assert (Hqlt : (q < nrec')%nat) by lia.
    assert (Hqk : q = k0).
    { apply (Hu' q k0 Hqlt Hk0 Hlq Hl0).
      unfold dir_bname. rewrite Hnq. symmetry. exact (proj1 (proj2 Hw)). }
    lia.
Qed.

(* THE NEXT dirlookup MISSES the zeroed record's name -- the unmasking
   lemma, said the way a caller uses it. *)
Lemma dir_first_after_zero (data data' : nat -> list (bv 8))
    (nrec k0 : nat) :
  dir_names_unique data nrec ->
  (k0 < nrec)%nat -> dir_live data k0 ->
  dir_zeroed_at data data' k0 ->
  dir_first data' nrec (dir_bname data k0) = None.
Proof.
  intros Hu Hk0 Hl0 Hzer.
  apply dir_view_lookup_None.
  rewrite (dir_view_zero data data' nrec k0 Hu Hk0 Hl0 Hzer).
  apply lookup_delete.
Qed.

(* ====================================================================== *)
(*  3.  THE DIRECTORY FRAGMENT, IN THE FORM THE CALL TAKES IT              *)
(* ====================================================================== *)

Section FsLookup.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{ICFG : icfg}.

  (* [FsRep.fnode] AT A NAMED RECORD AND NAMED BYTES.  [fnode] hides
     [dn]/[bm]/[data] existentially, which is right for a tree statement
     and WRONG at a call boundary: dirlookup's byte-level bundle
     ([inode_meta ip dn], [inode_map γfs ip bm]) names them, and nothing
     would tie the two together if the fragment did not.  So the contract
     takes the fragment SPREAD -- "the caller holds [fnode dp (NDir ents)]
     or its components" -- and [fdir_fnode] repacks it the moment the
     caller wants the tree statement back. *)
  Definition fdir (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (dinode_at γi (inum_of i) dn ∗ inode_blocks γfs bm data ∗
     ⌜node_rep (NDir ents) dn data⌝)%I.

  Lemma fdir_intro (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    node_rep (NDir ents) dn data ->
    dinode_at γi (inum_of i) dn -∗ inode_blocks γfs bm data -∗
    fdir γi γfs i ents dn bm data.
  Proof.
    intros Hrep. iIntros "Hd Hb". rewrite /fdir.
    iSplitL "Hd"; [iExact "Hd" |].
    iSplitL "Hb"; [iExact "Hb" |].
    iPureIntro. exact Hrep.
  Qed.

  Lemma fdir_fnode (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    fdir γi γfs i ents dn bm data -∗ fnode γi γfs i (NDir ents).
  Proof.
    iIntros "(Hd & Hb & %Hrep)".
    iApply (fnode_intro γi γfs i (NDir ents) dn bm data Hrep with "Hd Hb").
  Qed.

  Lemma fnode_fdir (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) :
    fnode γi γfs i (NDir ents) -∗
      ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
        fdir γi γfs i ents dn bm data.
  Proof.
    iIntros "H". iDestruct "H" as (dn bm data) "(Hd & Hb & %Hrep)".
    iExists dn, bm, data.
    iApply (fdir_intro γi γfs i ents dn bm data Hrep with "Hd Hb").
  Qed.

  (* the record's type, read straight off the fragment -- what a caller
     hands dirlookup's dead panic *)
  Lemma fdir_T_DIR (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    fdir γi γfs i ents dn bm data -∗ ⌜di_type dn = T_DIR⌝.
  Proof.
    iIntros "(_ & _ & %Hrep)". iPureIntro.
    exact (node_rep_T_DIR ents dn data Hrep).
  Qed.

End FsLookup.

(* ====================================================================== *)
(*  4.  THE TRIPLE                                                         *)
(* ====================================================================== *)

(* [SpecDirlookup.wp_dirlookup_sconf_body], READ AT THE TREE.  Three
   differences and no others:

     - the [di_type dn = T_DIR] premise is GONE -- [node_rep]'s NDir case
       supplies it ([node_rep_T_DIR]);
     - [inode_blocks γfs bm data] in the pre and the post is replaced by
       the directory's node fragment [fdir γi γfs dpi ents dn bm data],
       which CONTAINS it.  The [dinode_at] half rides through untouched:
       dirlookup never names the region;
     - each arm carries the tree-level answer beside the byte-level one;
     - **and, since the iget-licence increment, the BORROW** -- see the
       block below, which is a FINDING and not just a change.

   ---- ROW 14's FINDING: F2's PREMISE SET GREW BEYOND THE DISJUNCTION ----

   The licence increment (fs-fragments.md §7.1) gave [SpecDirlookup] one
   pure DISJUNCTIVE premise (§7.5.6) plus a borrowed ticket list and the
   home's own record.  The worklist sanctioned relaying THE DISJUNCTION to
   this triple and said to STOP AND REPORT if more was needed, because
   "F2 has fewer premises than the bytes" is the property F2 exists for.

   MORE IS NEEDED, and here is the exact list, so the coordinator can rule:

     (i)   the §7.5.6 disjunction                      -- SANCTIONED;
     (ii)  ⌜dir_orphan_clean dn data⌝                  -- NOT sanctioned.
           It is what closes the RIGHT disjunct, and [FsTree.node_rep]'s
           NDir case cannot supply it: [node_rep] fixes the type, name
           uniqueness and [ents = dir_view …] and says NOTHING about
           [di_nlink].  There is no tree-level fact that implies it.
     (iii) ⌜0 <= dpi < 2 ^ 32⌝                         -- NOT sanctioned.
           The byte contract keys the ticket list at [bv_unsigned dinum]
           and the tree keys it at [dpi : Z]; [FsRep.inum_of_unsigned] is
           the round trip and this is its premise.  It IS the tree's own
           [FsTree.fs_inums_ok] at one node, so every client has it.
     (iv)  [FsRep.fedges dpi dn data]                  -- NOT sanctioned,
           and it is the substantive one: a RESOURCE, the directory's
           out-edges.  §1.3 makes edges a primitive client-held fragment
           beside the node, so a client of this triple does hold it -- but
           [fdir] does not contain it, and that is the shape question the
           coordinator should rule on (folding the edges into [fdir] would
           restore the property outright).

   WHAT SURVIVES: F2 still has STRICTLY FEWER premises than the byte-level
   contract it wraps -- the bytes gained three pure premises and two
   resources, this gained three pure and one resource, and [dinode_at] is
   still hidden inside [fdir].  So the property F2 exists for is dented,
   not lost.  The row was executed rather than left red because the whole
   increment's gate is a green cone; the finding is recorded here, in the
   ledger entry, and in the worklist.

   Everything else -- readi's threading, [dir_inums_ok], the running-thread
   bundle, the icache, the parking premise, the [iref_slot] ledger -- is
   the landed contract verbatim, because the tree layer deliberately does
   not carry byte-level well-formedness ([InodeLock.inode_ok],
   [DirView.dir_ok]) and a caller holds all of it beside the fragment in
   [IcacheEscrow.ic_loaded].

   [dpi] IS THE DIRECTORY'S INUM, [ip] its in-core entry pointer.  They are
   independent parameters and neither constrains the other: what ties the
   fragment to THIS directory is that [dn] and [data] are shared between
   [fdir] and the byte-level bundle. *)
Definition wp_dirlookup_tree_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn : dinode)
    (dpi : Z) (ents : gmap fname Z)                   (* THE TREE-LEVEL NODE *)

    (fn : nat -> bv 8)                                (* the caller's name   *)
    (hasp : bool) (pofv : mword 32)                   (* poff, two-armed     *)
    (pidv : mword 32) (dq dqd dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.dirlookup in
  let pj := proc_addr j in
  let nb := (m !!! Regidx (mword_of_int 11 : mword 5) : mword 64) in
  let pf := (m !!! Regidx (mword_of_int 12 : mword 5) : mword 64) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  let s := bname 14 fn in
  (K_dirlookup <= K)%nat ->
  (* (1) IS GONE -- see the header.  panic("dirlookup read") at +0x46 is
     still a LIVE arm, discharged inside the landed proof. *)
  (* (2) readi's own threading, verbatim *)
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  bm_covers bm (bv_unsigned (di_size dn)) ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (* (2') the payload's hole clause, owed to licence (a)'s borrow
     (durable-disk 2b-inode-5, step 3) *)
  blk_holes_zero bm data ->
  (* (3) iget's argument bound, over the records *)
  dir_inums_ok data nrec nib ->
  (* (4) THE LICENCE PREMISES -- see the FINDING in the header *)
  (bv_unsigned (di_nlink dn) <> 0
   \/ (s <> dot_name /\ s <> dotdot_name)) ->
  dir_orphan_clean dn data ->
  0 <= dpi < 2 ^ 32 ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (m !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = ip ->
  eq_vec (m !!! Regidx (mword_of_int 12 : mword 5)) zero_reg = negb hasp ->
  eb = true ->
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY: the cells, and THE NODE FRAGMENT ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  fdir γi γfs dpi ents dn bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's [f]) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
  (* ---- poff: a 4-byte cell, or nothing ---- *)
  (if hasp then pf ↦₄[KT1] pofv else emp) -∗
  (* ---- the caller's own pid cell ---- *)
  proc_priv_bare pj pidv Vpr -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) γd pd pav pu) -∗
  bslot -∗
  (* ---- THE ICACHE, exactly as iget takes it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  (* the inode region: iget's premise since iclaim-ledger.md §3.3, relayed
     verbatim.  The tree layer neither reads nor names a dinode through it
     -- the hit arm's iget opens it ghost-only, on the ledger columns. *)
  ireg_inv γi γfs inodestart nib -∗
  iref_slot -∗
  (* the directory's OUT-EDGES, borrowed for the licence and returned
     verbatim on both arms (§1.3 makes them a client-held fragment) --
     and beside them the ENTRY UNITS the licence is now spelt with
     (durable-disk 2b-inode-5, step 3).  The tree layer has no fnode
     conjunct for them, so they ride as their own premise; nothing in the
     tree builds an [fdir] anyway (FsTree.v's §"the demonstration
     layer"). *)
  fedges dpi dn data -∗
  FsStateInode.ent_toks (FsBytesGamma.fs_gamma_L γfs) dpi
    (FsStateEra.era_node dn bm data) -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool) (k : nat) (kslot : nat) (q : Qp),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* THE DIRECTORY COMES BACK UNTOUCHED, NODE FRAGMENT INCLUDED --
         [ents] is the SAME map it went in at.  That is (LP1): the lock
         froze the node for the whole call, so the answer below is the
         answer at the linearization point. *)
      i_dev ip ↦₄{dqd} dev -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      fdir γi γfs dpi ents dn bm data -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
      proc_priv_bare pj pidv Vpr -∗
      bslot -∗
      fedges dpi dn data -∗
      FsStateInode.ent_toks (FsBytesGamma.fs_gamma_L γfs) dpi
        (FsStateEra.era_node dn bm data) -∗
      (* THE TWO ARMS, EACH AT BOTH ALTITUDES.  The record index [k]
         survives because a caller needs it: sys_unlink names the offset
         [16k] with it, and iget's reference is at that record's inum. *)
      (if found
       then ⌜ents !! s = Some (bv_unsigned (dir_inum data k))⌝ ∗
            ⌜dir_first data nrec s = Some k
             /\ (kslot < NINODE)%nat
             /\ (mf !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = ientry kslot⌝ ∗
            inode_ref kslot q dev
              (zero_extend' 32 (dir_inum data k : mword 16) : mword 32) ∗
            (* the minted provenance unit (item 7a-wire) *)
            runit_any
              (bv_unsigned
                 (zero_extend' 32 (dir_inum data k : mword 16) : mword 32)) ∗
            (if hasp
             then pf ↦₄[KT1] (mword_of_int (Z.of_nat (16 * k)) : mword 32)
             else emp)
       else ⌜ents !! s = None⌝ ∗
            ⌜dir_first data nrec s = None
             /\ mf !!! Regidx (mword_of_int 10 : mword 5)
                = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slot ∗
            (if hasp then pf ↦₄[KT1] pofv else emp)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE LIFTING.  A functor over the LANDED contract, not a new interface:
   SpecDirlookup does not move (R10, §20.18 ruling 1), and this file's whole
   claim is that the tree reading is available CALLER-SIDE. *)
Module FsLookupTree (DL : DIRLOOKUP).

  Lemma wp_dirlookup_tree
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (dpi : Z) (ents : gmap fname Z)
      (fn : nat -> bv 8)
      (hasp : bool) (pofv : mword 32)
      (pidv : mword 32) (dq dqd dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate) :
      wp_dirlookup_tree_body γs j γl γu γd γk pd pav pu bn γfs γi cn gtl
                             γa γf cov logstart inodestart nib dev ip bm data dn
                             dpi ents fn hasp pofv pidv dq dqd dqn
                             m K eb b lks Vpr.
  Proof.
    unfold wp_dirlookup_tree_body. cbv zeta.
    intros HK Hlg Hbwf Hbcov Hszb Hholes Hdio Hdisj Horph Hdpi Hj Hgs Ha0 Ha2
           Heb Hlkb.
    iIntros "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hkenv Hidev Hmeta Hmap Hfdir
             Hname Hpoff Hppid Hprocs Hdev Hdgeom Hdlk Hbslot
             Hitb2 Hitbl Hesc Hireg Hisl Hedges Hetk Hcont".
    iDestruct "Hfdir" as "(Hdiat & Hblocks & %Hrep)".
    (* licence (c)'s only demand on the record: an allocated one.  The
       tree layer has it by construction -- a directory node's type is
       [T_DIR_z] ([FsTree.node_rep_dir]). *)
    assert (Htynz : bv_unsigned (di_type dn) <> 0)
      by (rewrite (node_rep_dir ents dn data Hrep); unfold T_DIR_z; lia).
    (* the ticket list, re-keyed from the tree's [Z] to the region's word *)
    iAssert (dir_links (bv_unsigned (inum_of dpi)) dn data)
      with "[Hedges]" as "Hedges".
    { rewrite /fedges (inum_of_unsigned dpi Hdpi). iExact "Hedges". }
    pose proof (inum_of_unsigned dpi Hdpi) as Hkeq.
    iAssert (FsStateInode.ent_toks (FsBytesGamma.fs_gamma_L γfs)
               (bv_unsigned (inum_of dpi)) (FsStateEra.era_node dn bm data))
      with "[Hetk]" as "Hetk".
    { rewrite Hkeq. iExact "Hetk". }
    iDestruct (dlinks_intro with "Hedges Hetk") as "Hedges".
    iApply (DL.wp_dirlookup_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn gtl
              γa γf cov logstart inodestart nib dev ip (inum_of dpi) bm data dn dn
              fn hasp pofv
              pidv dq dqd dqn m K eb b lks Vpr
              HK (node_rep_T_DIR ents dn data Hrep) Hlg Hbwf Hbcov Hszb Hholes
              Hdio Hdisj Horph Htynz eq_refl Hj Hgs Ha0 Ha2 Hlkb
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hkenv
                    Hidev Hmeta Hmap Hblocks Hname Hpoff
                    Hppid Hprocs Hdev Hdgeom Hdlk Hbslot
                    Hitb2 Hitbl Hesc Hireg Hisl Hedges Hdiat").
    (* dirlookup is eb-generic now; this layer is still at [eb = true],
       where the complement is [emp]. *)
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDd Hgd mf found k kslot q)
      "%Hcs Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks Hname Hppid Hbslot
       Hedges Hdiat Harm".
    iDestruct (dlinks_open with "Hedges") as "[Hedges Hetk]".
    iEval (rewrite Hkeq) in "Hetk".
    iAssert (fedges dpi dn data) with "[Hedges]" as "Hedges".
    { rewrite /fedges (inum_of_unsigned dpi Hdpi). iExact "Hedges". }
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDd Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf found k kslot q
              with "[] Hcg Hcnt Hpc Hidev Hmeta Hmap
                    [Hdiat Hblocks] Hname Hppid Hbslot Hedges Hetk [Harm]").
    - iPureIntro. exact Hcs.
    - iApply (fdir_intro γi γfs dpi ents dn bm data Hrep with "Hdiat Hblocks").
    - destruct found.
      + iDestruct "Harm" as "(%Hpure & Href & Hru & Hpf)".
        iSplitR.
        { iPureIntro.
          exact (node_lookup_found ents dn data (bname 14 fn) k Hrep
                   (proj1 Hpure)). }
        iSplitR; [iPureIntro; exact Hpure |]. iFrame.
      + iDestruct "Harm" as "(%Hpure & Hslot & Hpf)".
        iSplitR.
        { iPureIntro.
          exact (node_lookup_none ents dn data (bname 14 fn) Hrep
                   (proj1 Hpure)). }
        iSplitR; [iPureIntro; exact Hpure |]. iFrame.
  Qed.

End FsLookupTree.

(* ====================================================================== *)
(*  5.  THE AMBIENT TREE, SPOKEN OF AT ONE INSTANT                         *)
(* ====================================================================== *)

Section FsLookupAu.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{ICFG : icfg}.

  (* the tree the caller's locked node completes.  FRAGMENTS-WITH-HOLES is
     the only consistent top-level shape (§1.4), so the ambient tree is the
     one WITHOUT the locked directory and the caller plugs its own node in. *)
  Definition tree_ins (t : fstree) (i : Z) (n : fsnode) : fstree :=
    MkTree (<[i := n]> (fs_nodes t)) (fs_root t).

  Lemma tree_ins_ent (t : fstree) (i : Z) (ents : gmap fname Z) (f : fname) :
    tree_ent (tree_ins t i (NDir ents)) i f = ents !! f.
  Proof.
    rewrite /tree_ent /tree_ins /=. rewrite lookup_insert. reflexivity.
  Qed.

  (* **THE LOGICALLY-ATOMIC FORM (R8), AND THE ONLY ONE THAT IS SOUND
     HERE.**  A client that keeps the rest of the file system in an
     invariant of its own supplies this: a fupd that surrenders the AMBIENT
     tree -- everything but the directory it has locked -- and takes it
     straight back, paying out the client's chosen receipt [Φt] AT THE
     ANSWER THE COMPLETED TREE GIVES.  It is fired ONCE, at the
     linearization point.

     WHY THE LOCKED NODE IS NOT IN IT.  It cannot be: the caller holds
     [dinode_at] for that inum (out of [IcacheEscrow.ic_loaded]), and a
     second copy arriving through the fupd would meet
     [InodeRegion.dinode_at_excl].  The hole in [t] is therefore FORCED,
     not a convenience -- and it is why [fs_closed] is false in general.

     WHAT IT BUYS, AND WHAT IT DOES NOT.  It buys the right to state the
     answer as a fact about a GLOBAL tree at ONE instant.  It does NOT buy
     a path -> inode function across two instants: the next iteration of a
     walk opens the invariant again, at a tree that may have moved
     (SpecNamex.v:113-124).  Nothing here weakens that ruling. *)
  Definition dl_au (γi : gname) (γfs : fs_names) (Ed : coPset)
      (dpi : Z) (ents : gmap fname Z) (s : fname)
      (Φt : option Z -> iProp Σ) : iProp Σ :=
    (|={⊤, Ed}=> ∃ t : fstree,
       ⌜fs_nodes t !! dpi = None⌝ ∗ fs_rep γi γfs t ∗
       (fs_rep γi γfs t
        ={Ed, ⊤}=∗ Φt (tree_ent (tree_ins t dpi (NDir ents)) dpi s)))%I.

  (* FIRING IT.  The ambient fragment is handed back untouched, which is
     what makes the update ATOMIC rather than an accessor held open; the
     receipt lands at the node's own answer, which §1 has already shown to
     be dirlookup's. *)
  Lemma dl_au_fire (γi : gname) (γfs : fs_names) (Ed : coPset)
      (dpi : Z) (ents : gmap fname Z) (s : fname)
      (Φt : option Z -> iProp Σ) :
    dl_au γi γfs Ed dpi ents s Φt ={⊤}=∗ Φt (ents !! s).
  Proof.
    iIntros "Hau". iMod "Hau" as (t) "(%Hhole & Ht & Hclose)".
    iEval (rewrite tree_ins_ent) in "Hclose".
    iMod ("Hclose" with "Ht") as "HΦ". by iModIntro.
  Qed.

  (* the two arms, composed: this is what a client writes in dirlookup's
     continuation, one line per arm *)
  Lemma dl_au_found (γi : gname) (γfs : fs_names) (Ed : coPset)
      (dpi : Z) (ents : gmap fname Z) (dn : dinode)
      (data : nat -> list (bv 8)) (s : fname) (k : nat)
      (Φt : option Z -> iProp Σ) :
    node_rep (NDir ents) dn data ->
    dir_first data (dnrec dn) s = Some k ->
    dl_au γi γfs Ed dpi ents s Φt
    ={⊤}=∗ Φt (Some (bv_unsigned (dir_inum data k))).
  Proof.
    intros Hrep Hf.
    rewrite <- (node_lookup_found ents dn data s k Hrep Hf).
    iApply dl_au_fire.
  Qed.

  Lemma dl_au_miss (γi : gname) (γfs : fs_names) (Ed : coPset)
      (dpi : Z) (ents : gmap fname Z) (dn : dinode)
      (data : nat -> list (bv 8)) (s : fname)
      (Φt : option Z -> iProp Σ) :
    node_rep (NDir ents) dn data ->
    dir_first data (dnrec dn) s = None ->
    dl_au γi γfs Ed dpi ents s Φt ={⊤}=∗ Φt None.
  Proof.
    intros Hrep Hf.
    rewrite <- (node_lookup_none ents dn data s Hrep Hf).
    iApply dl_au_fire.
  Qed.

End FsLookupAu.

(* ====================================================================== *)
(*  6.  THE DOT-RECORD COMPOSITION -- §20.17.4's OWED FACT, BOTH HALVES     *)
(* ====================================================================== *)

(*  THE SEAM, AND WHY IT TAKES TWO HALVES.

    S7's [dp->nlink--] must consume one [ilink dp], and the only one in the
    system sits in the CHILD's [dir_links], at the index of the child's
    [".."] record.  Two facts are needed and neither can state the other:

      the PAYLOAD half  [DirView.dir_dots_ix self dn data] -- a LIVE
        directory's record 0 is a live ["."] naming [self] and its record 1
        is a live [".."] -- says WHERE the parent entry is.  It cannot say
        WHAT it names: "the parent" is a relation between two inodes and a
        conjunct on ONE payload cannot state it (a parent parameter would
        move every contract naming [ic_loaded]);

      the TREE half  [ents !! DOTDOT = Some dp] -- a conjunct of
        [FsRep.fnode ip (NDir ents)] -- says WHAT it names.  It cannot say
        where: [DirLinks.dir_link_at] is keyed by record INDEX and is
        name-blind (fs-icache.md §20.17.4(b)).

    **[dir_names_unique] IS WHAT JOINS THEM**, and this is the third place
    R2's amendment pays for itself.  Under the invariant any-match is
    first-match, so the live [".."] at index 1 is the ONLY live [".."] and
    the index [dirlookup] stops at IS index 1 -- which is what makes the
    tree's [".."] edge and the payload's index-1 inum the same number.
    Note that the collision is refuted by UNIQUENESS rather than by
    [dot_name <> dotdot_name]: record 0 is a live ["."], so if it also
    matched [".."] the invariant would force [0 = 1].

    ---- WHAT THE LANDED CLAUSE CHANGED, AND IT ALL HELPS -----------------

    The payload half grew a ["."] half and a [di_nlink <> 0] guard on its
    way into the escrow payloads.  Three consequences here, all favourable:

      - [(2 <= dir_nrec …)] is no longer a PREMISE this file must take --
        it is a PROJECTION of the clause, so the composition below is
        self-supplying where the earlier form made every caller carry the
        record count;
      - the record-0 facts come free, so the ["."] edge is readable at the
        tree too ([node_dots_index]'s [ents !! DOT = Some self]) -- the
        self-loop the ledger deliberately does not file a [dir_links] unit
        against, now visible as an ordinary entry;
      - [self <> 0] falls out ([DirView.dir_dots_ix_self]), which is the
        fact create's [".."] establishment could not get anywhere else.

    The [di_nlink <> 0] guard travels as a premise.  It is not a burden:
    every caller in the S7 walk holds it already (create's guard at
    sysfile.c:262, namex's at fs.c:693), and an ORPHANED directory is the
    complement clause's business, not this one's.                          *)

(* the two spellings of each dot name are one term: [FsTree]'s are stated in
   the [mword] vocabulary the tree layer uses, [DirView]'s in the [bv]
   vocabulary the record view does *)
Lemma DOT_dot_name : DOT = dot_name.
Proof.
  unfold DOT, dot_name.
  assert (Hd : (mword_of_int 46 : mword 8) = Z_to_bv 8 0x2e)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hd. reflexivity.
Qed.

Lemma DOTDOT_dotdot_name : DOTDOT = dotdot_name.
Proof.
  unfold DOTDOT, dotdot_name.
  assert (Hd : (mword_of_int 46 : mword 8) = Z_to_bv 8 0x2e)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hd. reflexivity.
Qed.

(* **BOTH DOT RECORDS, AT THE INDEX [dirlookup] STOPS ON.**  Record 0 is
   trivially first; record 1 needs the invariant to refute record 0, which
   is the join described above. *)
Lemma node_dots_first (self : Z) (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep (NDir ents) dn data ->
  dir_dots_ix self dn data ->
  bv_unsigned (di_nlink dn) <> 0 ->
  dir_first data (dnrec dn) DOT = Some 0%nat
  /\ dir_first data (dnrec dn) DOTDOT = Some 1%nat.
Proof.
  unfold dnrec. intros Hrep Hix Hnl.
  pose proof (node_rep_dir ents dn data Hrep) as Hty.
  destruct (Hix Hty Hnl) as (Hnrec & Hl0 & _ & Hn0 & Hl1 & Hn1).
  assert (Hu : dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))))
    by (destruct Hrep as (_ & Hu & _); exact Hu).
  assert (Hb0 : dir_bname data 0 = DOT).
  { unfold dir_bname. rewrite Hn0. symmetry. exact DOT_dot_name. }
  assert (Hb1 : dir_bname data 1 = DOTDOT).
  { unfold dir_bname. rewrite Hn1. symmetry. exact DOTDOT_dotdot_name. }
  split.
  - apply dir_first_Some. split; [lia | split].
    + split; [exact Hl0 | exact Hb0].
    + intros q Hq. lia.
  - apply dir_first_Some. split; [lia | split].
    + split; [exact Hl1 | exact Hb1].
    + intros q Hq [Hlq Hnq].
      (* the only record below is 0, and it is the ["."]: uniqueness, not
         a name disequality, is what refutes it *)
      assert (Hq0 : q = 0%nat) by lia. subst q.
      assert (H01 : (0%nat) = 1%nat).
      { apply (Hu 0%nat 1%nat ltac:(lia) ltac:(lia) Hl0 Hl1).
        rewrite Hb1. exact Hnq. }
      discriminate.
Qed.

(* **THE COMPOSITION.**  The tree's parent edge IS the payload's index-1
   inum, and the tree's ["."] edge IS the node's own inum. *)
Lemma node_dots_index (self dp : Z) (ents : gmap fname Z) (dn : dinode)
    (data : nat -> list (bv 8)) :
  node_rep (NDir ents) dn data ->
  dir_dots_ix self dn data ->
  bv_unsigned (di_nlink dn) <> 0 ->
  ents !! DOTDOT = Some dp ->
  dir_first data (dnrec dn) DOTDOT = Some 1%nat
  /\ dp = bv_unsigned (dir_inum data 1)
  /\ ents !! DOT = Some self
  /\ self <> 0
  /\ (2 <= dnrec dn)%nat.
Proof.
  intros Hrep Hix Hnl Hdd.
  pose proof (node_rep_dir ents dn data Hrep) as Hty.
  destruct (node_dots_first self ents dn data Hrep Hix Hnl) as [Hf0 Hf1].
  pose proof (Hix Hty Hnl) as Hproj.
  destruct Hproj as (Hnrec & _ & Hin0 & _ & _ & _).
  split; [exact Hf1 |].
  split.
  { pose proof (node_lookup_found ents dn data DOTDOT 1 Hrep Hf1) as H.
    rewrite Hdd in H. injection H as H. exact H. }
  split.
  { pose proof (node_lookup_found ents dn data DOT 0 Hrep Hf0) as H.
    rewrite Hin0 in H. exact H. }
  split; [exact (dir_dots_ix_self self dn data Hty Hnl Hix) | exact Hnrec].
Qed.

(* ...and its resource form, straight off the node fragment: this is the
   line S7 writes.  Nothing is consumed -- the fragment is only read.

   THE FRAGMENT IS INDEXED AT [self], AND THAT IS THE COUPLING: the tree's
   node key and the payload's [self] are the same number precisely because
   record 0's ["."] names the node's own inum.  Both payloads have the inum
   in hand, so it costs no arity at any call site.

   THE LAST CONJUNCT IS [DirLinks.dir_links_dotdot_out]'s OWN PREMISE,
   discharged AT THE TREE: the extraction refuses a node whose [".."] names
   itself (the root), and "the parent is not the child" is a statement the
   tree can make and the bytes cannot. *)
Section FsLookupDots.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{ICFG : icfg}.

  Lemma fdir_dots_index (γi : gname) (γfs : fs_names) (self dp : Z)
      (ents : gmap fname Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    dir_dots_ix self dn data ->
    bv_unsigned (di_nlink dn) <> 0 ->
    ents !! DOTDOT = Some dp ->
    dp <> self ->
    fdir γi γfs self ents dn bm data -∗
      ⌜dir_first data (dnrec dn) DOTDOT = Some 1%nat
       /\ dp = bv_unsigned (dir_inum data 1)
       /\ ents !! DOT = Some self
       /\ self <> 0
       /\ (2 <= dnrec dn)%nat
       /\ bv_unsigned (di_type dn) = T_DIR_z
       /\ bv_unsigned (dir_inum data 1) <> self⌝.
  Proof.
    intros Hix Hnl Hdd Hne. iIntros "(_ & _ & %Hrep)". iPureIntro.
    destruct (node_dots_index self dp ents dn data Hrep Hix Hnl Hdd)
      as (Hf1 & Hz & Hdot & Hs0 & Hnrec).
    split; [exact Hf1 |]. split; [exact Hz |]. split; [exact Hdot |].
    split; [exact Hs0 |]. split; [exact Hnrec |].
    split; [exact (node_rep_dir ents dn data Hrep) |].
    rewrite <- Hz. exact Hne.
  Qed.

  (* ===================================================================== *)
  (*  THE PAYLOAD -> TREE CONSTRUCTOR (fs-fragments §7.5.8, item S2-0).     *)
  (*                                                                       *)
  (*  S2-0's finding was that F1b and F2 were landed, green and             *)
  (*  UNREACHABLE: [FsRep.fnode] demands [node_rep], whose NDir case        *)
  (*  demands [dir_names_unique], and that predicate occurred in no         *)
  (*  payload, no spec and no walk -- so no proof in the tree could build   *)
  (*  an [fnode], an [fdir], an [fslice] or an [fs_rep].  With [dir_uniq]   *)
  (*  riding in [IcacheEscrow.ic_loaded] the gap closes here, in one        *)
  (*  lemma: every OTHER ingredient of [fdir] was already in the payload.   *)
  (*                                                                       *)
  (*  IT IS AN ACCESSOR, NOT A CONVERSION.  [fdir] holds two of the         *)
  (*  payload's ten conjuncts ([dinode_at], [inode_blocks]); the wand puts  *)
  (*  them back, so a walk can read its tree and keep its bundle.           *)
  (*                                                                       *)
  (*  THE NODE IS NOT GUESSED -- it is [FsTree.dir_view] of the payload's   *)
  (*  OWN bytes, which is what makes the lemma unconditional in [ents].     *)
  (*  **AND THAT IS ALSO ITS LIMIT** (S7-unlink's D1): a walk that builds   *)
  (*  its [ents] this way learns [ents !! DOTDOT = Some (dir_inum data 1)]  *)
  (*  and nothing more, so feeding it to [fdir_dots_index] instantiates     *)
  (*  [dp] AS [dir_inum data 1] and returns the premise it was given.  The  *)
  (*  parent-edge IDENTITY is a two-inode relation; no reading of ONE       *)
  (*  payload can supply it.  See fs-sysfile.md, S7-unlink W5-DIR.          *)
  (* ===================================================================== *)

  Lemma inum_of_self (inum : mword 32) : inum_of (bv_unsigned inum) = inum.
  Proof.
    apply bv_eq. apply inum_of_unsigned.
    pose proof (bv_unsigned_in_range 32 inum) as H.
    unfold bv_modulus in H. cbn in H. lia.
  Qed.

  Lemma ic_loaded_fdir `{XI : CurCtx} (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    ic_loaded gfs gi cov logstart k inum dn bm -∗
      ∃ data : nat -> list (bv 8),
        fdir gi gfs (bv_unsigned inum)
             (dir_view data (dnrec dn)) dn bm data ∗
        (fdir gi gfs (bv_unsigned inum)
              (dir_view data (dnrec dn)) dn bm data -∗
         ic_loaded gfs gi cov logstart k inum dn bm).
  Proof.
    intros Hty.
    iIntros "H". iDestruct (ic_loaded_open with "H") as (data)
      "(%Hiok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta &
        Haddrs & Hind & Hblocks & Hdv & Hfv & Htop)".
    assert (Hrep : node_rep (NDir (dir_view data (dnrec dn))) dn data).
    { unfold node_rep, dnrec. split_and!;
        [exact Hty | exact (Hduq Hty) | reflexivity]. }
    iExists data.
    iSplitL "Hdiat Hblocks".
    { rewrite /fdir inum_of_self.
      iSplitL "Hdiat"; [iExact "Hdiat" |].
      iSplitL "Hblocks"; [iExact "Hblocks" |].
      iPureIntro. exact Hrep. }
    iIntros "Hfd". rewrite /fdir inum_of_self.
    iDestruct "Hfd" as "(Hdiat & Hblocks & _)".
    iApply (ic_mk_loaded gfs gi cov logstart k inum dn bm data
              Hiok Hrl Hdok Hddix Hdoc Hduq
              with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdv Hfv Htop").
  Qed.

  (* ...and the [fnode] form, which is what a client of F1b asks for. *)
  Lemma ic_loaded_fnode `{XI : CurCtx} (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    ic_loaded gfs gi cov logstart k inum dn bm -∗
      ∃ data : nat -> list (bv 8),
        fnode gi gfs (bv_unsigned inum)
              (NDir (dir_view data (dnrec dn))) ∗
        (fdir gi gfs (bv_unsigned inum)
              (dir_view data (dnrec dn)) dn bm data -∗
         ic_loaded gfs gi cov logstart k inum dn bm).
  Proof.
    intros Hty. iIntros "H".
    iDestruct (ic_loaded_fdir gfs gi cov logstart k inum dn bm Hty with "H")
      as (data) "[Hfd Hback]".
    iExists data. iSplitR "Hback"; [| iExact "Hback"].
    iApply (fdir_fnode with "Hfd").
  Qed.

End FsLookupDots.
