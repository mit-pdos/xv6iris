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
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import FsTree.
Require Import FsRep.
Require Import SpecDirlookup.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ}.
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
     - each arm carries the tree-level answer beside the byte-level one.

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
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn : dinode)
    (dpi : Z) (ents : gmap fname Z)                   (* THE TREE-LEVEL NODE *)
    (fn : nat -> bv 8)                                (* the caller's name   *)
    (hasp : bool) (pofv : mword 32)                   (* poff, two-armed     *)
    (pidv : mword 32) (dq dqd dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) (lks : gset string) :=
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
  (* (3) iget's argument bound, over the records *)
  dir_inums_ok data nrec nib ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (m !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = ip ->
  eq_vec (m !!! Regidx (mword_of_int 12 : mword 5)) zero_reg = negb hasp ->
  eb = true ->
  locks_below lks "bcache" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY: the cells, and THE NODE FRAGMENT ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  fdir γi γfs dpi ents dn bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's [f]) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
  (* ---- poff: a 4-byte cell, or nothing ---- *)
  (if hasp then pf ↦₄ pofv else emp) -∗
  (* ---- the caller's own pid cell ---- *)
  p_pid pj ↦₄{dq} pidv -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslot bn -∗
  (* ---- THE ICACHE, exactly as iget takes it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  iref_slot -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool) (k : nat) (kslot : nat) (q : Qp),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
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
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslot bn -∗
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
            (if hasp
             then pf ↦₄ (mword_of_int (Z.of_nat (16 * k)) : mword 32)
             else emp)
       else ⌜ents !! s = None⌝ ∗
            ⌜dir_first data nrec s = None
             /\ mf !!! Regidx (mword_of_int 10 : mword 5)
                = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slot ∗
            (if hasp then pf ↦₄ pofv else emp)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE LIFTING.  A functor over the LANDED contract, not a new interface:
   SpecDirlookup does not move (R10, §20.18 ruling 1), and this file's whole
   claim is that the tree reading is available CALLER-SIDE. *)
Module FsLookupTree (DL : DIRLOOKUP).

  Lemma wp_dirlookup_tree
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
        ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (dpi : Z) (ents : gmap fname Z)
      (fn : nat -> bv 8)
      (hasp : bool) (pofv : mword 32)
      (pidv : mword 32) (dq dqd dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) :
      wp_dirlookup_tree_body γs j γl γu γd γk pd pav pu bn γfs γi cn gtl
                             γa γf cov logstart nib dev ip bm data dn
                             dpi ents fn hasp pofv pidv dq dqd dqn
                             m K eb b lks.
  Proof.
    unfold wp_dirlookup_tree_body. cbv zeta.
    intros HK Hlg Hbwf Hbcov Hszb Hdio Hj Hgs Ha0 Ha2 Heb Hlkb.
    iIntros "Hcg Hcnt Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta Hmap Hfdir
             Hname Hpoff Hppid Hprocs Hdev Hdgeom Hdlk Hbslot
             Hitb2 Hitbl Hesc Hisl Hcont".
    iDestruct "Hfdir" as "(Hdiat & Hblocks & %Hrep)".
    iApply (DL.wp_dirlookup_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn gtl
              γa γf cov logstart nib dev ip bm data dn fn hasp pofv
              pidv dq dqd dqn m K eb b lks
              HK (node_rep_T_DIR ents dn data Hrep) Hlg Hbwf Hbcov Hszb
              Hdio Hj Hgs Ha0 Ha2 Heb Hlkb
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hkenv
                    Hidev Hmeta Hmap Hblocks Hname Hpoff
                    Hppid Hprocs Hdev Hdgeom Hdlk Hbslot
                    Hitb2 Hitbl Hesc Hisl").
    iIntros (CIDd Hgd mf found k kslot q)
      "%Hcs Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hname Hppid Hbslot Harm".
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDd Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf found k kslot q
              with "[] Hcg Hcnt Hpc Hidev Hmeta Hmap
                    [Hdiat Hblocks] Hname Hppid Hbslot [Harm]").
    - iPureIntro. exact Hcs.
    - iApply (fdir_intro γi γfs dpi ents dn bm data Hrep with "Hdiat Hblocks").
    - destruct found.
      + iDestruct "Harm" as "(%Hpure & Href & Hpf)".
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
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ}.
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
(*  6.  THE ".." COMPOSITION -- DEFERRED, ONE COMMIT BEHIND                *)
(* ====================================================================== *)

(*  §20.17.4's owed [".."] fact needs BOTH halves, and only one of them is
    committed yet.  The TREE half is here already -- [ents !! DOTDOT = Some
    dp] is a conjunct of [FsRep.fnode ip (NDir ents)], and [FsRep.fnode_dotdot]
    converts it to the record index.  The PAYLOAD half is
    [DirView.dir_dotdot_ix] ("a directory's record 1 is live and named
    ['..']"), which lands with the create owner's increment.

    The composition -- [node_dotdot_index] / [fdir_dotdot_index], concluding
    [dp = bv_unsigned (dir_inum data 1)] and [dir_first data nrec ".." = Some
    1] -- is WRITTEN AND VERIFIED GREEN against that payload half, and lands
    here the moment it is committed.  It is a dozen lines and it needs no
    change to anything in this file.

    **[dir_names_unique] IS WHAT JOINS THE TWO HALVES**, and that is the third
    place R2's amendment pays for itself: under the invariant any-match is
    first-match, so a live [".."] at index 1 is the ONLY live [".."] and the
    index [dirlookup] stops at IS index 1.  Neither half can state the other
    -- "the parent" is a relation between two inodes and a conjunct on ONE
    payload cannot say it, while [DirLinks.dir_link_at] is keyed by record
    INDEX and is name-blind.                                                *)
