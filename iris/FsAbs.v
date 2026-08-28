(* FsAbs.v -- THE SPEC LAYER'S ABSTRACT STATE, AND IT IS A READING.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 1-3
   (v3), lane A items (i) and (ii) of claude-notes/projects/fs-syscall-specs.md.

   WHAT THIS FILE IS.  Section 1's [absnode]/[anode]/[aview] and section 2's
   client-facing carriers, with EVERY ONE OF THEM DEFINED OFF GHOST STATE THE
   KERNEL PROOFS ALREADY MAINTAIN.  Nothing here is minted, nothing here is
   an invariant, and nothing here asks a landed proof to move (R10):

     [abs_of]   is [FsStateInode]'s readings ([fn_is_dir], [dir_entries],
                [fn_file_bytes], [fn_nlink]) packaged into one record.  The
                decoding is not re-done; [dir_entries] is still
                [FsTree.dir_view]'s FIRST-MATCH reading (fs-fragments.md
                section 1.2) and ".", ".." are ordinary names in it.
     [nview]    is [FsState.top_frag_q] under [abs_of].  Its three laws --
                agreement, split/join, timelessness -- are [top_frag_q_agree],
                [top_frag_q_split] and [top_frag_q_timeless] read through the
                [abs_of] equation, and its STABILITY is the landed mover
                discipline itself: every retag ([InodeRegion.ireg_top_retag])
                needs the WHOLE element, so an outstanding share pins the
                node.  That is why there is no cancellation arm anywhere
                below -- contrast [DirViewPin.dvp_lost], which exists because
                a [dv_pin] is a CANCELLABLE lend.
     [astate]   is THE γtop AUTHORITY ITSELF, read through [abs_of]
                ([abs_view]): [astate Γ av] is [ghost_map_auth (γtop Γ) 1 I]
                for the [I] whose reading is [av].  No new invariant, no
                [aviewN] (section 9 Q3, ruled) -- and, since durable-disk EV,
                no [fs_state] leg either (see below).

   WHERE THE AUTHORITY LIVES, AND WHY [fs_view] IS GONE (durable-disk EV).
   The EV campaign deleted [FsState.fs_view] -- the old
   [∃ S, ghost_map_auth (γtop Γ) 1 (fss_inodes S) ∗ fs_state Γ S] bundle --
   and put the live γtop authority in ITS OWN invariant,
   [InodeRegion.ftop_inv γfs = inv ftopN (ftop_body γfs)], whose body holds
   the RAW map [I : gmap Z fs_node] beside the arming registry [icfg_lk] and
   the row [ftop_clean I A].  [FsState.fs_state] also grew a [dfrac].  Two
   consequences for this file, and they are the only two:

     (1) [astate] DROPPED THE [fs_state] CONJUNCT.  No lemma here ever used
         the byte legs or [fs_geom] -- [astate_nview_dq] needs the authority
         and nothing else -- so the state predicate was dead weight that only
         served to name an [S].  [abs_view] is correspondingly restated over
         the RAW MAP ([abs_of <$> I]) rather than over [fss_inodes S]: that is
         the form [ftop_body] hands out, it is the same function on the nose
         at [I := fss_inodes S], and it keeps [abs_view_lookup] and
         [astate_nview_dq] byte-identical in shape.  [astate_timeless] lost
         its [GTimeless Γ] premise with the byte legs (strictly weaker
         hypothesis, same name).

     (2) [fs_view_astate], the old equivalence, is replaced by an ACCESSOR
         against the authority's real home: [astate_intro]/[astate_elim] are
         the (trivial) intro and elim against a raw [ghost_map_auth], and
         [ftop_astate_acc] / [ftop_astate_ro] in section 5 borrow [astate]
         out of [ftop_body] -- the shape an AU proof uses after opening
         [ftopN].  The live Γ is [FsBytesGamma.fs_gamma_L γfs] and the gname
         tie IS DEFINITIONAL: [fs_gamma_L] is
         [MkFsView _ (fs_link γfs) (fs_top γfs)], so
         [γtop (fs_gamma_L γfs) = fs_top γfs] by [reflexivity]
         ([ftop_gamma_top] states it).  Section 5 is LAST IN THE FILE and its
         [Require Import InodeRegion] sits immediately above it, so the
         region's cone cannot shadow a name any earlier section resolves.
         The give-back wand carries the ROW ([inode_local] at every entry of
         the returned map), because [ftop_body]'s [ftop_clean] is not
         recoverable from an abstract [av]: [abs_of] forgets the record.
         That is the same obligation [InodeRegion.ireg_top_retag] already
         charges every mover, so nothing new is asked of a caller.

   SECTION 3's PATH LAYER.  [apath_at] is the hop-by-hop first-match lookup
   the design names [path_at]; it is spelled [apath_at] because
   [FsTree.path_at] -- the same fold over [fstree] -- is landed and sits in
   this file's cone, and shadowing a landed name is how a downstream file
   silently gets the wrong function.  The two are ONE function up to
   [abs_tree] ([apath_at_tree]), so FsTree's path algebra is inherited rather
   than re-proved.

   THE PINNED WALK, RESTATED (section 3's "functional corollary").  A client
   that holds an [nview] share for every directory on the path gets the walk's
   answer AS [apath_at], with no divergence arm and no possible miss.  The
   walk's hop ([SpecNameiTr.nx_hop]) is [ax_hop] at the lent fragment
   [DirViewG.dv_half]: [ax_hop] is that definition with the lent predicate
   abstracted, so instantiating [F := dv_half] gives [nx_hop] and
   [ax_hops_from] gives [nx_hops_from] ON THE NOSE.  That is a CHECKED
   claim, not a reading of the source -- in a scratch file over the namei
   cone (which is why it is not in this build: it would drag 336 files into
   a spec-layer leaf),

       Lemma nx_hop_is_ax_hop P Pmiss k s :
         nx_hop P Pmiss k s = ax_hop dv_half P Pmiss k s.
       Proof. reflexivity. Qed.
       Lemma nx_hops_is_ax_hops P Pmiss pl n :
         nx_hops_from P Pmiss pl n
         = ax_hops_from dv_half P Pmiss (path_elems pl) n.
       Proof. reflexivity. Qed.

   both close, under `{!riscvGS Σ, !xv6G Σ, !fileG Σ}`.  What the chain lemma
   needs of [F] is exactly one law -- [lend_agrees]: the lent entry map
   agrees with a client-held [nview] -- and it is DISCHARGED here for the
   abstract-state lend [alend] ([alend_agrees]).  For the landed [dv_half] it
   is NOT derivable in this file and must not be faked: [dv_half] is an [own]
   at [icfg_dview] and [top_frag_q] is a [ghost_map] element at [γtop] --
   two disjoint ghosts, tied only inside the icache payload ([ic_loaded]
   carries both since N-1).  That seam is exactly the one
   fs-syscall-specs.md section 2 schedules ("the hop seam moves first, then
   the [dv_*] column comes off the payloads"); when it lands, this file's
   theorem applies unchanged with [F := dv_half].

   BINDERS.  [fsLinkG]/[fsTopG] are [Xv6G.xv6G] MEMBERS, so this file binds
   the members and never the bundle -- FsState.v's own binder list, verbatim
   (durable-notes, "ONE BUNDLE PER GHOST CLASS").  [Xv6Cameras] is IMPORTED,
   not merely required, or [fsTopG]'s field instances would be inert. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import iprop own ghost_map fancy_updates.
Require Import DinodeEnc.
Require Import DirView.        (* [T_DIR_z]                                  *)
Require Import FsTree.         (* [fname], [fsnode], [path_at], [node_of]    *)
Require Import FsImg.          (* [T_FILE_z], [ROOTINO]                      *)
Require Import Xv6Cameras.     (* [fsTopG]/[fsLinkG] -- IMPORTED (see header) *)
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
(*  3.  THE CARRIER: [nview], AND THE STATE ACCESSOR [astate]             *)
(* ===================================================================== *)

Section FsAbsCarrier.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.

  (* i ↦ₐ{q} a, at a general dfrac and at a fraction.  [nview] IS the
     [DfracOwn] reading, on the nose (as [top_frag] is [top_frag_q]'s), so a
     site that spells either sees the same proposition. *)
  Definition nview_dq Γ (dq : dfrac) (i : Z) (a : anode) : iProp Σ :=
    (∃ n, top_frag_q Γ dq i n ∗ ⌜abs_of n = a⌝)%I.

  Definition nview Γ (q : Qp) (i : Z) (a : anode) : iProp Σ :=
    nview_dq Γ (DfracOwn q) i a.

  Lemma nview_eq Γ q i a :
    nview Γ q i a = (∃ n, top_frag_q Γ (DfracOwn q) i n ∗ ⌜abs_of n = a⌝)%I.
  Proof. reflexivity. Qed.

  (* the introduction rule: a holder of the landed fragment holds the
     carrier, and there is nothing to update to get it *)
  Lemma nview_of_frag Γ dq i n : top_frag_q Γ dq i n ⊢ nview_dq Γ dq i (abs_of n).
  Proof. iIntros "H". iExists n. by iFrame. Qed.

  Lemma nview_frag Γ dq i a :
    nview_dq Γ dq i a ⊢ ∃ n, top_frag_q Γ dq i n ∗ ⌜abs_of n = a⌝.
  Proof. by iIntros "H". Qed.

  Global Instance nview_dq_timeless Γ dq i a : Timeless (nview_dq Γ dq i a).
  Proof. rewrite /nview_dq. apply _. Qed.
  Global Instance nview_timeless Γ q i a : Timeless (nview Γ q i a).
  Proof. rewrite /nview. apply _. Qed.

  (* AGREEMENT, off [top_frag_q_agree]: two shares of one inum name the same
     node, hence the same reading. *)
  Lemma nview_dq_agree Γ dq1 dq2 i a1 a2 :
    nview_dq Γ dq1 i a1 -∗ nview_dq Γ dq2 i a2 -∗ ⌜a1 = a2⌝.
  Proof.
    rewrite /nview_dq. iIntros "H1 H2".
    iDestruct "H1" as (n1) "[H1 %Ha1]". iDestruct "H2" as (n2) "[H2 %Ha2]".
    iDestruct (top_frag_q_agree with "H1 H2") as %<-.
    iPureIntro. by rewrite -Ha1 -Ha2.
  Qed.

  Lemma nview_agree Γ q1 q2 i a1 a2 :
    nview Γ q1 i a1 -∗ nview Γ q2 i a2 -∗ ⌜a1 = a2⌝.
  Proof. apply nview_dq_agree. Qed.

  Lemma nview_valid Γ dq i a : nview_dq Γ dq i a -∗ ⌜✓ dq⌝.
  Proof.
    rewrite /nview_dq /top_frag_q. iIntros "H". iDestruct "H" as (n) "[H _]".
    by iDestruct (ghost_map_elem_valid with "H") as %?.
  Qed.

  (* SPLIT / JOIN, off [top_frag_q_split]: the [abs_of] equation rides along
     both ways -- forward it is copied, backward the two nodes are identified
     by agreement first. *)
  Lemma nview_split Γ (q1 q2 : Qp) i a :
    nview Γ (q1 + q2)%Qp i a ⊣⊢ nview Γ q1 i a ∗ nview Γ q2 i a.
  Proof.
    rewrite /nview /nview_dq. iSplit.
    - iIntros "H". iDestruct "H" as (n) "[H %Ha]".
      rewrite top_frag_q_split. iDestruct "H" as "[H1 H2]".
      iSplitL "H1"; iExists n; by iFrame.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (n1) "[H1 %Ha1]". iDestruct "H2" as (n2) "[H2 %Ha2]".
      iDestruct (top_frag_q_agree with "H1 H2") as %<-.
      iExists n1. rewrite top_frag_q_split.
      iSplitL "H1 H2"; [iFrame | by iPureIntro].
  Qed.

  Global Instance nview_fractional Γ i a : Fractional (fun q => nview Γ q i a).
  Proof. intros q1 q2. apply nview_split. Qed.
  Global Instance nview_as_fractional Γ q i a :
    AsFractional (nview Γ q i a) (fun q => nview Γ q i a) q.
  Proof. split; [reflexivity | apply _]. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3a.  [astate av]: the γtop AUTHORITY, read through [abs_of]         *)
  (* ------------------------------------------------------------------ *)

  (* OVER THE RAW MAP since durable-disk EV (header, consequence (1)): it is
     the form [InodeRegion.ftop_body] holds, and at [I := fss_inodes S] it is
     the old function on the nose. *)
  Definition abs_view (I : gmap Z fs_node) : aview := abs_of <$> I.

  Lemma abs_view_lookup I i n :
    I !! i = Some n -> abs_view I !! i = Some (abs_of n).
  Proof. intros Hi. by rewrite /abs_view lookup_fmap Hi. Qed.

  (* The pure conjunct goes LAST (durable-notes) even in a new definition:
     every consumer destructures the authority first. *)
  Definition astate Γ (av : aview) : iProp Σ :=
    (∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝)%I.

  Global Instance astate_timeless Γ av : Timeless (astate Γ av).
  Proof. rewrite /astate. apply _. Qed.

  (* INTRO AND ELIM AGAINST THE AUTHORITY.  This is all that is left of the
     old [fs_view_astate] equivalence once the authority moved into
     [InodeRegion.ftop_inv]: [astate] is a READING of [ghost_map_auth], so
     both directions are the definition.  The borrow off [ftop_body] itself
     is [ftop_astate_acc] (section 5). *)
  Lemma astate_intro Γ I :
    ghost_map_auth (γtop Γ) 1 I ⊢ astate Γ (abs_view I).
  Proof. iIntros "Ha". iExists I. by iFrame. Qed.

  Lemma astate_elim Γ av :
    astate Γ av ⊢ ∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝.
  Proof. by iIntros "H". Qed.

  (* A HELD FRAGMENT AGREES WITH THE AUTHORITY'S ROW. *)
  Lemma astate_nview_dq Γ av dq i a :
    astate Γ av -∗ nview_dq Γ dq i a -∗ ⌜av !! i = Some a⌝.
  Proof.
    rewrite /astate /nview_dq /top_frag_q.
    iIntros "Hst Hn". iDestruct "Hst" as (I) "(Ha & %Hav)".
    iDestruct "Hn" as (n) "[Hf %Han]".
    iDestruct (ghost_map_lookup with "Ha Hf") as %Hl.
    iPureIntro. subst av. by rewrite (abs_view_lookup I i n Hl) Han.
  Qed.

  Lemma astate_nview Γ av q i a :
    astate Γ av -∗ nview Γ q i a -∗ ⌜av !! i = Some a⌝.
  Proof. apply astate_nview_dq. Qed.

End FsAbsCarrier.

(* ===================================================================== *)
(*  4.  THE PINNED WALK OVER THE NEW CARRIER                              *)
(* ===================================================================== *)

Section FsAbsWalk.
  Context `{!invGS_gen hlc Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ONE CALLER-SUPPLIED ATOMIC STEP, with the LENT FRAGMENT ABSTRACTED.
     [SpecNameiTr.nx_hop] is [ax_hop DirViewG.dv_half] and
     [SpecNameiTr.nx_hops_from P Pmiss pl n] is
     [ax_hops_from dv_half P Pmiss (path_elems pl) n]: same binders, same
     single [={⊤}=∗], same "hand the fragment back at the same [dq]". *)
  Definition ax_hop (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (k : nat) (s : fname) : iProp Σ :=
    (∀ (d : Z) (ents : gmap fname Z) (dqv : dfrac),
       P k d -∗ F d dqv ents ={⊤}=∗
       F d dqv ents ∗
       match ents !! s with
       | Some c => P (S k) c
       | None   => Pmiss k d
       end)%I.

  Definition ax_hops_from (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (ps : list fname) (n : nat) : iProp Σ :=
    ([∗ list] j ↦ s ∈ drop n ps, ax_hop F P Pmiss (n + j)%nat s)%I.

  (* THE ONE LAW THE CHAIN LEMMA ASKS OF THE LENT FRAGMENT: what the walk
     lends at [d] agrees with what a client holds at [d].  Everything else
     below is pure bookkeeping. *)
  Definition lend_agrees Γ (F : Z -> dfrac -> gmap fname Z -> iProp Σ) : Prop :=
    forall (d : Z) (dq : dfrac) (ents : gmap fname Z) (q : Qp) (a : anode),
      ⊢ F d dq ents -∗ nview Γ q d a -∗ ⌜an_node a = ADir ents⌝.

  (* the abstract state's own lend -- the shape the seam should give the
     walk once the hop fires off the payload's [top_frag] *)
  Definition alend Γ (d : Z) (dq : dfrac) (ents : gmap fname Z) : iProp Σ :=
    (∃ nl : nat, nview_dq Γ dq d (MkAnode (ADir ents) nl))%I.

  Lemma alend_agrees Γ : lend_agrees Γ (alend Γ).
  Proof.
    intros d dq ents q a. rewrite /alend /nview.
    iIntros "Hl Hn". iDestruct "Hl" as (nl) "Hl".
    iDestruct (nview_dq_agree with "Hl Hn") as %<-. by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4a.  The pins, the cursor, and the hop discharged from a pin        *)
  (* ------------------------------------------------------------------ *)

  (* ONE PIN: the client's share of a directory on the chain, beside the row
     of [av] it names.  There is NO cancellation arm (contrast
     [DirViewPin.dvp_lost]): a [top_frag_q] share is not a lend, and every
     mover needs the whole element. *)
  Definition apn_pin Γ (q : Qp) (av : aview) (d : Z) : iProp Σ :=
    (∃ a, ⌜av !! d = Some a⌝ ∗ nview Γ q d a)%I.

  (* the pins the walk has NOT yet spent, from hop [k] on; the directory
     visited at hop [k + j] is [ds !!! (k + j)] *)
  Definition apn_pins Γ (q : Qp) (av : aview) (ds : list Z) (ps : list fname)
      (k : nat) : iProp Σ :=
    ([∗ list] j ↦ y ∈ drop k ps, apn_pin Γ q av (ds !!! (k + j)%nat))%I.

  Definition apn_P Γ (q : Qp) (av : aview) (ds : list Z) (ps : list fname)
      (k : nat) (d : Z) : iProp Σ :=
    (⌜d = ds !!! k⌝ ∗ apn_pins Γ q av ds ps k)%I.

  (* A MISS IS IMPOSSIBLE ON A PINNED CHAIN, so the miss receipt is [False]
     and the walk's failure post's miss arm is refutable. *)
  Definition apn_Pmiss : nat -> Z -> iProp Σ := fun _ _ => False%I.

  Lemma apn_Pmiss_absurd (k : nat) (d : Z) : apn_Pmiss k d -∗ False.
  Proof. by iIntros "H". Qed.

  (* THE HOP, DISCHARGED FROM THE PIN.  Agreement forces the lent entry map
     to be the pinned one, the run says what that map answers, and the
     cursor steps.  This is the whole file's content. *)
  Lemma apn_hop Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (k : nat) (s : fname) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    ps !! k = Some s ->
    ⊢ ax_hop F (apn_P Γ q av ds ps) apn_Pmiss k s.
  Proof.
    intros Hag Hr Hk. rewrite /ax_hop {2}/apn_P.
    iIntros (d ents dqv) "[%Hd Hpins] HF". subst d.
    rewrite {1}/apn_pins (drop_S _ _ _ Hk) big_sepL_cons Nat.add_0_r.
    iDestruct "Hpins" as "[Hpin Htl]".
    iDestruct "Hpin" as (a) "[%Hav Hn]".
    iDestruct (Hag (ds !!! k) dqv ents q a with "HF Hn") as %Hnd.
    assert (Hlk : ents !! s = Some (ds !!! S k)).
    { pose proof (arun_step_tot av root ps ds k s Hr Hk) as Hst.
      rewrite /astep /aents Hav /= /anode_ents Hnd /= in Hst. exact Hst. }
    rewrite Hlk. iModIntro. iFrame "HF".
    rewrite /apn_P /apn_pins. iSplitR; [by iPureIntro |].
    iApply (big_sepL_mono with "Htl").
    intros jj y _. by rewrite Nat.add_succ_r Nat.add_succ_l.
  Qed.

  (* the whole family, from hop [n] on *)
  Lemma apn_hops Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (n : nat) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    ⊢ ax_hops_from F (apn_P Γ q av ds ps) apn_Pmiss ps n.
  Proof.
    intros Hag Hr. rewrite /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    by iApply (apn_hop Γ q av F root ps ds (n + j)%nat s).
  Qed.

  (* the cursor at hop 0: the walk starts at the root and so does the run *)
  Lemma apn_P_start Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) :
    arun av root ps ds ->
    apn_pins Γ q av ds ps 0%nat -∗ apn_P Γ q av ds ps 0%nat root.
  Proof.
    intros Hr. iIntros "Hp". rewrite /apn_P. iSplitR; [| iFrame "Hp"].
    iPureIntro. symmetry. exact (arun_head _ _ _ _ Hr).
  Qed.

  (* ...AND WHAT THE CURSOR SAYS AT THE END: the walk's answer IS
     [apath_at].  This is section 3's functional corollary. *)
  Lemma apn_P_final Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) (iL : Z) :
    arun av root ps ds ->
    apn_P Γ q av ds ps (length ps) iL -∗ ⌜apath_at av root ps = Some iL⌝.
  Proof.
    intros Hr. rewrite /apn_P. iIntros "[%Hd _]". iPureIntro.
    rewrite (arun_apath_tot _ _ _ _ Hr). by rewrite Hd.
  Qed.

  (* THE PACKAGE a caller of the trace contract instantiates: the cursor at
     the root, the hop family the contract asks for, and the reading of the
     cursor the contract returns.  With [F := DirViewG.dv_half] and
     [ps := path_elems pl] the middle component IS
     [SpecNameiTr.nx_hops_from] and the whole thing is [wp_namei_tr]'s two
     trace premises plus its success post -- see the header for the one
     seam that instantiation still needs. *)
  Lemma apn_walk Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    apn_pins Γ q av ds ps 0%nat -∗
      apn_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from F (apn_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apn_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝).
  Proof.
    intros Hag Hr. iIntros "Hp".
    iDestruct (apn_P_start Γ q av root ps ds Hr with "Hp") as "HP".
    iFrame "HP". iSplitR.
    - by iApply (apn_hops Γ q av F root ps ds 0%nat).
    - iIntros (iL) "HP". by iApply (apn_P_final Γ q av root ps ds iL Hr).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4b.  Building the pins: shares plus the state's own rows            *)
  (* ------------------------------------------------------------------ *)

  Lemma big_sepL_apn_pin Γ (q : Qp) (av : aview) {A : Type}
      (l : list A) (f : nat -> Z) :
    astate Γ av -∗ ([∗ list] j ↦ y ∈ l, ∃ a, nview Γ q (f j) a) -∗
      astate Γ av ∗ ([∗ list] j ↦ y ∈ l, apn_pin Γ q av (f j)).
  Proof.
    revert f. induction l as [| x l IH]; intros f.
    - iIntros "Hst _". by iFrame.
    - iIntros "Hst H". rewrite !big_sepL_cons.
      iDestruct "H" as "[Hh Ht]". iDestruct "Hh" as (a) "Hn".
      iDestruct (astate_nview with "Hst Hn") as %Hav.
      iDestruct (IH (fun j => f (S j)) with "Hst Ht") as "[Hst Ht]".
      iFrame "Hst Ht". rewrite /apn_pin. iExists a. by iFrame.
  Qed.

  Lemma apn_pins_of_views Γ (q : Qp) (av : aview) (ds : list Z)
      (ps : list fname) (k : nat) :
    astate Γ av -∗
    ([∗ list] j ↦ y ∈ drop k ps, ∃ a, nview Γ q (ds !!! (k + j)%nat) a) -∗
      astate Γ av ∗ apn_pins Γ q av ds ps k.
  Proof.
    iIntros "Hst Hl". rewrite /apn_pins.
    by iApply (big_sepL_apn_pin Γ q av (drop k ps)
                 (fun j => ds !!! (k + j)%nat) with "Hst Hl").
  Qed.

End FsAbsWalk.

(* [apn_pins] is a big-op behind a [Definition]: seal it, or an [iFrame]
   near it resolves its instances through the whole list (durable-notes). *)
Global Typeclasses Opaque apn_pins.

(* ===================================================================== *)
(*  5.  THE BORROW: [astate] OUT OF [InodeRegion.ftop_body]               *)
(* ===================================================================== *)

(* LAST IN THE FILE, AND THE REQUIRE SITS RIGHT HERE, for the reason the
   header gives: the region's cone is large and nothing above this line may
   have a name of it resolved by accident.  Everything sections 1-4 state is
   already elaborated when this is read. *)
Require Import RiscvPtsto.     (* [riscvGS], a member of the binder list    *)
Require Import FsBlocks.       (* [fs_names] / [fs_top]: the era's gnames   *)
Require Import FsBytesGamma.   (* [fs_gamma_L]: the LIVE Γ                  *)
Require Import InodeRegion.    (* [ftop_body]/[ftop_clean]: its real home   *)

Section FsAbsFtop.
  (* InodeRegion's own binder list, verbatim (it binds MEMBERS, not the
     [Xv6G.xv6G] bundle -- durable-notes, "ONE BUNDLE PER GHOST CLASS"). *)
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ, !fsTopG Σ, !fsLinkG Σ}.
  Context `{ICFG : icfg}.

  (* THE TIE, AND IT IS DEFINITIONAL: [fs_gamma_L γfs] is
     [MkFsView _ (fs_link γfs) (fs_top γfs)], so the abstract map [astate]
     reads at the live Γ and the map [ftop_body] holds the authority of are
     ONE GNAME.  Stated so a downstream [rewrite] has a name to cite; the
     proof is [reflexivity]. *)
  Lemma ftop_gamma_top (γfs : fs_names) : γtop (fs_gamma_L γfs) = fs_top γfs.
  Proof. reflexivity. Qed.

  (* THE ACCESSOR THAT REPLACES [fs_view_astate].  An AU proof opens [ftopN],
     lands on [ftop_body], and takes this: it gets the abstract state at the
     live Γ, and owes back an authority whose every entry is well-formed.

     WHY THE ROW IS ON THE GIVE-BACK.  [ftop_body]'s [ftop_clean I A] is a
     statement about the RECORDS, and [abs_of] forgets them, so no [av] can
     pay for it; the mover re-establishes [inode_local] anyway ([ireg_top_retag]
     charges exactly this, and [FsStateEra.inode_local_of_ok_rec] is the one
     line that assembles it).  The obligation is stated at the STRONGER,
     A-free form -- every entry local -- which implies [ftop_clean I' A] for
     the [A] the body happens to carry, so the caller never has to see the
     arming registry.  A caller that suspends the row instead ([ireg_arm])
     is not this accessor's customer: it moves the map through
     [ireg_top_retag_armed] and never opens [ftopN] itself.

     WHY THE GIVE-BACK NAMES THE MAP AND NOT JUST [astate].  [abs_view] is
     not injective (again: [abs_of] forgets the record), so "an [astate] at
     some [av']" does not say WHICH map the caller is returning, and the row
     cannot be charged for a map nobody named.  The caller therefore hands
     back the authority itself -- which is exactly what [astate_elim] gives
     it, at [γtop (fs_gamma_L γfs)] = [fs_top γfs] ([ftop_gamma_top], and it
     is [reflexivity], so the two spellings are interchangeable with no
     rewrite. *)
  Lemma ftop_astate_acc (γfs : fs_names) :
    ftop_body γfs -∗
      ∃ av, astate (fs_gamma_L γfs) av
          ∗ (∀ I' : gmap Z fs_node,
               ⌜forall i n, I' !! i = Some n -> inode_local i n⌝ -∗
               ghost_map_auth (fs_top γfs) 1 I' -∗ ftop_body γfs).
  Proof.
    iIntros "Hb". rewrite /ftop_body.
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iExists (abs_view I).
    iSplitL "Hta".
    { iApply astate_intro. iExact "Hta". }
    iIntros (I' Hloc) "Hta".
    iExists I', A. iFrame "Hta Hla Hpark". iPureIntro.
    intros i n Hi _. exact (Hloc i n Hi).
  Qed.

  (* THE READ-ONLY BORROW: the caller that only LOOKS at the map (a spec
     whose atomic step is an observation) hands the SAME authority back and
     owes no row at all -- [ftop_clean] is the one the body came with. *)
  Lemma ftop_astate_ro (γfs : fs_names) :
    ftop_body γfs -∗
      ∃ I : gmap Z fs_node,
        astate (fs_gamma_L γfs) (abs_view I)
        ∗ (ghost_map_auth (fs_top γfs) 1 I -∗ ftop_body γfs).
  Proof.
    iIntros "Hb". rewrite /ftop_body.
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iExists I. iSplitL "Hta".
    { iApply astate_intro. iExact "Hta". }
    iIntros "Hta". iExists I, A. by iFrame.
  Qed.

End FsAbsFtop.
