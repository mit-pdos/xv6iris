(* FsAbs.v -- THE SPEC LAYER'S ABSTRACT STATE, AND IT IS A READING.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 1-3
   (v3), lane A items (i) and (ii) of claude-notes/projects/fs-syscall-specs.md.

   PURE LAYER: sections 1-2 and [abs_view] are in FsAbsDefs.v since
   2026-09-04 (Exported from here; see the note above the Require).

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
                discipline itself: every retag ([InodeRegion.ireg_top_retag_*])
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
         That is the same obligation [InodeRegion.ireg_top_retag_*] already
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
   answer AS [apath_at], with no divergence arm and no possible miss.

   ===== READ THE NEXT THREE PARAGRAPHS AS HISTORY (2026-08-30) ==========
   They record how this file's abstracted lend [F] was aimed at the landed
   ghost-trace hop and what the attempt found.  THE DVIEW RETIREMENT deleted
   both the hop ([SpecNameiTr.nx_hop]) and the ghost it lent
   ([DirViewG.dv_half]); the consumed form is [FsAbsEra.ex_hop] = [ax_hop] at
   [FsAbsEra.elend], the era fragment, which discharges the STRONG law
   ([lend_agrees]) that [dv_half] could not.  Everything this file proves is
   stated at the abstracted [F] and did not move.
   ======================================================================

   The walk's hop ([SpecNameiTr.nx_hop]) is [ax_hop] at the lent fragment
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

   ...AND WHAT THE SEAM ATTEMPT FOUND (lane A (iii), [FsAbsSeam.v]).  The tie
   is REAL and it is one landed pure lemma
   ([FsStateEra.dir_entries_era_node]: [dir_entries (era_node dn bm data)] IS
   [dv_of dn data] at a directory), but it lives BESIDE the two ghosts INSIDE
   the payload -- and the payload is in the WALK's hand at the fire instant.
   Two consequences, both machine-checked in [FsAbsSeam.v]:

     (1) [lend_agrees Gamma dv_half] is not merely unproven here, it is the
         WRONG law: no arm can prove the pinned node is a DIRECTORY, since
         [dv_half] rides a file too ("of a file the value is determined
         garbage", DirViewG's header).  [lend_reads] below is the law a
         payload discharges, and section 4a' re-proves the whole package at
         it ([apn_hop_rd] .. [apn_walk_rd]).
     (2) A CLIENT CANNOT HOLD [nview] AT ALL TODAY.  [IcacheEscrow.ic_loaded]
         and [IcacheEscrow.ipool_alloc] carry [FsState.top_frag] at
         [DfracOwn 1], so an [apn_pin] against a live inum is REFUTED
         ([FsAbsSeam.ic_loaded_nview_excl], [FsAbsSeam.apn_pin_loaded_excl];
         [top_frag_1_nview_excl] below is the ghost half of it).  The one arm
         that sheds is the READ arm ([ic_rd_arm], at 3/4) -- and there
         [lend_reads] IS discharged ([FsAbsSeam.dv_lend_arm_reads]), so the
         package instantiates at a real top_frag-agreeing lend
         ([FsAbsSeam.apn_walk_arm]).  What namei lends at its fire is
         [dv_half] ALONE, without that arm; closing the seam therefore needs
         a producer of a client-held [top_frag_q] share that survives a
         WRITE-arm checkout, which is a payload change and not a spec-layer
         one.

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
Require Import FsTree.         (* [fname], [fsnode], [path_at], [node_of]    *)
Require Import Xv6Cameras.     (* [fsTopG]/[fsLinkG] -- IMPORTED (see header) *)
Require Export FsState.        (* Export's FsStateInode: the readings        *)

(* THE PURE LAYER IS HOISTED (2026-09-04).  Sections 1-2 -- [absnode] /
   [anode] / [aview], [abs_of] and its readings, the [FsTree] bridge,
   [apath_at] and [arun] -- and section 3a's [abs_view] live in
   FsAbsDefs.v and are EXPORTED here, so every [Require Import FsAbs]
   still resolves every one of those names to the same constant.  The
   hoist exists so that files below [ProcInv] (FsAbsInv, FsAbsDelta) can
   name [aview]/[abs_view] without this file's ghost cone. *)
Require Export FsAbsDefs.

Local Open Scope Z_scope.

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

  (* THE WHOLE ELEMENT ADMITS NO CLIENT SHARE, and this is the law lane A's
     seam runs into: every arm of the fs payload -- [IcacheEscrow.ic_loaded],
     [IcacheEscrow.ipool_alloc] -- carries [FsState.top_frag] at [DfracOwn 1],
     so a client holding ANY [nview] share of that inum is refuted outright
     ([FsAbsSeam.ic_loaded_nview_excl] is this lemma, one payload down).  The
     read arm ([ic_rd_arm], at 3/4) is the one place a share is legitimately
     outstanding. *)
  Lemma top_frag_1_nview_excl Γ i n q a :
    top_frag_q Γ (DfracOwn 1) i n -∗ nview Γ q i a -∗ False.
  Proof.
    rewrite /nview /nview_dq /top_frag_q. iIntros "H1 H2".
    iDestruct "H2" as (n2) "[H2 _]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. rewrite dfrac_op_own in Hv. apply dfrac_valid_own in Hv.
    exact (Qp.not_add_le_l 1%Qp q Hv).
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

  (* The pure conjunct goes LAST (durable-notes) even in a new definition:
     every consumer destructures the authority first.

     AT A FRACTION (app-instances.md round A).  The running authority is
     SPLIT between the kernel ([InodeRegion.ftop_body], the half every AU
     commit shape lends) and the application ([AppInv.app_inv]); the
     durable one ([FsDurSnap.fs_snap]) is whole.  [astate_q] names the
     fraction; [astate] -- the READING every pin and every hop is stated
     over -- is at SOME fraction, so it is introduced from whichever the
     reader holds and eliminated only up to that fraction.  Reads
     (agreement) work at any fraction, which is all a reading needs. *)
  Definition astate_q Γ (q : Qp) (av : aview) : iProp Σ :=
    (∃ I, ghost_map_auth (γtop Γ) q I ∗ ⌜av = abs_view I⌝)%I.

  Definition astate Γ (av : aview) : iProp Σ := (∃ q : Qp, astate_q Γ q av)%I.

  Global Instance astate_q_timeless Γ q av : Timeless (astate_q Γ q av).
  Proof. rewrite /astate_q. apply _. Qed.

  Global Instance astate_timeless Γ av : Timeless (astate Γ av).
  Proof. rewrite /astate. apply _. Qed.

  (* INTRO AND ELIM AGAINST THE AUTHORITY.  This is all that is left of the
     old [fs_view_astate] equivalence once the authority moved into
     [InodeRegion.ftop_inv]: [astate] is a READING of [ghost_map_auth], so
     both directions are the definition.  The borrow off [ftop_body] itself
     is [ftop_astate_acc] (section 5). *)
  Lemma astate_q_intro Γ (q : Qp) I :
    ghost_map_auth (γtop Γ) q I ⊢ astate_q Γ q (abs_view I).
  Proof. iIntros "Ha". iExists I. by iFrame. Qed.

  Lemma astate_q_elim Γ (q : Qp) av :
    astate_q Γ q av ⊢ ∃ I, ghost_map_auth (γtop Γ) q I ∗ ⌜av = abs_view I⌝.
  Proof. by iIntros "H". Qed.

  Lemma astate_of_q Γ (q : Qp) av : astate_q Γ q av ⊢ astate Γ av.
  Proof. iIntros "H". iExists q. iExact "H". Qed.

  Lemma astate_intro Γ (q : Qp) I :
    ghost_map_auth (γtop Γ) q I ⊢ astate Γ (abs_view I).
  Proof. iIntros "Ha". iApply astate_of_q. iApply astate_q_intro. iExact "Ha". Qed.

  Lemma astate_elim Γ av :
    astate Γ av ⊢ ∃ (q : Qp) I, ghost_map_auth (γtop Γ) q I ∗ ⌜av = abs_view I⌝.
  Proof. iIntros "H". iDestruct "H" as (q) "H". iExists q. iExact "H". Qed.

  (* A HELD FRAGMENT AGREES WITH THE AUTHORITY'S ROW. *)
  Lemma astate_q_nview_dq Γ (q : Qp) av dq i a :
    astate_q Γ q av -∗ nview_dq Γ dq i a -∗ ⌜av !! i = Some a⌝.
  Proof.
    rewrite /astate_q /nview_dq /top_frag_q.
    iIntros "Hst Hn". iDestruct "Hst" as (I) "(Ha & %Hav)".
    iDestruct "Hn" as (n) "[Hf %Han]".
    iDestruct (ghost_map_lookup with "Ha Hf") as %Hl.
    iPureIntro. subst av. by rewrite (abs_view_lookup I i n Hl) Han.
  Qed.

  Lemma astate_nview_dq Γ av dq i a :
    astate Γ av -∗ nview_dq Γ dq i a -∗ ⌜av !! i = Some a⌝.
  Proof.
    iIntros "Hst Hn". iDestruct "Hst" as (q) "Hst".
    iApply (astate_q_nview_dq with "Hst Hn").
  Qed.

  Lemma astate_q_nview Γ (q' : Qp) av q i a :
    astate_q Γ q' av -∗ nview Γ q i a -∗ ⌜av !! i = Some a⌝.
  Proof. apply astate_q_nview_dq. Qed.

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

  (* ...AND THE WEAKER LAW A PAYLOAD CAN ACTUALLY DISCHARGE.  [lend_agrees]
     asks the lend to prove the pinned node IS a directory; no payload arm
     can, because [dv_half] is carried at a FILE too ("of a file the value is
     determined garbage", DirViewG's header) and the abstract node's arm is
     the one thing the entry map does not say.  [lend_reads] asks only what
     the chain lemma actually consumes -- IF the pinned node reads as a
     directory THEN its entry map is the lent one -- and the walk supplies
     the directory-ness itself, out of [arun].  Everything below is proven
     at this weaker hypothesis ([apn_hop_rd] ... [apn_walk_rd]); the
     [lend_agrees] forms are kept verbatim (R10) and are the special case
     ([lend_agrees_reads]). *)
  Definition lend_reads Γ (F : Z -> dfrac -> gmap fname Z -> iProp Σ) : Prop :=
    forall (d : Z) (dq : dfrac) (ents : gmap fname Z) (q : Qp) (a : anode)
           (e : gmap fname Z),
      ⊢ F d dq ents -∗ nview Γ q d a -∗ ⌜an_node a = ADir e -> e = ents⌝.

  Lemma lend_agrees_reads Γ F : lend_agrees Γ F -> lend_reads Γ F.
  Proof.
    intros Hag d dq ents q a e. iIntros "HF Hn".
    iDestruct (Hag d dq ents q a with "HF Hn") as %Ha.
    iPureIntro. intros He. rewrite Ha in He. by simplify_eq.
  Qed.

  Lemma alend_reads Γ : lend_reads Γ (alend Γ).
  Proof. apply lend_agrees_reads, alend_agrees. Qed.

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
  (*  4a'.  THE SAME THREE, AT [lend_reads]                               *)
  (*                                                                      *)
  (*  The directory-ness the [lend_agrees] forms took from the LEND comes  *)
  (*  from the RUN instead: [arun]'s step at hop [k] is an [astep], which  *)
  (*  is a [bind] through [anode_ents], so it cannot be [Some] unless the  *)
  (*  pinned node's arm is [ADir].  That is the whole difference; the      *)
  (*  three proofs are otherwise their neighbours' above, line for line.   *)
  (* ------------------------------------------------------------------ *)

  Lemma apn_hop_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (k : nat) (s : fname) :
    lend_reads Γ F ->
    arun av root ps ds ->
    ps !! k = Some s ->
    ⊢ ax_hop F (apn_P Γ q av ds ps) apn_Pmiss k s.
  Proof.
    intros Hrd Hr Hk. rewrite /ax_hop {2}/apn_P.
    iIntros (d ents dqv) "[%Hd Hpins] HF". subst d.
    rewrite {1}/apn_pins (drop_S _ _ _ Hk) big_sepL_cons Nat.add_0_r.
    iDestruct "Hpins" as "[Hpin Htl]".
    iDestruct "Hpin" as (a) "[%Hav Hn]".
    pose proof (arun_step_tot av root ps ds k s Hr Hk) as Hst.
    rewrite /astep /aents Hav /= /anode_ents in Hst.
    destruct (an_node a) as [bs | e | mj mi] eqn:Hna;
      [discriminate Hst | | discriminate Hst].
    simpl in Hst.
    iDestruct (Hrd (ds !!! k) dqv ents q a e with "HF Hn") as %Hee.
    rewrite (Hee Hna) in Hst.
    rewrite Hst. iModIntro. iFrame "HF".
    rewrite /apn_P /apn_pins. iSplitR; [by iPureIntro |].
    iApply (big_sepL_mono with "Htl").
    intros jj y _. by rewrite Nat.add_succ_r Nat.add_succ_l.
  Qed.

  Lemma apn_hops_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (n : nat) :
    lend_reads Γ F ->
    arun av root ps ds ->
    ⊢ ax_hops_from F (apn_P Γ q av ds ps) apn_Pmiss ps n.
  Proof.
    intros Hrd Hr. rewrite /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    by iApply (apn_hop_rd Γ q av F root ps ds (n + j)%nat s).
  Qed.

  Lemma apn_walk_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) :
    lend_reads Γ F ->
    arun av root ps ds ->
    apn_pins Γ q av ds ps 0%nat -∗
      apn_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from F (apn_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apn_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝).
  Proof.
    intros Hrd Hr. iIntros "Hp".
    iDestruct (apn_P_start Γ q av root ps ds Hr with "Hp") as "HP".
    iFrame "HP". iSplitR.
    - by iApply (apn_hops_rd Γ q av F root ps ds 0%nat).
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
(*  4a''.  THE PIN-RETURNING WALK: THE SAME PACKAGE, SHARES HANDED BACK   *)
(* ===================================================================== *)

(* WAS iris/FsAbsPins.v, FUSED IN 2026-08-30 (the FsAbs* leaf fuse).  It was
   a separate leaf for one mechanical reason -- the build mirror's rule that
   a tracked file is not touched -- and its own header said to fuse it "the
   next time [FsAbs.v] is legitimately edited".  Nothing moved: what follows
   is that file's [Section FsAbsPins] verbatim, at the [FsAbsWalk] binder
   list it already copied; [FsAbsPins.v] survives as a stub that
   [Require Export]s this file.

   Owner ruling relayed 2026-08-28: "a client's nview share used for hop
   agreement must come back, not be spent into the accumulator".

   WHAT CHANGES, AND IT IS ONE IDEA.  [apn_P Gamma q av ds ps k d] is
   [<<d = ds !!! k>>] beside the pins the walk has NOT yet spent
   ([apn_pins .. k], the big-op over [drop k ps]).  Each hop peels the head
   pin, uses it for agreement, and DROPS it: after [L] hops the client's
   [nview] shares are gone.  But agreement is NON-DESTRUCTIVE -- the hop
   reads the entry map off the lent fragment against the share and consumes
   nothing -- so the shrinking accumulator was an artifact of the shape, not
   of the logic.

   [apr_pins] is therefore the WHOLE list, carried unchanged through every
   hop, and the hop takes the k-th pin out with [big_sepL_lookup_acc], reads
   it, and puts it straight back.  Three consequences, and they are the
   point:

     - AT THE END the client gets every share back beside the answer
       ([apr_P_final] returns [apr_pins] alongside [apath_at]).
     - AT A DEATH INDEX likewise: the trace contract's failure arm hands
       [P k d] back, and here that IS the whole bundle ([apr_P_pins]).
     - THE ACCUMULATOR NEVER CHANGES SHAPE, so the index bookkeeping that
       [apn_hop] spends four lines on ([Nat.add_succ_r] under a
       [big_sepL_mono]) disappears.

   The section-4/4a' spending forms are NOT touched and are not deprecated;
   [apr_pins_is_apn_pins] is a [reflexivity] receipt that the returning
   accumulator IS the landed one at hop 0, so a consumer can move between
   them with no proof.

   THE MISS ARM IS STILL [False] ([apn_Pmiss]): a miss on a pinned chain is
   impossible, so there is nothing there to return.  The pins that matter on
   a short walk come back through the LEFT disjunct of the contract's
   failure arm, which carries [P k d] itself. *)

Section FsAbsPins.
  Context `{!invGS_gen hlc Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ===================================================================== *)
  (*  1.  THE RETURNING ACCUMULATOR                                         *)
  (* ===================================================================== *)

  (* ONE PIN PER HOP, and the final inum is deliberately NOT pinned: the
     walk's answer need not be a directory, and a client that wants it
     pinned holds that share itself. *)
  Definition apr_pins Γ (q : Qp) (av : aview) (ds : list Z)
      (ps : list fname) : iProp Σ :=
    ([∗ list] j ↦ _ ∈ ps, apn_pin Γ q av (ds !!! j))%I.

  Definition apr_P Γ (q : Qp) (av : aview) (ds : list Z) (ps : list fname)
      (k : nat) (d : Z) : iProp Σ :=
    (⌜d = ds !!! k⌝ ∗ apr_pins Γ q av ds ps)%I.

  (* THE RECEIPT that nothing was invented: at hop 0 the returning
     accumulator IS [FsAbs.apn_pins] ([drop 0 ps] is [ps] and [0 + j] is
     [j], both by computation). *)
  Lemma apr_pins_is_apn_pins Γ (q : Qp) (av : aview) (ds : list Z)
      (ps : list fname) :
    apr_pins Γ q av ds ps = apn_pins Γ q av ds ps 0%nat.
  Proof. reflexivity. Qed.

  (* ...AND THE RULING ITSELF, as a one-line lemma: whatever index the walk
     dies at, the cursor it hands back IS the client's whole bundle. *)
  Lemma apr_P_pins Γ (q : Qp) (av : aview) (ds : list Z) (ps : list fname)
      (k : nat) (d : Z) :
    apr_P Γ q av ds ps k d -∗ apr_pins Γ q av ds ps ∗ ⌜d = ds !!! k⌝.
  Proof. rewrite /apr_P. iIntros "[%Hd $]". by iPureIntro. Qed.

  Lemma apr_P_intro Γ (q : Qp) (av : aview) (ds : list Z) (ps : list fname)
      (k : nat) :
    apr_pins Γ q av ds ps -∗ apr_P Γ q av ds ps k (ds !!! k).
  Proof. iIntros "H". rewrite /apr_P. by iFrame. Qed.

  (* ===================================================================== *)
  (*  2.  THE HOP, READ OFF A PIN AND PUT STRAIGHT BACK                     *)
  (* ===================================================================== *)

  (* [FsAbs.apn_hop_rd]'s proof with [big_sepL_lookup_acc] in place of the
     [drop_S] peel: the directory-ness still comes from [arun] (an [astep]
     is a bind through [anode_ents], so it cannot answer unless the pinned
     node's arm is [ADir]), the lend still supplies the entry map, and the
     accessor's wand returns the share. *)
  Lemma apr_hop_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (k : nat) (s : fname) :
    lend_reads Γ F ->
    arun av root ps ds ->
    ps !! k = Some s ->
    ⊢ ax_hop F (apr_P Γ q av ds ps) apn_Pmiss k s.
  Proof.
    intros Hrd Hr Hk. rewrite /ax_hop {2}/apr_P.
    iIntros (d ents dqv) "[%Hd Hpins] HF". subst d.
    rewrite {1}/apr_pins.
    iDestruct (big_sepL_lookup_acc _ ps k s Hk with "Hpins")
      as "[Hpin Hback]".
    iDestruct "Hpin" as (a) "[%Hav Hn]".
    pose proof (arun_step_tot av root ps ds k s Hr Hk) as Hst.
    rewrite /astep /aents Hav /= /anode_ents in Hst.
    destruct (an_node a) as [bs | e | mj mi] eqn:Hna;
      [discriminate Hst | | discriminate Hst].
    simpl in Hst.
    iDestruct (Hrd (ds !!! k) dqv ents q a e with "HF Hn") as %Hee.
    rewrite (Hee Hna) in Hst.
    rewrite Hst. iModIntro. iFrame "HF".
    rewrite /apr_P /apr_pins. iSplitR; [by iPureIntro |].
    iApply "Hback". rewrite /apn_pin. iExists a. by iFrame.
  Qed.

  Lemma apr_hop Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (k : nat) (s : fname) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    ps !! k = Some s ->
    ⊢ ax_hop F (apr_P Γ q av ds ps) apn_Pmiss k s.
  Proof.
    intros Hag. apply (apr_hop_rd Γ q av F root ps ds k s
                         (lend_agrees_reads Γ F Hag)).
  Qed.

  Lemma apr_hops_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (n : nat) :
    lend_reads Γ F ->
    arun av root ps ds ->
    ⊢ ax_hops_from F (apr_P Γ q av ds ps) apn_Pmiss ps n.
  Proof.
    intros Hrd Hr. rewrite /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    by iApply (apr_hop_rd Γ q av F root ps ds (n + j)%nat s).
  Qed.

  Lemma apr_hops Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) (n : nat) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    ⊢ ax_hops_from F (apr_P Γ q av ds ps) apn_Pmiss ps n.
  Proof.
    intros Hag. apply (apr_hops_rd Γ q av F root ps ds n
                         (lend_agrees_reads Γ F Hag)).
  Qed.

  (* ===================================================================== *)
  (*  3.  START, FINISH, AND THE PACKAGE                                    *)
  (* ===================================================================== *)

  Lemma apr_P_start Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) :
    arun av root ps ds ->
    apr_pins Γ q av ds ps -∗ apr_P Γ q av ds ps 0%nat root.
  Proof.
    intros Hr. iIntros "Hp". rewrite /apr_P. iSplitR; [| iFrame "Hp"].
    iPureIntro. symmetry. exact (arun_head _ _ _ _ Hr).
  Qed.

  (* THE DIFFERENCE FROM [FsAbs.apn_P_final], and the whole ruling: the
     answer comes back WITH the shares, not instead of them. *)
  Lemma apr_P_final Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) (iL : Z) :
    arun av root ps ds ->
    apr_P Γ q av ds ps (length ps) iL -∗
      ⌜apath_at av root ps = Some iL⌝ ∗ apr_pins Γ q av ds ps.
  Proof.
    intros Hr. rewrite /apr_P. iIntros "[%Hd $]". iPureIntro.
    rewrite (arun_apath_tot _ _ _ _ Hr). by rewrite Hd.
  Qed.

  (* THE PACKAGE a caller of an [ax_hop]-shaped trace contract
     instantiates.  Three components, as in [FsAbs.apn_walk]: the cursor at
     the root, the hop family, and the reading at the end -- the third one
     RETURNING. *)
  Lemma apr_walk_rd Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) :
    lend_reads Γ F ->
    arun av root ps ds ->
    apr_pins Γ q av ds ps -∗
      apr_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from F (apr_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apr_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝
                     ∗ apr_pins Γ q av ds ps).
  Proof.
    intros Hrd Hr. iIntros "Hp".
    iDestruct (apr_P_start Γ q av root ps ds Hr with "Hp") as "HP".
    iFrame "HP". iSplitR.
    - by iApply (apr_hops_rd Γ q av F root ps ds 0%nat).
    - iIntros (iL) "HP". by iApply (apr_P_final Γ q av root ps ds iL Hr).
  Qed.

  Lemma apr_walk Γ (q : Qp) (av : aview)
      (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (root : Z) (ps : list fname) (ds : list Z) :
    lend_agrees Γ F ->
    arun av root ps ds ->
    apr_pins Γ q av ds ps -∗
      apr_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from F (apr_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apr_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝
                     ∗ apr_pins Γ q av ds ps).
  Proof.
    intros Hag. apply (apr_walk_rd Γ q av F root ps ds
                         (lend_agrees_reads Γ F Hag)).
  Qed.

  (* ===================================================================== *)
  (*  4.  BUILDING THE BUNDLE                                               *)
  (* ===================================================================== *)

  Lemma apr_pins_of_views Γ (q : Qp) (av : aview) (ds : list Z)
      (ps : list fname) :
    astate Γ av -∗
    ([∗ list] j ↦ _ ∈ ps, ∃ a, nview Γ q (ds !!! j) a) -∗
      astate Γ av ∗ apr_pins Γ q av ds ps.
  Proof.
    iIntros "Hst Hl". rewrite /apr_pins.
    by iApply (big_sepL_apn_pin Γ q av ps (fun j => ds !!! j) with "Hst Hl").
  Qed.

End FsAbsPins.

(* the same seal [FsAbs] puts on [apn_pins], and for the same measured
   reason: it is a big-op behind a [Definition] and an [iFrame] near it
   would resolve instances through the whole list (durable-notes). *)
Global Typeclasses Opaque apr_pins.

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
     pay for it; the mover re-establishes [inode_local] anyway ([ireg_top_retag_*]
     charges exactly this, and [FsStateEra.inode_local_of_ok_rec] is the one
     line that assembles it).  The obligation is stated at the STRONGER,
     A-free form -- every entry local -- which implies [ftop_clean I' A] for
     the [A] the body happens to carry, so the caller never has to see the
     arming registry.  A caller that suspends the row instead ([ireg_arm])
     is not this accessor's customer: it moves the map through
     [ireg_top_retag_armed_*] and never opens [ftopN] itself.

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
      ∃ av, astate_q (fs_gamma_L γfs) (1/2) av
          ∗ (∀ I' : gmap Z fs_node,
               ⌜forall i n, I' !! i = Some n -> inode_local i n⌝ -∗
               ghost_map_auth (fs_top γfs) (1/2) I' -∗ ftop_body γfs).
  Proof.
    iIntros "Hb". rewrite /ftop_body.
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iExists (abs_view I).
    iSplitL "Hta".
    { iApply astate_q_intro. iExact "Hta". }
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
        astate_q (fs_gamma_L γfs) (1/2) (abs_view I)
        ∗ (ghost_map_auth (fs_top γfs) (1/2) I -∗ ftop_body γfs).
  Proof.
    iIntros "Hb". rewrite /ftop_body.
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iExists I. iSplitL "Hta".
    { iApply astate_q_intro. iExact "Hta". }
    iIntros "Hta". iExists I, A. by iFrame.
  Qed.

End FsAbsFtop.
