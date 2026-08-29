(* FsAbsPins.v -- THE PIN-RETURNING PINNED WALK: [FsAbs] section 4a's
   package with the client's carriers HANDED BACK instead of spent.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii)
   (the era-fragment walk); owner ruling relayed 2026-08-28, "a client's
   nview share used for hop agreement must come back, not be spent into the
   accumulator".

   WHY THIS FILE EXISTS AND WHY IT IS NOT AN APPEND TO [FsAbs.v].  The
   package this restates is [FsAbs]'s and belongs beside it (it is section
   4a'' in every sense but the file boundary).  It is a separate leaf for
   ONE mechanical reason: this campaign's builds run on the EC2 mirror,
   whose rule is that no TRACKED file there is touched, and [FsAbs.v] is
   tracked.  A new leaf that [Require]s [FsAbs] is byte-for-byte
   append-only from [FsAbs]'s point of view -- nothing of section 4a moves,
   [Typeclasses Opaque apn_pins] still governs the landed form -- and the
   two files can be fused the next time [FsAbs.v] is legitimately edited.

   WHAT CHANGES, AND IT IS ONE IDEA.  [FsAbs.apn_P Γ q av ds ps k d] is
   [⌜d = ds !!! k⌝] beside the pins the walk has NOT yet spent
   ([apn_pins .. k], the big-op over [drop k ps]).  Each hop peels the head
   pin, uses it for agreement, and DROPS it: after [L] hops the client's
   [nview] shares are gone.  But agreement is NON-DESTRUCTIVE -- the hop
   reads [⌜ents = dir_entries n⌝] off the lent fragment against the share
   and consumes nothing -- so the shrinking accumulator was an artifact of
   the shape, not of the logic.

   [apr_pins] is therefore the WHOLE list, carried unchanged through every
   hop:

       apr_pins Γ q av ds ps := [∗ list] j ↦ _ ∈ ps, apn_pin Γ q av (ds !!! j)
       apr_P    Γ q av ds ps k d := ⌜d = ds !!! k⌝ ∗ apr_pins Γ q av ds ps

   and the hop takes the k-th pin out with [big_sepL_lookup_acc], reads it,
   and puts it straight back.  Three consequences, and they are the point:

     - AT THE END the client gets every share back beside the answer
       ([apr_P_final] returns [apr_pins] alongside [apath_at]).
     - AT A DEATH INDEX likewise: the trace contract's failure arm hands
       [P k d] back, and here that IS the whole bundle ([apr_P_pins]).
     - THE ACCUMULATOR NEVER CHANGES SHAPE, so the index bookkeeping that
       [FsAbs.apn_hop] spends four lines on ([Nat.add_succ_r] under a
       [big_sepL_mono]) disappears.

   The landed spending forms are NOT touched and are not deprecated here;
   [apr_pins_is_apn_pins] is a [reflexivity] receipt that the returning
   accumulator IS the landed one at hop 0, so a consumer can move between
   them with no proof.

   THE MISS ARM IS STILL [False] ([FsAbs.apn_Pmiss]): a miss on a pinned
   chain is impossible, so there is nothing there to return.  The pins that
   matter on a short walk come back through the LEFT disjunct of the
   contract's failure arm, which carries [P k d] itself.

   BINDERS: [FsAbs]'s own [FsAbsWalk] list, verbatim. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map fancy_updates.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import Xv6Cameras.
Require Import FsAbs.

Local Open Scope Z_scope.

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
