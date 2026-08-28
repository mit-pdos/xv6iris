(* FsAbsEra.v -- THE ERA-FRAGMENT LEND: what lane A-iii's option (b) walk
   fires at each hop, and the three laws that make it worth firing.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   the user's 2026-08-28 ruling ("OPTION (b): the campaign builds the
   era-fragment walk").  Design of record: claude-notes/design/
   fs-syscall-specs.md v3, sections 2-3.

   WHY A SECOND LEND EXISTS AT ALL.  [FsAbsSeam] settled item (iii)'s three
   findings: the dv<->top tie is real and pure ([dv_of_dir_entries]), the
   law a payload can discharge is [FsAbs.lend_reads] and not
   [lend_agrees] -- and the landed fire ([SpecNameiTr.nx_hop], which R10
   freezes) passes only [DirViewG.dv_half] through the caller's fupd, so a
   client-side hop learns NOTHING about gamma-top.  The fix the owner ruled
   is not a payload change but a SECOND WALK: same 334 bytes of namex, same
   contract shape, one different resource crossing the caller's [={T}=*].
   This file is that resource, stated once, so the walk's proof
   ([ProofNamexEra]) and its consumers ([SpecSysMknodAU]'s prover) share a
   vocabulary instead of each unfolding a ghost.

   THE SHAPE, AND WHY IT IS THIS ONE.  [elend Gamma d dq ents] is the era
   fragment at [d] TOGETHER WITH the two pure facts that make it readable:

       exists n, top_frag_q Gamma dq d n
                 /\ fn_is_dir n = true /\ dir_entries n = ents.

   Three deliberate choices.

     (1) THE NODE IS EXISTENTIAL, because [FsAbs.ax_hop]'s [F] has the
         signature [Z -> dfrac -> gmap fname Z -> iProp], fixed by the
         frozen trace vocabulary.  Nothing is lost: the walk lends HALF its
         element and keeps the other half, so [top_frag_q_agree] pins the
         returned node to the lent one ([elend_fire_hit] below).  That is
         the whole reason the fire splits rather than lending [DfracOwn 1]:
         at the whole share the caller could hand back a DIFFERENT node
         with the same entry map, and the walk could not re-pack its
         [ic_loaded].

     (2) DIRECTORY-NESS IS CARRIED, not left to the caller.  [dv_half]
         could not carry it ("of a file the value is determined garbage",
         DirViewG's header) and that is exactly why [FsAbsSeam] had to fall
         back on the weaker [lend_reads].  The era fragment CAN: the walk
         has already tested [ip->type == T_DIR] before it calls dirlookup,
         so the fact is free at the fire.  Consequence: this lend
         discharges the STRONGER law ([elend_agrees] : [lend_agrees]) and
         [lend_reads] comes off it by [FsAbs.lend_agrees_reads].  Both the
         section-4 package ([apn_walk]) and the section-4a' one
         ([apn_walk_rd]) therefore instantiate here.

     (3) THE ENTRY MAP IS [dir_entries n], NOT [dv_of dn data].  Those are
         one function on a payload node ([FsAbsSeam.dv_of_dir_entries]) and
         [elend_of_era] is that bridge; but the CLIENT-facing side of the
         lend must speak the abstract state's own reading, or
         [FsAbs.astate] cannot be read against it.  [elend_astate] is what
         that buys: inside the hop's fupd a consumer opens ftopN, takes
         [FsAbs.ftop_astate_ro], and reads the parent's row out of [av]
         AS [ADir ents].  That -- not the pinned walk -- is the
         non-vacuous consumption route today, see the note below.

   WHAT THE PINNED WALK DOES AND DOES NOT GIVE (recorded so the next lane
   does not re-discover it).  [apn_walk_era] is [FsAbs.apn_walk] at
   [F := elend], a theorem.  But the walk holds the WHOLE element at the
   fire (it keeps 1/2 and lends 1/2), so a client holding any [nview] share
   of a directory ON the chain is still refuted -- [FsAbsSeam]'s finding 3
   is about the payload's custody and a new walk does not change it.  The
   package is therefore instantiable but VACUOUS for a live inum, exactly
   as [FsAbsSeam.apn_walk_arm] is non-vacuous only under a read lock.  What
   the era walk really delivers over the dv walk is [elend_astate]: the hop
   reads the AUTHORITY's row, which needs no client-held share at all.  A
   non-vacuous pin waits for the tree layer's exclusivity fact (the ruling's
   own words), not for another walk.

   AND THE PINS COME BACK (owner ruling, relayed 2026-08-28).  Agreement is
   non-destructive, so the shrinking accumulator of [FsAbs.apn_P] was a
   shape and not a necessity.  [FsAbsPins] restates the package with the
   client's whole bundle carried through every hop and handed back at the
   end -- and at any death index too, since the contract's failure arm
   returns [P k d] itself.  [apr_walk_era] below is that package at this
   lend, and it is the form a consumer should instantiate;
   [apn_walk_era] is kept beside it only because [FsAbs]'s own statements
   are frozen and a reader will look for the landed shape first.

   BINDERS.  [FsAbsSeam]'s, minus the two slot classes it needed for
   [ic_rd_arm]: the BUNDLE [xv6G] and never a member (durable-notes, "ONE
   BUNDLE PER GHOST CLASS").  [FsAbs] is REQUIRED LAST for the same reason
   it is there -- its [Require Export FsState] must win on the [FsState*]
   stack's shadowed names. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.      (* [riscvGS]                                  *)
Require Import DinodeEnc.       (* [dinode], [di_type]                        *)
Require Import DirView.         (* [T_DIR_z]                                  *)
Require Import FsTree.          (* [fname]                                    *)
Require Import PathElems.       (* [path_elems]: the hop family's index       *)
Require Import BioDefs.
Require Import InodeInv.        (* [blkmap]                                   *)
Require Import InodeLock.       (* [inode_ok]                                 *)
Require Import IrefSlots.
Require Import FsBlocks.        (* [fs_names]                                 *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the LIVE Gamma               *)
Require Import FsStateEra.      (* [era_node], [era_node_rec]                 *)
Require Import IcacheRef.
Require Import DirViewLend.
Require Import IcacheEscrow.    (* Require Export's DirViewG: [dv_of]         *)
Require Import Xv6G.            (* the bundle                                 *)
Require Import FsAbsSeam.       (* [dv_of_dir_entries]: the pure bridge       *)
Require Import FsAbsPins.       (* the PIN-RETURNING package (owner ruling)   *)
Require Import FsAbs.           (* LAST: [nview], [ax_hop], [lend_agrees]     *)

Local Open Scope Z_scope.

Section FsAbsEra.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE LEND                                                        *)
  (* =================================================================== *)

  (* The pure conjuncts go LAST and TOGETHER (durable-notes): every
     consumer takes the fragment first and the two facts as one [%]. *)
  Definition elend Γ (d : Z) (dq : dfrac) (ents : gmap fname Z) : iProp Σ :=
    (∃ n : fs_node,
       top_frag_q Γ dq d n ∗ ⌜fn_is_dir n = true /\ dir_entries n = ents⌝)%I.

  Global Instance elend_timeless Γ d dq ents : Timeless (elend Γ d dq ents).
  Proof. rewrite /elend. apply _. Qed.

  Lemma elend_frag Γ d dq ents : elend Γ d dq ents ⊢ ∃ n, top_frag_q Γ dq d n.
  Proof. iIntros "H". iDestruct "H" as (n) "[H _]". by iExists n. Qed.

  Lemma elend_intro Γ d dq (n : fs_node) :
    fn_is_dir n = true ->
    top_frag_q Γ dq d n ⊢ elend Γ d dq (dir_entries n).
  Proof. intros Hd. iIntros "H". iExists n. by iFrame. Qed.

  (* =================================================================== *)
  (*  2.  THE THREE LAWS                                                  *)
  (* =================================================================== *)

  (* THE STRONG ONE, and it is available here precisely because the era
     fragment carries the node's TYPE while [dv_half] cannot
     ([FsAbsSeam], finding 2). *)
  Lemma elend_agrees Γ : lend_agrees Γ (elend Γ).
  Proof.
    intros d dq ents q a. rewrite /elend. iIntros "HF Hn".
    iDestruct "HF" as (n) "[Hf [%Hdir %Hde]]".
    iDestruct (nview_frag with "Hn") as (n') "[Hf' %Han]".
    iDestruct (top_frag_q_agree with "Hf Hf'") as %<-.
    iPureIntro. by rewrite -Han (abs_of_dir n Hdir) Hde.
  Qed.

  Lemma elend_reads Γ : lend_reads Γ (elend Γ).
  Proof. apply lend_agrees_reads, elend_agrees. Qed.

  (* THE READING AGAINST THE AUTHORITY -- the law the era walk exists for.
     No client-held share is needed: the lent fragment agrees with the
     [ghost_map_auth] [FsAbs.ftop_astate_ro] hands out, so a consumer that
     opens ftopN INSIDE the hop's [={T}=*] reads the parent's row as an
     [ADir] at the lent entry map.  That is [SpecSysMknodAU]'s
     [dlookup_commit] shape on the nose. *)
  Lemma elend_astate Γ (av : aview) (d : Z) (dq : dfrac)
      (ents : gmap fname Z) :
    astate Γ av -∗ elend Γ d dq ents -∗
      ⌜∃ nl : nat, av !! d = Some (MkAnode (ADir ents) nl)⌝.
  Proof.
    rewrite /elend. iIntros "Hst HF".
    iDestruct "HF" as (n) "[Hf [%Hdir %Hde]]".
    iDestruct (nview_of_frag with "Hf") as "Hn".
    iDestruct (astate_nview_dq with "Hst Hn") as %Hav.
    iPureIntro. exists (fn_nlink n).
    by rewrite Hav /abs_of /abs_node Hdir Hde.
  Qed.

  (* ...and the same reading with the row's own [anode] named, for a
     consumer that would rather match on [FsAbs.aents]. *)
  Lemma elend_aents Γ (av : aview) (d : Z) (dq : dfrac)
      (ents : gmap fname Z) :
    astate Γ av -∗ elend Γ d dq ents -∗ ⌜aents av d = Some ents⌝.
  Proof.
    iIntros "Hst HF".
    iDestruct (elend_astate with "Hst HF") as %(nl & Hav).
    iPureIntro. by rewrite /aents Hav.
  Qed.

  (* =================================================================== *)
  (*  3.  THE HOP VOCABULARY: [FsAbs.ax_hop] AT THIS LEND                 *)
  (* =================================================================== *)

  (* NOT a new definition of a hop -- [ex_hop] IS [FsAbs.ax_hop] at
     [F := elend], by [reflexivity] ([ex_hop_is_ax_hop]), exactly as
     [SpecNameiTr.nx_hop] is [ax_hop dv_half].  The abbreviation exists so
     the contract file can be [SpecNamexTr]'s text with one name changed
     and so the era walk's [Gamma] is spelled ONCE (it is always the live
     one, [fs_gamma_L]). *)
  Definition ex_hop (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (k : nat) (s : fname) : iProp Σ :=
    ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.

  Definition ex_hops_from (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) : iProp Σ :=
    ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (path_elems pl) n.

  Lemma ex_hop_is_ax_hop (γfs : fs_names) P Pmiss k s :
    ex_hop γfs P Pmiss k s = ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.
  Proof. reflexivity. Qed.

  Lemma ex_hops_is_ax_hops (γfs : fs_names) P Pmiss pl n :
    ex_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (path_elems pl) n.
  Proof. reflexivity. Qed.

  (* PEEL THE HEAD HOP -- [ProofNamexTr.nxt_hops_cons] at this family, and
     the same two-line index shift. *)
  Lemma ex_hops_cons (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (s : fname) (rest : list fname) :
    drop k (path_elems pl) = s :: rest ->
    ex_hops_from γfs P Pmiss pl k -∗
    ex_hop γfs P Pmiss k s ∗ ex_hops_from γfs P Pmiss pl (S k).
  Proof.
    iIntros (Hd) "H". rewrite /ex_hops_from /ax_hops_from.
    assert (HdS : drop (S k) (path_elems pl) = rest).
    { replace (S k) with (k + 1)%nat by lia.
      rewrite -(drop_drop (path_elems pl) 1 k) Hd. reflexivity. }
    rewrite Hd HdS big_sepL_cons Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iApply (big_sepL_mono with "H"). intros i x _.
    replace (k + S i)%nat with (S k + i)%nat by lia. done.
  Qed.

  (* =================================================================== *)
  (*  4.  THE PRODUCER AT THE FIRE, AND THE TWO FIRE LEMMAS               *)
  (* =================================================================== *)

  (* THE BRIDGE.  What the walk holds is [ic_loaded]'s era leg at the
     payload's own [(dn, bm, data)]; what the lend speaks is
     [dir_entries].  [FsAbsSeam.dv_of_dir_entries] is the identification,
     and its two side conditions are the [inode_ok] the payload came with
     and the directory test the walk has already run. *)
  Lemma elend_of_era (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (dq : dfrac) (d : Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    top_frag_q (fs_gamma_L γfs) dq d (era_node dn bm data) ⊢
      elend (fs_gamma_L γfs) d dq (dv_of dn data).
  Proof.
    intros Hok Hty.
    assert (Hd : fn_is_dir (era_node dn bm data) = true).
    { rewrite /fn_is_dir /fn_type era_node_rec.
      by apply bool_decide_eq_true_2. }
    iIntros "H". iExists (era_node dn bm data). iFrame "H". iPureIntro.
    split; [exact Hd | exact (dv_of_dir_entries cov logstart dn bm data Hok Hd)].
  Qed.

  (* THE SPLIT THE FIRE RIDES ON.  The walk lends HALF and keeps HALF; the
     kept half is what identifies the node the caller returns. *)
  Lemma era_half_split Γ (d : Z) (n : fs_node) :
    top_frag Γ d n
    ⊣⊢ top_frag_q Γ (DfracOwn (1/2)) d n ∗ top_frag_q Γ (DfracOwn (1/2)) d n.
  Proof. rewrite top_frag_1 -top_frag_q_split. by rewrite Qp.div_2. Qed.

  (* FIRE A HOP THAT HITS.  [ProofNamexTr.nxt_hop_hit]'s statement with the
     lent resource changed and NOTHING else: same caller fupd, same cursor
     step, same "hand it back at the same dfrac".  The walk's own custody
     is the WHOLE element (namex's [ilock] takes the write arm), so unlike
     the dv fire there is no 3/4 arm to case on -- there is a split
     instead. *)
  Lemma elend_fire_hit (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (P Pmiss : nat -> Z -> iProp Σ) (k : nat) (s : fname) (d : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (c : Z) :
    inode_ok cov logstart dn bm data ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    dv_of dn data !! s = Some c ->
    ex_hop γfs P Pmiss k s -∗ P k d -∗
    top_frag (fs_gamma_L γfs) d (era_node dn bm data) ={⊤}=∗
      top_frag (fs_gamma_L γfs) d (era_node dn bm data) ∗ P (S k) c.
  Proof.
    intros Hok Hty He. iIntros "Hh HP Ht".
    rewrite era_half_split. iDestruct "Ht" as "[Ht1 Ht2]".
    iDestruct (elend_of_era γfs cov logstart (DfracOwn (1/2)) d dn bm data
                 Hok Hty with "Ht2") as "HF".
    rewrite /ex_hop /ax_hop.
    iMod ("Hh" $! d (dv_of dn data) (DfracOwn (1/2)) with "HP HF")
      as "[HF HR]".
    iDestruct (elend_frag with "HF") as (n') "Ht2".
    iDestruct (top_frag_q_agree with "Ht1 Ht2") as %<-.
    iModIntro. iSplitL "Ht1 Ht2"; [by iFrame |].
    rewrite He. iExact "HR".
  Qed.

  (* ...AND ONE THAT MISSES: same lend, [Pmiss] back instead of a stepped
     cursor. *)
  Lemma elend_fire_miss (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (P Pmiss : nat -> Z -> iProp Σ) (k : nat) (s : fname) (d : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    dv_of dn data !! s = None ->
    ex_hop γfs P Pmiss k s -∗ P k d -∗
    top_frag (fs_gamma_L γfs) d (era_node dn bm data) ={⊤}=∗
      top_frag (fs_gamma_L γfs) d (era_node dn bm data) ∗ Pmiss k d.
  Proof.
    intros Hok Hty He. iIntros "Hh HP Ht".
    rewrite era_half_split. iDestruct "Ht" as "[Ht1 Ht2]".
    iDestruct (elend_of_era γfs cov logstart (DfracOwn (1/2)) d dn bm data
                 Hok Hty with "Ht2") as "HF".
    rewrite /ex_hop /ax_hop.
    iMod ("Hh" $! d (dv_of dn data) (DfracOwn (1/2)) with "HP HF")
      as "[HF HR]".
    iDestruct (elend_frag with "HF") as (n') "Ht2".
    iDestruct (top_frag_q_agree with "Ht1 Ht2") as %<-.
    iModIntro. iSplitL "Ht1 Ht2"; [by iFrame |].
    rewrite He. iExact "HR".
  Qed.

  (* =================================================================== *)
  (*  5.  THE PINNED-WALK PACKAGE, FIRED AT THE ERA LEND                  *)
  (* =================================================================== *)

  (* [FsAbs.apn_walk] at [F := elend].  See the header's note on what this
     does and does not give: it is a theorem, and it is vacuous for an inum
     whose payload is checked out, because the walk's custody is the whole
     element.  It is here so the era contract's trace premise can be
     discharged from a client's pins the day a producer exists, with no
     further seam work. *)
  Lemma apn_walk_era Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) :
    arun av root ps ds ->
    apn_pins Γ q av ds ps 0%nat -∗
      apn_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from (elend Γ) (apn_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apn_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝).
  Proof.
    intros Hr.
    iApply (apn_walk Γ q av (elend Γ) root ps ds (elend_agrees Γ) Hr).
  Qed.

  (* ...AND THE ONE A CONSUMER SHOULD ACTUALLY USE (owner ruling, relayed
     2026-08-28): the pin-returning package of [FsAbsPins] at the era lend.
     Same three components, and the third one hands the client's [nview]
     shares BACK beside the answer -- as does the trace contract's failure
     arm, whose [P k d] IS the whole bundle ([FsAbsPins.apr_P_pins]).  The
     era lend discharges the STRONG law, so this is [apr_walk] and not its
     [_rd] sibling. *)
  Lemma apr_walk_era Γ (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) :
    arun av root ps ds ->
    apr_pins Γ q av ds ps -∗
      apr_P Γ q av ds ps 0%nat root
      ∗ ax_hops_from (elend Γ) (apr_P Γ q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apr_P Γ q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝
                     ∗ apr_pins Γ q av ds ps).
  Proof.
    intros Hr.
    iApply (apr_walk Γ q av (elend Γ) root ps ds (elend_agrees Γ) Hr).
  Qed.

  (* the same, in the CONTRACT's own index: the era walk's trace premise is
     [ex_hops_from γfs P Pmiss pl 0], which is [ax_hops_from] at
     [path_elems pl] ([ex_hops_is_ax_hops]), so a client whose run is over
     [path_elems pl] discharges the premise by this lemma with no rewrite. *)
  Lemma apr_hops_era_pl (γfs : fs_names) (q : Qp) (av : aview) (root : Z)
      (pl : list (bv 8)) (ds : list Z) (n : nat) :
    arun av root (path_elems pl) ds ->
    ⊢ ex_hops_from γfs
        (apr_P (fs_gamma_L γfs) q av ds (path_elems pl)) apn_Pmiss pl n.
  Proof.
    intros Hr. rewrite ex_hops_is_ax_hops.
    iApply (apr_hops (fs_gamma_L γfs) q av (elend (fs_gamma_L γfs)) root
              (path_elems pl) ds n (elend_agrees (fs_gamma_L γfs)) Hr).
  Qed.

End FsAbsEra.
