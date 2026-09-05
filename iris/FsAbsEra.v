(* FsAbsEra.v -- THE ERA-FRAGMENT LEND: what lane A-iii's option (b) walk
   fires at each hop, and the three laws that make it worth firing.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   the user's 2026-08-28 ruling ("OPTION (b): the campaign builds the
   era-fragment walk").  Design of record: claude-notes/design/
   fs-syscall-specs.md v3, sections 2-3.

   (THE DVIEW RETIREMENT, 2026-08-30: the "first" lend and the contract that
   fired it are DELETED -- this file's lend is the only one left, and the
   history below is why it was built.)

   WHY A SECOND LEND EXISTS AT ALL.  [FsAbsSeam] settled item (iii)'s three
   findings: the dv<->top tie is real and pure ([dir_entries_era_ok], as it
   is now spelled), the
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

     (3) THE ENTRY MAP IS [dir_entries n], NOT the record's own byte
         reading.  Those are one function on a payload node
         ([FsAbsSeam.dir_entries_era_ok]) and
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


(* ==== WHAT IS IN THIS FILE (the FsAbs* era leaves, fused 2026-08-30) ====

   THE ERA WALK'S WHOLE VOCABULARY IS HERE.  Four files were one lane's work
   split only by the build mirror's rule that a tracked file is not touched;
   each of their headers said to fuse them "when [FsAbsEra.v] is next
   edited", and this is that edit.  Every statement and proof below is the
   original text, in its original section at its original binder list:

     section 0    [dir_entries_era_ok] / [abs_of_era_dir] and the payload
                  exclusions -- WAS iris/FsAbsSeam.v (whose surviving half
                  is exactly the pure bridge section 4 consumes).
     sections 1-5 the lend itself -- this file's own.
     section 6    the NAMEIPARENT prefix family -- WAS iris/FsAbsNpar.v.
     section 7    the DEFERRED START -- WAS iris/FsAbsStart.v.

   All four old names survive as stubs that [Require Export] this file, so
   no consumer moved.  The require block below is the four blocks' UNION,
   with [FsAbs] still LAST (and [TsoCtx] still qualified). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.      (* [riscvGS]                                  *)
Require Import DinodeEnc.       (* [dinode], [di_type]                        *)
Require Import DirView.         (* [T_DIR_z], [dir_view], [dir_nrec]          *)
Require Import ByteBuf.         (* [bb_cstr]: section 7's C-string buffer     *)
Require Import DirentEnc.       (* [bview]: section 7's path buffer           *)
Require Import FsTree.          (* [fname]                                    *)
Require Import PathElems.       (* [path_elems], [SLASH]                      *)
Require Import InodeInv.        (* [blkmap], [ROOTINO] : mword 32             *)
Require Import InodeLock.       (* [inode_ok]                                 *)
Require Import IrefSlots.       (* [irefslotG]: section 0's binder list       *)
Require Import FsBlocks.        (* [fs_names]                                 *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the LIVE Gamma               *)
Require Import FsStateEra.      (* [era_node], [era_node_rec]                 *)
Require Import IcacheRef.
Require Import IcacheEscrow.    (* the payload arms                           *)
Require Import Xv6Cameras.
Require Import Xv6G.            (* the bundle                                 *)
Require FsImg.                  (* [FsImg.ROOTINO]: the start rule's root     *)
Require Import FsAbs.           (* LAST: [nview], [ax_hop], [lend_agrees]     *)
Require TsoCtx.   (* qualified: the class only, no notation flip *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE PAYLOAD SEAM (was iris/FsAbsSeam.v, fused 2026-08-30)         *)
(* ===================================================================== *)

(* WHAT SURVIVED THAT FILE.  It asked whether [FsAbs.apn_walk]'s abstracted
   lend law could be discharged at [F := DirViewG.dv_half], the resource the
   landed ghost-trace namei lent at every hop.  The dview retirement deleted
   both the hop and the ghost; three things outlived them:

     1. THE TIE IS PURE AND WAS ALREADY LANDED -- the payload's contents
        reading and its era fragment's are ONE function.  That is
        [dir_entries_era_ok] (and its abstract-node form [abs_of_era_dir]),
        which section 4's [elend_of_era] consumes.
     2. [lend_agrees] WAS THE WRONG LAW at that lend, because [dv_half] rode
        a FILE too -- which is exactly the weakness the era fragment does
        not have (it carries the type), so section 2's lend discharges the
        strong law after all.
     3. NO CLIENT CAN HOLD [nview] WHILE THE WALK RUNS.  [Section
        FsAbsSeam] below is still a theorem about the landed payload and
        still says a pin against a live inum is refuted.

   BINDERS: that file's own, which are [IcacheEscrow]'s verbatim -- wider
   than sections 1-7's, hence its own [Section]. *)

(* ===================================================================== *)
(*  1.  THE PURE HALF: A PAYLOAD NODE'S [dir_entries] IS ITS [dir_view]    *)
(* ===================================================================== *)

(* [FsStateEra.dir_entries_era_node] with its guard discharged: the two side
   conditions are [inode_ok] conjuncts, so every payload arm has them in the
   same [Hiok] its other clauses come out of, and the directory guard is the
   one the walk has already tested.  (This was [dv_of_dir_entries], stated at
   the deleted [DirViewG.dv_of]; the right-hand side is that function,
   spelled out.) *)
Lemma dir_entries_era_ok (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  dir_entries (era_node dn bm data)
  = dir_view data (dir_nrec (bv_unsigned (di_size dn))).
Proof.
  intros (_ & _ & _ & _ & Hsz & Hh & _) Hd.
  rewrite /fn_is_dir /fn_type era_node_rec in Hd.
  by rewrite (dir_entries_era_node dn bm data Hh Hsz) Hd.
Qed.

(* ...and the same fact as the ABSTRACT NODE's arm, which is the form the
   lend law's conclusion is stated in. *)
Lemma abs_of_era_dir (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  an_node (abs_of (era_node dn bm data))
  = ADir (dir_view data (dir_nrec (bv_unsigned (di_size dn)))).
Proof.
  intros Hok Hd.
  by rewrite (abs_of_dir _ Hd) (dir_entries_era_ok cov logstart dn bm data Hok Hd).
Qed.

Section FsAbsSeam.
  (* [IcacheEscrow]'s binder list, verbatim (header). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : TsoCtx.CurCtx}.

  (* =================================================================== *)
  (*  2-3.  THE SEAM AT [dv_half], AND THE LEND FIRED AT THE READ ARM:    *)
  (*        RETIRED WITH THE GHOST (see the header's tombstone)           *)
  (* =================================================================== *)

  (* THE ONE PRODUCER OF A CLIENT-HELD [nview] IN THE LANDED TREE, and it is
     the other half of the read arm: what a read-locking [ilock] withdraws
     ([IcacheEscrow.ic_rd_held] carries [inode_rd_era] at a quarter) IS a
     carrier share, on the nose.  So [apn_pin] is satisfiable -- for an inum
     the client HAS READ-LOCKED, and for no other.  The byte legs come back
     beside it because a read-locker needs them to call [readi]. *)
  Lemma inode_rd_era_nview (γfs : fs_names) (q : Qp) (inum : mword 32)
      (n : fs_node) :
    inode_rd_era γfs (DfracOwn q) inum n -∗
      inode_dat_q (fs_gamma_L γfs) (DfracOwn q) n
      ∗ nview (fs_gamma_L γfs) q (bv_unsigned inum) (abs_of n).
  Proof.
    rewrite /inode_rd_era. iIntros "[$ Ht]". by iApply nview_of_frag.
  Qed.

  (* =================================================================== *)
  (*  4.  ...AND WHY THE WRITE ARM CANNOT BE THE ONE                      *)
  (* =================================================================== *)

  (* THE REFUTATION.  [ic_loaded] carries the era leg at [DfracOwn 1], so it
     carries [top_frag] WHOLE; a client-held [nview] share of that inum is
     not merely unavailable, it is inconsistent.  This is what stops the
     package above from being instantiated against namei's own fire, whose
     directory is checked out on the WRITE arm at the fire instant. *)
  Lemma ic_loaded_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (a : anode) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    iIntros "Hl Hn".
    iDestruct (ic_loaded_open with "Hl") as (data)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* ...and the same at the POOL row, which is where an allocated inum's
     element parks when no cache slot holds it -- so the refutation covers
     every allocated inum, cached or not. *)
  Lemma ipool_alloc_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (q : Qp) (a : anode) :
    ipool_alloc γfs γi cov logstart inum -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    rewrite /ipool_alloc. iIntros "Hp Hn".
    iDestruct "Hp" as (dn0 bm0 data0) "(_ & _ & _ & _ & _ & Hleg)".
    iDestruct (ic_inode_leg_open with "Hleg") as "[_ Hown]".
    iDestruct (inode_owned_era_to_q with "Hown") as "(_ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* the same statement in the walk package's own vocabulary: a PIN cannot be
     held against a loaded payload *)
  Lemma apn_pin_loaded_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (av : aview) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    apn_pin (fs_gamma_L γfs) q av (bv_unsigned inum) -∗ False.
  Proof.
    iIntros "Hl Hp". rewrite /apn_pin. iDestruct "Hp" as (a) "[_ Hn]".
    iApply (ic_loaded_nview_excl with "Hl Hn").
  Qed.

End FsAbsSeam.


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
  Lemma elend_astate_q Γ (q : Qp) (av : aview) (d : Z) (dq : dfrac)
      (ents : gmap fname Z) :
    astate_q Γ q av -∗ elend Γ d dq ents -∗
      ⌜∃ nl : nat, av !! d = Some (MkAnode (ADir ents) nl)⌝.
  Proof.
    rewrite /elend. iIntros "Hst HF".
    iDestruct "HF" as (n) "[Hf [%Hdir %Hde]]".
    iDestruct (nview_of_frag with "Hf") as "Hn".
    iDestruct (astate_q_nview_dq with "Hst Hn") as %Hav.
    iPureIntro. exists (fn_nlink n).
    by rewrite Hav /abs_of /abs_node Hdir Hde.
  Qed.

  (* ...and at the READING, any fraction *)
  Lemma elend_astate Γ (av : aview) (d : Z) (dq : dfrac)
      (ents : gmap fname Z) :
    astate Γ av -∗ elend Γ d dq ents -∗
      ⌜∃ nl : nat, av !! d = Some (MkAnode (ADir ents) nl)⌝.
  Proof.
    iIntros "Hst HF". iDestruct "Hst" as (q) "Hst".
    iApply (elend_astate_q with "Hst HF").
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
     [dir_entries].  [FsAbsSeam.dir_entries_era_ok] is the identification,
     and its two side conditions are the [inode_ok] the payload came with
     and the directory test the walk has already run. *)
  Lemma elend_of_era (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (dq : dfrac) (d : Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    top_frag_q (fs_gamma_L γfs) dq d (era_node dn bm data) ⊢
      elend (fs_gamma_L γfs) d dq
        (dir_view data (dir_nrec (bv_unsigned (di_size dn)))).
  Proof.
    intros Hok Hty.
    assert (Hd : fn_is_dir (era_node dn bm data) = true).
    { rewrite /fn_is_dir /fn_type era_node_rec.
      by apply bool_decide_eq_true_2. }
    iIntros "H". iExists (era_node dn bm data). iFrame "H". iPureIntro.
    split; [exact Hd | exact (dir_entries_era_ok cov logstart dn bm data Hok Hd)].
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
    dir_view data (dir_nrec (bv_unsigned (di_size dn))) !! s = Some c ->
    ex_hop γfs P Pmiss k s -∗ P k d -∗
    top_frag (fs_gamma_L γfs) d (era_node dn bm data) ={⊤}=∗
      top_frag (fs_gamma_L γfs) d (era_node dn bm data) ∗ P (S k) c.
  Proof.
    intros Hok Hty He. iIntros "Hh HP Ht".
    rewrite era_half_split. iDestruct "Ht" as "[Ht1 Ht2]".
    iDestruct (elend_of_era γfs cov logstart (DfracOwn (1/2)) d dn bm data
                 Hok Hty with "Ht2") as "HF".
    rewrite /ex_hop /ax_hop.
    iMod ("Hh" $! d (dir_view data (dir_nrec (bv_unsigned (di_size dn))))
            (DfracOwn (1/2)) with "HP HF")
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
    dir_view data (dir_nrec (bv_unsigned (di_size dn))) !! s = None ->
    ex_hop γfs P Pmiss k s -∗ P k d -∗
    top_frag (fs_gamma_L γfs) d (era_node dn bm data) ={⊤}=∗
      top_frag (fs_gamma_L γfs) d (era_node dn bm data) ∗ Pmiss k d.
  Proof.
    intros Hok Hty He. iIntros "Hh HP Ht".
    rewrite era_half_split. iDestruct "Ht" as "[Ht1 Ht2]".
    iDestruct (elend_of_era γfs cov logstart (DfracOwn (1/2)) d dn bm data
                 Hok Hty with "Ht2") as "HF".
    rewrite /ex_hop /ax_hop.
    iMod ("Hh" $! d (dir_view data (dir_nrec (bv_unsigned (di_size dn))))
            (DfracOwn (1/2)) with "HP HF")
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

(* ===================================================================== *)
(*  6.  THE NAMEIPARENT PREFIX FAMILY                                     *)
(*      (was iris/FsAbsNpar.v, fused 2026-08-30)                           *)
(* ===================================================================== *)

(* FsAbsNpar.v -- THE NAMEIPARENT SIDE OF THE ERA WALK'S VOCABULARY: the
   hop family over the PARENT PREFIX, and the death arm a nameiparent walk
   can actually reach.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item ("the NAMEIPARENT walk").  Design of record:
   claude-notes/design/fs-syscall-specs.md v3, sections 2-3.

   (WAS A LEAF, iris/FsAbsNpar.v, for the mechanical reason [FsAbsPins] was
   one: the EC2 build mirror forbids touching a tracked file.  FUSED IN
   2026-08-30, as its own text asked; the stub at the old name re-exports
   this file.)

   NOTHING HERE IS A NEW KIND OF HOP.  [ep_hop] is [FsAbs.ax_hop] at
   [FsAbsEra.elend], by [reflexivity] -- the very same hop [FsAbsEra.ex_hop]
   is.  What changes is the LIST it ranges over.

   THE ONE IDEA.  nameiparent walks one element LESS than namei: it
   dirlookups every element but the last, and returns the directory the
   last element would have been looked up IN.  So its trace family is the
   hop list over [removelast (path_elems pl)] -- which is, definitionally,
   [SpecSysMknodAU.mknod_parent_elems pl], the family lane W's
   [FsAbsEraMknod.mknod_walk_pre_era] already produces.  Stating the
   contract over the parent prefix is therefore not a design choice with
   alternatives: it is the only shape a create-side caller can supply.  (An
   earlier sketch had the walk take the FULL family and hand the last hop
   back unfired; that is unsuppliable, because producing the extra hop is a
   real fupd obligation and the caller has no directory to discharge it
   against.)

   THE DEATH ARM IS THE GENUINELY NEW STATEMENT.  The frozen namei shape
   ([SpecNameiTr] / [SpecNamexEra]) is

       exists k d, k < L /\ ((P k d * hops k) \/ (Pmiss k d * hops (S k)))

   and it cannot express two things a nameiparent walk really does.

     (1) THE PARENT'S OWN TYPE TEST.  namex runs [ip->type == T_DIR]
         (+0xbc) and its nlink guard (+0x7a) at EVERY level it reaches --
         including the LAST one, the level whose directory is the parent
         being returned.  A death there is at index [k = length ps], one
         past the last hop, which [k < length ps] refuses.

     (2) "nameiparent of /".  When the path has no elements at all the loop
         never runs: namex falls out at +0x140, iputs, and returns 0 with
         the cursor and the (empty) family untouched.  That is [k = 0] with
         [length ps = 0], which again [k < length ps] refuses.

   So the LEFT disjunct's bound is [k <= length ps] and both cases land in
   it.  The RIGHT disjunct -- hop [k] fired and MISSED -- keeps a STRICT
   bound, and honestly so: dirlookup is reached only after the walk has
   decided the element is not the last one, so a miss cannot happen at the
   parent level.  The two bounds differ by exactly the instruction order of
   namex's loop body, which is the point of stating them separately rather
   than weakening both.

   BINDERS: [FsAbsEra]'s, unchanged. *)

(* ===================================================================== *)
(*  0.  TWO PURE FACTS ABOUT [removelast]                                 *)
(*                                                                        *)
(*  Both are used by the walk's proof and by the discharge lemmas, and    *)
(*  neither is in stdpp under a name this import mix exposes.  Stated at  *)
(*  the top level, outside the ghost section, so they carry no binder.    *)
(* ===================================================================== *)

Lemma np_len_removelast {A} (l : list A) :
  length (removelast l) = (length l - 1)%nat.
Proof.
  induction l as [|x l IH]; [reflexivity |].
  destruct l as [|y l']; [reflexivity |].
  cbn [removelast] in *. cbn [length] in *. lia.
Qed.

Lemma np_removelast_app {A} (l l' : list A) :
  l' <> [] -> removelast (l ++ l') = l ++ removelast l'.
Proof.
  intros Hne. induction l as [|x l IH]; [reflexivity |].
  cbn [app]. rewrite -IH.
  destruct (l ++ l') as [|y r] eqn:Heq; [| reflexivity].
  exfalso. destruct l as [|z l0]; cbn [app] in Heq;
    [ exact (Hne Heq) | discriminate ].
Qed.

Lemma np_removelast_snoc {A} (l : list A) (x : A) :
  removelast (l ++ [x]) = l.
Proof. rewrite (np_removelast_app l [x] ltac:(discriminate)). by rewrite app_nil_r. Qed.

(* THE TWO INDEX BOUNDS THE WALK'S PROOF NEEDS, HOISTED.  They are here and
   not inline for [ProofNamex.v]'s own reason (its [nx_wi_*] family): inside
   that file's proofmode context [lia] on a goal with NAT SUBTRACTION fails
   with "Cannot find witness" -- measured, on the two-line goal
   [n <= n + S m - 1] -- while the same goal closes instantly at the top
   level.  Stated so the walk never has to subtract: the caller hands the
   decomposition it already has and gets the bound. *)

Lemma np_removelast_len_ge {A} (ps es rest : list A) :
  ps = es ++ rest -> rest <> [] ->
  (length es <= length (removelast ps))%nat.
Proof.
  intros -> Hne. rewrite (np_removelast_app es rest Hne) length_app. lia.
Qed.

Lemma np_removelast_len_gt {A} (ps es : list A) (x : A) (rest : list A) :
  ps = (es ++ [x]) ++ rest -> rest <> [] ->
  (length es < length (removelast ps))%nat.
Proof.
  intros -> Hne.
  rewrite (np_removelast_app (es ++ [x]) rest Hne) !length_app.
  cbn [length]. lia.
Qed.

Section FsAbsNpar.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE PARENT PREFIX AND ITS HOP FAMILY                            *)
  (* =================================================================== *)

  Definition np_elems (pl : list (bv 8)) : list fname :=
    removelast (path_elems pl).

  Definition ep_hop (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (k : nat) (s : fname) : iProp Σ :=
    ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.

  Definition ep_hops_from (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) : iProp Σ :=
    ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (np_elems pl) n.

  Lemma ep_hop_is_ax_hop (γfs : fs_names) P Pmiss k s :
    ep_hop γfs P Pmiss k s = ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.
  Proof. reflexivity. Qed.

  Lemma ep_hops_is_ax_hops (γfs : fs_names) P Pmiss pl n :
    ep_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (np_elems pl) n.
  Proof. reflexivity. Qed.

  (* the head hop peels off exactly as [FsAbsEra.ex_hops_cons] peels it,
     at the shorter list *)
  Lemma ep_hops_cons (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (s : fname) (rest : list fname) :
    drop k (np_elems pl) = s :: rest ->
    ep_hops_from γfs P Pmiss pl k -∗
    ep_hop γfs P Pmiss k s ∗ ep_hops_from γfs P Pmiss pl (S k).
  Proof.
    iIntros (Hd) "H". rewrite /ep_hops_from /ax_hops_from.
    assert (HdS : drop (S k) (np_elems pl) = rest).
    { replace (S k) with (k + 1)%nat by lia.
      rewrite -(drop_drop (np_elems pl) 1 k) Hd. reflexivity. }
    rewrite Hd HdS big_sepL_cons Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iApply (big_sepL_mono with "H"). intros i x _.
    replace (k + S i)%nat with (S k + i)%nat by lia. done.
  Qed.

  (* the family past its end is [emp] -- what the success exit and the
     "nameiparent of /" exit both hand back *)
  Lemma ep_hops_done (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) :
    (length (np_elems pl) <= k)%nat ->
    ⊢ ep_hops_from γfs P Pmiss pl k.
  Proof.
    intros Hk. rewrite /ep_hops_from /ax_hops_from.
    rewrite (drop_ge (np_elems pl) k Hk). by iApply big_sepL_nil.
  Qed.

  (* =================================================================== *)
  (*  2.  THE DEATH ARM                                                   *)
  (* =================================================================== *)

  (* See the header for why the two bounds differ.  LEFT: hop [k] never
     fired (the level's type test or nlink guard died, or the path had no
     elements at all), so the cursor comes back beside hops [k..] -- and
     [k] may BE [length ps], the parent's own level.  RIGHT: hop [k] fired
     and missed, which can only happen strictly inside the prefix. *)
  Definition np_dead (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) : iProp Σ :=
    ((∃ (k : nat) (d : Z),
        ⌜(k <= length (np_elems pl))%nat⌝ ∗ P k d
        ∗ ep_hops_from γfs P Pmiss pl k)
     ∨ (∃ (k : nat) (d : Z),
        ⌜(k < length (np_elems pl))%nat⌝ ∗ Pmiss k d
        ∗ ep_hops_from γfs P Pmiss pl (S k)))%I.

  (* the three introduction forms the walk's three failure exits use *)
  Lemma np_dead_unfired (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (d : Z) :
    (k <= length (np_elems pl))%nat ->
    P k d -∗ ep_hops_from γfs P Pmiss pl k -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hk) "HP Hh". rewrite /np_dead. iLeft.
    iExists k, d. iSplitR; [by iPureIntro |]. iFrame.
  Qed.

  Lemma np_dead_missed (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (d : Z) :
    (k < length (np_elems pl))%nat ->
    Pmiss k d -∗ ep_hops_from γfs P Pmiss pl (S k) -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hk) "HP Hh". rewrite /np_dead. iRight.
    iExists k, d. iSplitR; [by iPureIntro |]. iFrame.
  Qed.

  (* "nameiparent of /": the path has no elements, so the family is empty
     and the cursor at 0 IS the whole refund *)
  Lemma np_dead_noelems (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (d : Z) :
    path_elems pl = [] ->
    P 0%nat d -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hnil) "HP".
    iApply (np_dead_unfired γfs P Pmiss pl 0%nat d with "HP").
    - lia.
    - iApply ep_hops_done. rewrite /np_elems Hnil. reflexivity.
  Qed.

End FsAbsNpar.

(* ===================================================================== *)
(*  7.  THE DEFERRED START (was iris/FsAbsStart.v, fused 2026-08-30)       *)
(* ===================================================================== *)

(* FsAbsStart.v -- THE DEFERRED START: the ONE premise shape that lets an
   era walk begin somewhere other than the root.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item ("the RELATIVE START").  (WAS A LEAF, iris/FsAbsStart.v,
   for [FsAbsNpar]'s reason -- the mirror forbids touching a tracked file.
   FUSED IN 2026-08-30, which is what its own text asked for: "fuse the
   three [FsAbs*] era leaves when [FsAbsEra.v] is next edited".)

   ==== WHAT THE GAP ACTUALLY WAS =======================================

   The era contracts ([SpecNamexEra], [SpecNparEra] and the wrappers over
   them) carried TWO trace premises -- [P 0 ROOTINO] and the hop family --
   beside the scope premise [pfun 0 = SLASH].  A RELATIVE walk starts at
   [idup(p->cwd)] instead, and the recorded blocker (SpecNameiTr's Q-c,
   restated in [SpecNparEra]'s header) was that no landed reading exposes
   the cwd's inum: [IcacheRef.inode_held] hides it existentially, so
   [P 0 <the cwd's inum>] is not a formula the caller can write.

   IT DOES NOT HAVE TO BE.  The caller never needs to NAME the start inum
   -- the WALK knows it, and knows it at exactly the instant it matters:
   idup's postcondition hands back a package whose existential witness IS
   the slot's inum, so the proof reads it there and instantiates the
   caller's trace at that value.  What the contract has to carry is
   therefore not an exposed cwd but a trace that is PARAMETRIC in the
   start: a one-shot, universally quantified over the start inum, with the
   only tie a caller can be expected to know -- an ABSOLUTE path starts at
   the root.

   That is precisely the shape lane W's [FsAbsEraMknod.mknod_walk_pre_era]
   was already written in (that file's ∀ pl r with the [pl !! 0 = Some
   SLASH -> r = ROOTINO] side condition), which is why the consumer side
   needed no invention: [ep_start] at lane W's own [pl] IS that predicate
   ([FsAbsNparMknod.np_start_of_mknod], one [iMod] and a [vm_compute]).

   ==== THE ABSOLUTE ARMS DO NOT WEAKEN =================================

   [ex_start_of_pair] / [ep_start_of_pair] are the receipts: a caller
   holding the landed pair, on a path that begins with SLASH, builds the
   deferred form and loses nothing (the tie forces [r = ROOTINO], so the
   pair it holds is already at the right index).  So every consumer of the
   old contracts composes through the new ones, and the strengthening is
   one-directional.

   ==== THE TIE IS ON THE PATH LIST, NOT THE BUFFER =====================

   [pl !! 0 = Some SLASH] rather than [pfun 0 = SLASH]: the walk has both
   ([pl = bview plen pfun]) but only the list form is statable at the
   altitudes above namex, and it is lane W's spelling.  The two head
   lemmas below are the bridge, and they are the reason the walk's
   RELATIVE arm can discharge the tie at all -- it holds [pfun 0 <> SLASH]
   and needs the [pl] form refuted. *)

(* ===================================================================== *)
(*  0.  THE HEAD OF THE PATH BUFFER, BOTH WAYS                            *)
(*                                                                        *)
(*  Top level, outside the ghost section, so they carry no binder -- and  *)
(*  because the walk's proofmode context is where [lia] starves           *)
(*  (ProofNamex's [nx_wi_*] rule).                                        *)
(* ===================================================================== *)

Lemma bview_head_slash (plen : nat) (pfun : nat -> bv 8) :
  bview plen pfun !! 0%nat = Some SLASH -> pfun 0%nat = SLASH.
Proof.
  destruct plen as [| p'].
  - intros H. discriminate H.
  - rewrite (bview_lookup (S p') pfun 0%nat ltac:(lia)).
    intros H. by injection H.
Qed.

(* The other direction needs the buffer to be NONEMPTY, and [bb_cstr]
   gives that for free at a path beginning with SLASH: the terminator sits
   at index [plen], so [plen = 0] would make the head a NUL. *)
Lemma bview_head_slash_intro (plen : nat) (pfun : nat -> bv 8) :
  bb_cstr pfun plen -> pfun 0%nat = SLASH ->
  bview plen pfun !! 0%nat = Some SLASH.
Proof.
  intros [_ Hnul] Hsl.
  destruct plen as [| p'].
  - exfalso. rewrite Hsl in Hnul.
    assert (HSN : SLASH <> (mword_of_int 0 : mword 8))
      by (vm_compute; discriminate).
    exact (HSN Hnul).
  - rewrite (bview_lookup (S p') pfun 0%nat ltac:(lia)). by rewrite Hsl.
Qed.

(* ===================================================================== *)
(*  0'. NAMEX'S START RULE (lane C3)                                      *)
(*                                                                        *)
(*  Pure and top level: absolute paths start at the root, relative ones   *)
(*  at the process's cwd inum [cw].  [FsFdMirror.um_start] is this same   *)
(*  rule read off the U-mode mirror ([FsFdMirror.um_start_of_agree]).     *)
(* ===================================================================== *)

Definition um_start_of (cw : Z) (pl : list (bv 8)) : Z :=
  if decide (pl !! 0%nat = Some SLASH) then FsImg.ROOTINO else cw.

Lemma um_start_of_slash (cw : Z) (pl : list (bv 8)) :
  pl !! 0%nat = Some SLASH -> um_start_of cw pl = FsImg.ROOTINO.
Proof. intros Hsl. rewrite /um_start_of. by rewrite decide_True. Qed.

Lemma um_start_of_rel (cw : Z) (pl : list (bv 8)) :
  pl !! 0%nat <> Some SLASH -> um_start_of cw pl = cw.
Proof. intros Hsl. rewrite /um_start_of. by rewrite decide_False. Qed.

(* the two roots agree ([FsAbsNparMknod.np_rootino_agree] restated here,
   upstream of it, because the tie is now spelled at [FsImg.ROOTINO]) *)
Lemma rootino_agree : bv_unsigned ROOTINO = FsImg.ROOTINO.
Proof. vm_compute. reflexivity. Qed.

Section FsAbsStart.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE DEFERRED TRACE, AT BOTH FAMILIES                            *)
  (* =================================================================== *)

  (* THE NAMEI SIDE: the full family over [path_elems pl].  One shot, at
     the start inum namex's start rule picks -- ROOTINO on the absolute
     arm, the process's cwd inum [cw] on the relative one
     ([um_start_of], the C3 tie: [cw] is the caller's [pv_cwi], and the
     relative arm fires it at idup's package, which C1 pinned to that
     very inum). *)
  Definition ex_start (γfs : fs_names) (cw : Z) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∀ r : Z,
       ⌜r = um_start_of cw pl⌝ ={⊤}=∗
       P 0%nat r ∗ ex_hops_from γfs P Pmiss pl 0%nat)%I.

  (* THE NAMEIPARENT SIDE: the same one shot over the PARENT PREFIX
     ([FsAbsNpar.np_elems], which is lane W's [mknod_parent_elems]). *)
  Definition ep_start (γfs : fs_names) (cw : Z) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∀ r : Z,
       ⌜r = um_start_of cw pl⌝ ={⊤}=∗
       P 0%nat r ∗ ep_hops_from γfs P Pmiss pl 0%nat)%I.

  (* =================================================================== *)
  (*  2.  THE RECEIPTS: THE ABSOLUTE PAIR IS A START                      *)
  (* =================================================================== *)

  Lemma ex_start_of_pair (γfs : fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    pl !! 0%nat = Some SLASH ->
    P 0%nat (bv_unsigned ROOTINO) -∗
    ex_hops_from γfs P Pmiss pl 0%nat -∗
    ex_start γfs cw P Pmiss pl.
  Proof.
    iIntros (Hsl) "HP Hh". rewrite /ex_start.
    iIntros (r Hr). rewrite Hr (um_start_of_slash _ _ Hsl) rootino_agree.
    iModIntro. iFrame.
  Qed.

  Lemma ep_start_of_pair (γfs : fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    pl !! 0%nat = Some SLASH ->
    P 0%nat (bv_unsigned ROOTINO) -∗
    ep_hops_from γfs P Pmiss pl 0%nat -∗
    ep_start γfs cw P Pmiss pl.
  Proof.
    iIntros (Hsl) "HP Hh". rewrite /ep_start.
    iIntros (r Hr). rewrite Hr (um_start_of_slash _ _ Hsl) rootino_agree.
    iModIntro. iFrame.
  Qed.

End FsAbsStart.
