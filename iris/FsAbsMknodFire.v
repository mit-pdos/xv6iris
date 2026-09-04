(* FsAbsMknodFire.v -- THE MKNOD AU's TWO FIRE POINTS, DISCHARGED AGAINST
   THE INVARIANT, plus the two bridges [SpecSysMknodAU]'s header owes its
   prover (items 2 and 4).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the mknod
   AU prover).  (It was a NEW LEAF rather than an append to
   [FsAbsEraMknod.v] for the mirror's reason the campaign's other leaves
   record: the build mirror forbids touching a tracked file.  The two --
   and the other two mknod leaves -- ARE FUSED as of 2026-08-30, which is
   what this paragraph asked for; see the next note.)

   ==== WHY THE COMMITS HAD TO BE RESTATED AT THE AUTHORITY ==============

   THIS IS THE LANE'S FIRST FINDING, and it is a shape finding, not a
   proof gap.  [SpecSysMknodAU]'s two commit steps are stated over
   [FsAbs.astate]:

       astate Γ av ={E}=∗ astate Γ av ∗ Φ ...                (dlookup)
       astate Γ av ={E}=∗ astate Γ av ∗ (astate Γ (δ av) ={E}=∗ ...)  (acre)

   and the prover's only source of [astate] is the γtop authority inside
   [InodeRegion.ftop_inv].  Borrowing it ([FsAbs.ftop_astate_ro] /
   [ftop_astate_acc]) is fine; GIVING IT BACK is not.  [astate Γ av] is
   [∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝], and [abs_view]
   IS NOT INJECTIVE ([abs_of] forgets the record: the block map, the
   size's slack, every field [inode_local] constrains).  So what comes
   back out of a caller's fupd is an authority at SOME map with the right
   reading -- and [ftop_body]'s row ([ftop_clean I A]) is a statement
   about the RECORDS.  Neither give-back wand can be paid:

     - [ftop_astate_ro]'s wants the SAME [I] the borrow named, and nothing
       in [astate Γ av] says the returned map is that one;
     - [ftop_astate_acc]'s wants [inode_local] at EVERY entry of whatever
       map comes back, which is exactly the fact [abs_view] threw away.

   The fix is one step down: the commits below take the RAW MAP and hand
   the very same [ghost_map_auth] back.  [dlookup_commit_at] IMPLIES the
   landed [dlookup_commit] ([dlookup_commit_at_weaken]) -- the read-only
   direction goes through, because a client that can serve the authority
   form can serve the [astate] form by unfolding it.  The success commit's
   two phases do NOT relate that way in either direction (phase 2 names
   the post-state map, and no [astate] at the delta determines it), so
   [acre_commit_at] is a PARALLEL FORM beside the frozen one, in the
   campaign's usual sense: R10 leaves [SpecSysMknodAU] byte-identical and
   the era-side contract ([SpecSysMknodAUEra]) carries these.

   Everything the frozen file offers a client is offered here at the same
   strength: the trivial-receipt units, and the agreement seeds
   ([_pinned]) the stable corollary is derived from.

   ==== WHAT THE TWO FIRE LEMMAS DO ====================================

   [mkf_dlookup_fire] and [mkf_acre_fire] are the two fire points as ONE
   step each, [ftopN] opened and closed inside.  The resource they read
   the row off is NOT a walk's lend but the FIRING FUNCTION'S OWN era
   fragment -- create holds [FsState.top_frag] for the parent inside
   [IcacheEscrow.ic_loaded] across both its dirlookup and its dirlink, so
   no seam is needed at these two instants at all (that is why they are
   dischargeable while [FsAbsEraMknod]'s hop-side twins needed the era
   walk).  [mkf_acre_fire] FUSES the parent-row retag: the two phases and
   the [ghost_map_update] are one [ftopN] critical section, which is what
   the frozen header asks for ("the pair is ONE instant to every other
   party"), and it pays the row obligation [InodeRegion.ireg_top_retag]
   charges every mover -- so a walk that used to call [ireg_top_retag] at
   the parent calls THIS instead, with one extra premise (the caller's
   commit) and one extra payout (the receipt).

   ==== THE TWO BRIDGES =================================================

   [mkf_parent_row] is the reading bridge (item 2): the written parent
   record's abstract row.  Its real half -- [dir_entries] of the appended
   record is [<[nm := i]>] of the old one -- is ALREADY LANDED as
   [FsStateEra.dir_entries_dirlink_ins], so this lemma takes that equation
   as a premise and does the [abs_of] arithmetic around it.
   [mkf_child_dev] is item 4's abstract half ([SpecCreate.create_made]
   read through [abs_of]) and [mkf_low16_mod] / [mkf_dev_arg] are its
   bit-level half: the low halfword of the [argint]'d word, read unsigned,
   IS [SpecSysMknodAU.dev_arg].

   BINDERS: [SpecSysMknodAU]'s section list VERBATIM -- [fileG] is bound
   and [icacheG]/[icfg] resolve only through its fields (SpecCreate's
   header: a standalone [icfg] beside [fileG] gives two instance paths and
   the propositions print identically while failing to unify). *)


(* ==== WHAT IS IN THIS FILE (the mknod/create leaves, fused 2026-08-30) ==

   ONE FILE FOR THE mknod/create AU's ABSTRACT-STATE WORK.  Four leaves were
   one lane's, split only by the build mirror's rule that a tracked file is
   not touched -- and three of the four headers below say, in as many
   words, to fuse them the next time one of them is edited.  This is that
   edit.  Every statement and proof is the original text, in its original
   section at its original binder list (and all four sections take the SAME
   binder list, which is what made them one file's worth of work):

     sections 1-4  the authority-shaped commits, the two fires and the
                   halfword bridge -- this file's own.
     section 5     the era-lend fire points and lane W's two walk
                   predicates -- WAS iris/FsAbsEraMknod.v.
     section 6     the nameiparent acceptance test -- WAS
                   iris/FsAbsNparMknod.v.
     section 7     FIRE 2 at a non-directory child -- WAS
                   iris/FsAbsCreateFire.v.

   NOT FUSED, AND IT IS NOT A JUDGEMENT CALL: the other fire leaves
   ([FsAbsOpenFire], [FsAbsWriteFire], [FsAbsUnlinkFire], [FsAbsReadFire])
   each stand on a DIFFERENT [Spec*AU] contract, and three of those
   contracts require THIS file -- so merging any of them here is a
   dependency CYCLE, not a tidy-up.  One fire leaf per syscall is the
   shape the cone forces.

   All three old names survive as stubs that [Require Export] this file, so
   no consumer moved. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.  (* [nth_byte], [assemble_bytes]            *)
Require Import RiscvExtras.      (* [trunc32]                               *)
Require Import VcGen.            (* [trunc32_unsigned]                      *)
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsTree.           (* [fname]                                 *)
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import InodeInv.
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes [SpecSysMknodAU]'s section list names, IMPORTED
   rather than inherited: [Require Import] does not re-import a required
   file's own imports, and an unbound [fileG] in a [`{! ...}] binder is
   silently generalised into a [gFunctors -> Type] VARIABLE -- at which
   point [icfg] has no field to resolve through. *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecCreate.       (* [create_made], [T_DEVICE]               *)
Require Import SpecSysMknodAU.   (* the frozen statement this parallels     *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)

Local Open Scope Z_scope.

Section MknodFire.
  (* [SpecSysMknodAU]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE AUTHORITY-SHAPED COMMITS                                    *)
  (* =================================================================== *)

  (* the read-only sibling, at the raw map.  Note the receipt is handed
     the READING [abs_view I], so a client never sees a record. *)
  Definition dlookup_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜abs_view I !! d = Some (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = Some i⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗ Φ (abs_view I) d nm i)%I.

  (* the success commit, two-phase, at the raw map.  Phase 2 is quantified
     over the POST map and constrained by its READING alone -- so the
     client still witnesses exactly "the delta was applied" and nothing
     about the record the mover chose. *)
  Definition acre_commit_at Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜cre_pre (abs_view I) d nm ents nl i c⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_create d nm i c (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) 1 I' ={E}=∗
            ghost_map_auth (γtop Γ) 1 I' ∗ Φ (abs_view I) d nm i))%I.

  (* THE ONE RELATION THAT HOLDS: the read-only form is stronger. *)
  Lemma dlookup_commit_at_weaken Γ E Φ :
    dlookup_commit_at Γ E Φ ⊢ dlookup_commit Γ E Φ.
  Proof.
    iIntros "Hcm". rewrite /dlookup_commit.
    iIntros (av d i nm ents nl) "%Hd %Hnm Hst".
    iDestruct (astate_elim with "Hst") as (I) "[Ha %Hav]". subst av.
    iMod ("Hcm" $! I d i nm ents nl with "[//] [//] Ha") as "[Ha HΦ]".
    iModIntro. iFrame "HΦ". iApply astate_intro. iExact "Ha".
  Qed.

  (* satisfiability: neither commit can be vacuously blocked on the
     caller's side (the frozen file's [*_unit] pair, restated) *)
  Lemma dlookup_commit_at_unit Γ E :
    ⊢ dlookup_commit_at Γ E (fun _ _ _ _ => True%I).
  Proof.
    rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma acre_commit_at_unit Γ E c :
    ⊢ acre_commit_at Γ E c (fun _ _ _ _ => True%I).
  Proof.
    rewrite /acre_commit_at. iIntros (I d i nm ents nl) "%Hpre Ha".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1a.  Agreement against the authority, without spending it          *)
  (* ------------------------------------------------------------------ *)

  Lemma mkf_auth_frag Γ (I : gmap Z fs_node) (dq : dfrac) (i : Z)
      (n : fs_node) :
    ghost_map_auth (γtop Γ) 1 I -∗ top_frag_q Γ dq i n -∗ ⌜I !! i = Some n⌝.
  Proof.
    rewrite /top_frag_q. iIntros "Ha Hf".
    by iDestruct (ghost_map_lookup with "Ha Hf") as %Hl.
  Qed.

  Lemma mkf_auth_nview Γ (I : gmap Z fs_node) (dq : dfrac) (i : Z)
      (a : anode) :
    ghost_map_auth (γtop Γ) 1 I -∗ nview_dq Γ dq i a -∗
      ⌜abs_view I !! i = Some a⌝.
  Proof.
    rewrite /nview_dq. iIntros "Ha Hn". iDestruct "Hn" as (n) "[Hf %Han]".
    iDestruct (mkf_auth_frag with "Ha Hf") as %Hl.
    iPureIntro. by rewrite (abs_view_lookup I i n Hl) Han.
  Qed.

  (* THE STABLE SEEDS at this shape -- the frozen file's [_pinned] pair,
     restated so the stable corollary's derivation stays assembly. *)
  Lemma dlookup_commit_at_pinned Γ E (q : Qp) (dpin : Z) (a : anode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    nview Γ q dpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜d = dpin -> av !! dpin = Some a⌝ -∗ nview Γ q dpin a -∗
       Φ av d nm i) -∗
    dlookup_commit_at Γ E Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /dlookup_commit_at.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    destruct (decide (d = dpin)) as [-> | Hne].
    - iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
      iModIntro. iFrame "Ha".
      iApply ("HΦ" $! (abs_view I) dpin nm i with "[%] Hn"). auto.
    - iModIntro. iFrame "Ha".
      iApply ("HΦ" $! (abs_view I) d nm i with "[%] Hn"). congruence.
  Qed.

  Lemma acre_commit_at_pinned Γ E (c : absnode) (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    nview Γ q jpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview Γ q jpin a -∗ Φ av d nm i) -∗
    acre_commit_at Γ E c Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /acre_commit_at.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) d nm i with "[%] Hn"). done.
  Qed.

  (* =================================================================== *)
  (*  2.  THE ROW READINGS                                                *)
  (* =================================================================== *)

  Lemma mkf_abs_of_dir (n : fs_node) :
    fn_is_dir n = true ->
    abs_of n = MkAnode (ADir (dir_entries n)) (fn_nlink n).
  Proof. intros Hd. by rewrite /abs_of /abs_node Hd. Qed.

  Lemma mkf_era_is_dir (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    fn_is_dir (era_node dn bm data) = true.
  Proof.
    intros Hty. rewrite /fn_is_dir /fn_type era_node_rec.
    by apply bool_decide_eq_true_2.
  Qed.

  Lemma mkf_era_nlink (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    fn_nlink (era_node dn bm data) = Z.to_nat (bv_unsigned (di_nlink dn)).
  Proof. by rewrite /fn_nlink era_node_rec. Qed.

  (* ---- ITEM 2: THE READING BRIDGE AT THE WRITE ---------------------- *)

  (* The real half is [FsStateEra.dir_entries_dirlink_ins] (LANDED): the
     appended record's entry map IS [<[s := v]>] of the old one, by
     [dir_view]'s first-match reading over the written slot.  This lemma
     is the [abs_of] arithmetic around it: dirlink keeps the TYPE (so the
     row stays an [ADir]) and the COUNT (so the nlink field does not
     move), which is exactly what makes the fused delta collapse to the
     one-row parent insert. *)
  Lemma mkf_parent_row (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8)) (s : fname) (v : Z) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    dir_entries (era_node dn' bm' data')
      = <[s := v]> (dir_entries (era_node dn bm data)) ->
    abs_of (era_node dn' bm' data')
    = MkAnode (ADir (<[s := v]> (dir_entries (era_node dn bm data))))
              (fn_nlink (era_node dn bm data)).
  Proof.
    intros Hty Hty' Hnl' Hents.
    assert (Hdir' : fn_is_dir (era_node dn' bm' data') = true).
    { apply mkf_era_is_dir. by rewrite Hty'. }
    rewrite (mkf_abs_of_dir _ Hdir') Hents.
    by rewrite !mkf_era_nlink Hnl'.
  Qed.

  (* ---- ITEM 4: THE MINTED CHILD'S ROW ------------------------------- *)

  Lemma mkf_child_dev (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (major minor : mword 16) :
    dn = create_made T_DEVICE major minor ->
    abs_of (era_node dn bm data)
    = MkAnode (ADev (bv_unsigned major) (bv_unsigned minor)) 1%nat.
  Proof.
    intros ->. apply abs_of_create_dev. by rewrite era_node_rec.
  Qed.

  (* =================================================================== *)
  (*  3.  THE TWO FIRE POINTS, [ftopN] OPENED AND CLOSED                  *)
  (* =================================================================== *)

  (* THE READ-ONLY FIRE, at create's dirlookup(found) under the parent's
     lock.  The row comes off the FIRING FUNCTION's own era fragment (the
     one [IcacheEscrow.ic_loaded] carries), so no walk lend is involved
     and the fragment goes straight back. *)
  Lemma mkf_dlookup_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (n : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    fn_is_dir n = true ->
    dir_entries n !! nm = Some i ->
    ftop_inv γfs -∗
    dlookup_commit_at (fs_gamma_L γfs) fsabsE Φ -∗
    top_frag_q (fs_gamma_L γfs) dq d n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq d n
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))⌝
          ∗ ⌜dir_entries n !! nm = Some i⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hdir Hnm. iIntros "#Hi Hcm Hf".
    (* [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot
       solve [γtop ?Γ =?= fs_top γfs], so the fragment is put in the
       body's own spelling before the invariant is opened -- exactly what
       [InodeRegion.ireg_top_retag] does at its own retag. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! d
                   = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))).
    { by rewrite (abs_view_lookup I d n Hlk) (mkf_abs_of_dir n Hdir). }
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I d i nm (dir_entries n) (fn_nlink n)
            with "[//] [//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* THE SUCCESS FIRE, FUSED WITH THE PARENT-ROW RETAG.  Replaces the
     [InodeRegion.ireg_top_retag] a mover would otherwise call at this
     instant: same premise (the new node is well-formed), same payout
     (the moved fragment), plus the caller's two phases fired on either
     side of the [ghost_map_update] INSIDE the one [ftopN] critical
     section.  The child's fragment is only READ (its row is the
     minted-orphan observation [cre_pre]'s third conjunct asks for) and
     comes back untouched. *)
  Lemma mkf_acre_fire (γfs : fs_names) (E : coPset) (ma mi : Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode (ADev ma mi) 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) fsabsE (ADev ma mi) Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i (ADev ma mi)⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hloc Hdir Hnone Habsp' Habsc.
    iIntros "#Hi Hcm Hfp Hfc".
    (* the same re-spelling as above, and the reason is the same *)
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hfc") as %Hlkc.
    assert (Hpre : cre_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) i (ADev ma mi)).
    { rewrite /cre_pre. split_and!.
      - by rewrite (abs_view_lookup I d np Hlkp) (mkf_abs_of_dir np Hdir).
      - exact Hnone.
      - by rewrite (abs_view_lookup I i nc Hlkc) Habsc. }
    (* the fused delta collapses to the ONE-ROW parent insert, and the
       insert's reading is the new record's own row *)
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_create d nm i (ADev ma mi) (abs_view I)).
    { rewrite (abs_view_insert I d np') Habsp'.
      by rewrite (delta_create_dev (abs_view I) d nm (dir_entries np)
                    (fn_nlink np) i ma mi Hpre). }
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I d i nm (dir_entries np) (fn_nlink np)
            with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update np' with "Hta Hfp") as "[Hta Hfp]".
    iMod ("Hph2" $! (<[d := np']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros j m Hj Hun. destruct (decide (j = d)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j m Hj Hun). }
    iModIntro. iFrame "Hfp Hfc". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

End MknodFire.

(* ===================================================================== *)
(*  4.  ITEM 4's BIT-LEVEL HALF: THE HALFWORD ARGUMENT                    *)
(* ===================================================================== *)

(* sys_mknod's [lh a2,-148(s0)] reads back the low HALFWORD of the [int]
   [argint] wrote, i.e. [hw_lo (arg_int32 v)] in ProofSysMknod's
   vocabulary; the record field reads back UNSIGNED.  So the abstract
   child's major number is the low sixteen bits of the trapframe word --
   [SpecSysMknodAU.dev_arg] on the nose.  Stated over the byte spelling
   rather than over [hw_lo] because [hw_lo] lives in a PROOF file. *)
(* the pure split, at the shape the byte assembly leaves behind:
   [Z.rem_mul_r] IS this fact ("the low half plus the next digit"), so the
   two bytes need no bit-shifting of their own. *)
Lemma mkf_split16 (u : Z) :
  (u mod 2 ^ 8 + 2 ^ 8 * ((u / 2 ^ 8) mod 2 ^ 8 + 2 ^ 8 * 0)) mod 2 ^ 16
  = u mod 2 ^ 16.
Proof.
  assert (Hp : (2:Z) ^ 16 = 2 ^ 8 * 2 ^ 8) by (vm_compute; reflexivity).
  rewrite Hp (Z.rem_mul_r u (2 ^ 8) (2 ^ 8)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)).
  rewrite Z.mul_0_r Z.add_0_r.
  apply Z.mod_small.
  pose proof (Z.mod_pos_bound u (2 ^ 8)
                ltac:(vm_compute; reflexivity)) as [Ha0 Ha1].
  pose proof (Z.mod_pos_bound (u / 2 ^ 8) (2 ^ 8)
                ltac:(vm_compute; reflexivity)) as [Hb0 Hb1].
  change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma mkf_low16_mod (w : mword 32) :
  bv_unsigned (Z_to_bv 16 (assemble_bytes [nth_byte w 0; nth_byte w 1])
               : bv 16)
  = bv_unsigned w mod 2 ^ 16.
Proof.
  rewrite Z_to_bv_unsigned /bv_wrap /bv_modulus.
  cbn [assemble_bytes].
  rewrite !nth_byte_unsigned.
  change (Z.of_N (8 * N.of_nat 0)) with 0.
  change (Z.of_N (8 * N.of_nat 1)) with 8.
  change (Z.of_N 16) with 16.
  rewrite Z.shiftr_0_r (Z.shiftr_div_pow2 (bv_unsigned w) 8 ltac:(lia)).
  apply mkf_split16.
Qed.

Lemma mkf_dev_arg (v : mword 64) :
  bv_unsigned (Z_to_bv 16 (assemble_bytes [nth_byte (trunc32 v) 0;
                                           nth_byte (trunc32 v) 1])
               : bv 16)
  = dev_arg v.
Proof.
  rewrite mkf_low16_mod trunc32_unsigned /dev_arg /bv_wrap /bv_modulus.
  change (Z.of_N 32) with 32.
  assert (Hp : (2:Z) ^ 32 = 2 ^ 16 * 2 ^ 16) by (vm_compute; reflexivity).
  rewrite Hp (Z.rem_mul_r (bv_unsigned v) (2 ^ 16) (2 ^ 16)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)).
  rewrite (Z.mul_comm (2 ^ 16) ((bv_unsigned v / 2 ^ 16) mod 2 ^ 16)).
  rewrite Z_mod_plus_full.
  apply Z.mod_mod. vm_compute. discriminate.
Qed.


(* ===================================================================== *)
(*  5.  THE ERA-LEND FIRE POINTS AND THE WALK PREDICATES                  *)
(*      (was iris/FsAbsEraMknod.v, fused 2026-08-30)                       *)
(* ===================================================================== *)

(* THE THREE REQUIRES THIS HALF ADDS, and they sit HERE rather than at the
   top for the reason [FsAbs.v]'s section 5 gives: nothing above this line
   may have a name of theirs resolved by accident.  [FsImg] is REQUIRED and
   NOT imported (both halves below spell [FsImg.ROOTINO] / [FsImg.T_FILE_z]
   qualified, and an import would shadow [InodeInv.ROOTINO]). *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require FsImg.
Require Import FsAbsEra.        (* [elend], [ex_hops_from], [elend_astate],
                                   and (since the era leaves fused) the
                                   parent prefix and the deferred start *)

(* FsAbsEraMknod.v -- THE FIRST CONSUMER, WIRED: [SpecSysMknodAU]'s two
   commit steps consumed at an ERA hop's fire instant, and the era-lend
   twins of its two walk predicates.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii)
   (the era-fragment walk) meeting lane W (the mknod AU statement).  The
   landed statement file does not move (its own R10-parallel discipline);
   these are the PARALLEL forms beside it.

   WHY THIS FILE.  Lane W's header records what its prover owes, and the
   first item is "the two fire points: dirlookup via [ftop_astate_ro]".
   With the LANDED trace contract that item was not merely unproven, it was
   unprovable: [SpecNameiTr.nx_hop] lent [DirViewG.dv_half] (both retired
   2026-08-30; the history is kept because it is why THIS file exists), which
   says
   nothing about gamma-top, so no amount of opening ftopN at the fire
   instant identifies the authority's row for the directory the walk is
   standing on ([FsAbsSeam], findings 2 and 3).  [SpecSysMknodAU]'s
   [mknod_walk_pre] therefore rides [ax_hops_from dv_half] and its prover
   has no way to reach [dlookup_commit]'s premises.

   With the era lend it is three lines: [FsAbsEra.elend_astate] reads the
   row straight off the authority, because the lent fragment and the
   carrier are THE SAME GHOST.  [era_dlookup_fire] below is that step,
   whole; [era_acre_fire] is the success commit's phase 1 at the same
   instant, which needs the parent's row for exactly the same reason.

   WHAT IS NOT HERE.  The nameiparent WALK.  These lemmas are about the
   HOP, and the hop is the same on both sides of namex's [a1] test; what
   the nameiparent side still needs is namex's two npar exits proven at a
   trace contract, which is a walk-proof item and not a lend item (see
   [ProofNamexEra]'s header).  So this file makes the mknod prover's fire
   points discharged-in-advance, and leaves it waiting on the walk that
   delivers them. *)
Section EraMknod.
  (* [SpecSysMknodAU]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE READ-ONLY FIRE                                              *)
  (* =================================================================== *)

  (* THE STEP LANE W's PROVER OWES, discharged.  At the hop instant the
     caller holds three things: its own [dlookup_commit] (the AU's
     read-only arm), the ERA LEND the walk just handed it, and [astate]
     (borrowed out of ftopN by [FsAbs.ftop_astate_ro] -- the borrow is
     not repeated here because it is [FsAbs]'s and the caller does it
     once around this step).  It gets the receipt, and BOTH the lend and
     the state back: nothing of the walk's is consumed, so the hop's
     "hand the fragment back at the same dfrac" obligation is met by the
     same [HF] that came in.

     The [ents !! nm = Some i] premise is dirlookup's own answer, which
     is what the hop's match is computed from -- so a caller inside
     [ax_hop]'s fupd has it by construction. *)
  Lemma era_dlookup_fire Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (av : aview) (d : Z) (dq : dfrac) (ents : gmap fname Z)
      (nm : fname) (i : Z) :
    ents !! nm = Some i ->
    dlookup_commit Γ E Φ -∗ elend Γ d dq ents -∗ astate Γ av ={E}=∗
      astate Γ av ∗ elend Γ d dq ents ∗ Φ av d nm i.
  Proof.
    intros Hnm. iIntros "Hcm HF Hst".
    iDestruct (elend_astate with "Hst HF") as %(nl & Hav).
    iMod ("Hcm" $! av d i nm ents nl with "[//] [//] Hst") as "[Hst HΦ]".
    iModIntro. iFrame "Hst HF HΦ".
  Qed.

  (* =================================================================== *)
  (*  2.  THE SUCCESS COMMIT'S PHASE 1                                    *)
  (* =================================================================== *)

  (* [acre_commit]'s first phase asks for [cre_pre av d nm ents nl i c],
     which is THREE facts: the parent's row read as an [ADir] at the entry
     map the walk lent, the name's absence from it, and the minted child's
     row.  The first is the one only the lend can supply -- and it is
     exactly what the [dv_half] fire could not -- so the era lend supplies
     it and the [nl] the row carries is existential to the caller.  The
     other two are the caller's own (dirlookup's miss and the mint's
     observation) and are premises here. *)
  Lemma era_acre_fire Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (av : aview) (d i : Z) (dq : dfrac) (ents : gmap fname Z)
      (nm : fname) :
    ents !! nm = None ->
    av !! i = Some (MkAnode c 1%nat) ->
    acre_commit Γ E c Φ -∗ elend Γ d dq ents -∗ astate Γ av ={E}=∗
      elend Γ d dq ents ∗ astate Γ av
      ∗ (astate Γ (delta_create d nm i c av) ={E}=∗
         astate Γ (delta_create d nm i c av) ∗ Φ av d nm i).
  Proof.
    intros Hnm Hi. iIntros "Hcm HF Hst".
    iDestruct (elend_astate with "Hst HF") as %(nl & Hav).
    iMod ("Hcm" $! av d i nm ents nl with "[%] Hst") as "[Hst Hph2]".
    { rewrite /cre_pre. split; [exact Hav | split; [exact Hnm | exact Hi]]. }
    iModIntro. iFrame "HF Hst Hph2".
  Qed.

  (* =================================================================== *)
  (*  3.  THE ERA TWINS OF LANE W's TWO WALK PREDICATES                   *)
  (* =================================================================== *)

  (* [SpecSysMknodAU.mknod_walk_pre] with [dv_half] replaced by the era
     lend and NOTHING else -- same one-shot fupd, same fetched-path
     shape, same root tie.  When the nameiparent era walk lands, THIS is
     the premise the syscall contract carries; the landed one stays for
     the dv-firing walk until the retirement step. *)
  Definition mknod_walk_pre_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜pl !! 0%nat = Some SLASH -> r = FsImg.ROOTINO⌝ ={⊤}=∗
       P 0%nat r
       ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
           (mknod_parent_elems pl) 0%nat)%I.

  Definition mknod_walk_dead_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∃ (k : nat) (d : Z),
       ⌜(k < length (mknod_parent_elems pl))%nat⌝ ∗
       ((P k d ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
                   (mknod_parent_elems pl) k)
        ∨ (Pmiss k d
           ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
               (mknod_parent_elems pl) (S k))))%I.

  (* the same two seals lane W puts on its own pair, and for the same
     reason (they are big-ops behind Definitions at syscall altitude) *)

End EraMknod.

Global Typeclasses Opaque mknod_walk_pre_era mknod_walk_dead_era.

(* ===================================================================== *)
(*  6.  THE ACCEPTANCE TEST                                               *)
(*      (was iris/FsAbsNparMknod.v, fused 2026-08-30)                      *)
(* ===================================================================== *)

(* FsAbsNparMknod.v -- THE LANE'S ACCEPTANCE TEST, DISCHARGED: lane W's two
   walk predicates ([FsAbsEraMknod.mknod_walk_pre_era] /
   [mknod_walk_dead_era]) are exactly what the nameiparent era walk's
   contract ([SpecNparEra]) consumes and produces.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item.  (WAS A LEAF, iris/FsAbsNparMknod.v, for the mirror's
   reason; FUSED IN 2026-08-30, stub at the old name.)

   THREE FACTS, and two of them are [reflexivity].

   (1) THE FAMILIES ARE THE SAME FAMILY.  [FsAbsNpar.np_elems pl] and
       [SpecSysMknodAU.mknod_parent_elems pl] are both
       [removelast (path_elems pl)] -- so [ep_hops_from] and the
       [ax_hops_from] inside [mknod_walk_pre_era] are the same big-op, and
       the walk's trace premise IS what the syscall's one-shot hands out.
       This is not a coincidence to be maintained: it is why the npar
       contract ranges over the parent prefix at all (FsAbsNpar's header).

   (2) THE PRE.  [np_pre_of_mknod] fires lane W's one-shot at the string
       the walk fetched and at [ROOTINO], which is what the absolute-path
       scope of this contract pins the start to.  The two [ROOTINO]s --
       [InodeInv.ROOTINO : mword 32], read off namex's [li a1,1], and
       [FsImg.ROOTINO : Z], the image's -- agree by computation.

   (3) THE DEAD.  This one is NOT an identity, and the mismatch is worth
       recording rather than papering over.  [mknod_walk_dead_era] bounds
       its death index STRICTLY ([k < length ps]) in BOTH disjuncts; the
       walk can die at [k = length ps], because namex runs the level's
       type test and nlink guard at the PARENT's own level too
       ([FsAbsNpar]'s header, case (1)), and at [k = 0 = length ps] when
       the path has no elements at all (case (2)).  So the honest
       statement is a DISJUNCTION: either lane W's predicate, or the
       cursor at the parent index -- and the second alternative is exactly
       [SpecSysMknodAU.mknod_post_fail]'s THIRD fold arm
       ([exists d, P (length (mknod_parent_elems pl)) d * acre_commit *
       (... \/ dlookup_commit)]), which a create that never got to
       dirlink refunds anyway.  So mknod's post is dischargeable as it
       stands; what is NOT true is that [mknod_walk_dead_era] alone covers
       the walk's failures. *)

Section NparMknod.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  (1) the families                                                   *)
  (* ------------------------------------------------------------------ *)

  Lemma np_elems_is_mknod_parent_elems (pl : list (bv 8)) :
    np_elems pl = mknod_parent_elems pl.
  Proof. reflexivity. Qed.

  Lemma ep_hops_is_mknod_hops (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) :
    ep_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (mknod_parent_elems pl) n.
  Proof. reflexivity. Qed.

  (* the roots agree *)
  Lemma np_rootino_agree :
    bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  (2) lane W's one-shot supplies the walk's two trace premises       *)
  (* ------------------------------------------------------------------ *)

  (* THE FORM THE WALK ACTUALLY TAKES SINCE LANE A-iii: no firing at all,
     because the START INUM is the walk's to choose ([FsAbsStart]'s
     header).  [ep_start] at a fixed [pl] IS [mknod_walk_pre_era]
     specialized to that [pl] -- same quantifier, same tie, same family --
     so this is a rename plus the two ROOTINOs agreeing. *)
  Lemma np_start_of_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    mknod_walk_pre_era γfs P Pmiss -∗ ep_start γfs P Pmiss pl.
  Proof.
    iIntros "Hpre". rewrite /ep_start. iIntros (r Hr).
    rewrite /mknod_walk_pre_era.
    iMod ("Hpre" $! pl r with "[%]") as "[$ $]"; [| done].
    intros Hsl. rewrite -np_rootino_agree. exact (Hr Hsl).
  Qed.

  Lemma np_pre_of_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    mknod_walk_pre_era γfs P Pmiss ={⊤}=∗
      P 0%nat (bv_unsigned InodeInv.ROOTINO)
      ∗ ep_hops_from γfs P Pmiss pl 0%nat.
  Proof.
    iIntros "Hpre". rewrite /mknod_walk_pre_era.
    iMod ("Hpre" $! pl (bv_unsigned InodeInv.ROOTINO) with "[%]") as "[$ $]".
    { intros _. exact np_rootino_agree. }
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (3) the walk's death arm, folded into lane W's two shapes          *)
  (* ------------------------------------------------------------------ *)

  Lemma np_dead_to_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    np_dead γfs P Pmiss pl -∗
      mknod_walk_dead_era γfs P Pmiss pl
      ∨ (∃ d : Z, P (length (mknod_parent_elems pl)) d).
  Proof.
    rewrite /np_dead /mknod_walk_dead_era.
    iIntros "[Hl | Hr]".
    - iDestruct "Hl" as (k d) "(%Hk & HP & Hh)".
      destruct (decide (k < length (np_elems pl))%nat) as [Hlt | Hge].
      + iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iLeft. iFrame.
      + (* [k = length ps]: the parent's OWN level died.  The family from
           there is empty, and the cursor at the parent index is the whole
           refund -- mknod's third fold arm. *)
        assert (Hkeq : k = length (np_elems pl)) by lia.
        iRight. iExists d. rewrite -Hkeq. iClear "Hh". iExact "HP".
    - iDestruct "Hr" as (k d) "(%Hk & HP & Hh)".
      iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iRight. iFrame.
  Qed.

  (* ...and the SUCCESS side needs no lemma at all: the walk returns
     [P (length (np_elems pl)) iL], which IS
     [P (length (mknod_parent_elems pl)) iL]. *)
  Lemma np_ok_is_mknod_ok (P : nat -> Z -> iProp Σ) (pl : list (bv 8))
      (iL : Z) :
    P (length (np_elems pl)) iL = P (length (mknod_parent_elems pl)) iL.
  Proof. reflexivity. Qed.

End NparMknod.

(* ===================================================================== *)
(*  7.  FIRE 2, AT A NON-DIRECTORY CHILD                                  *)
(*      (was iris/FsAbsCreateFire.v, fused 2026-08-30)                     *)
(* ===================================================================== *)

(* [TsoCtx] is IMPORTED here (and only here) because [Section CreateFire]
   binds [CurCtx]; it is deliberately the LAST require in the file, so no
   notation of its flips under anything above. *)
Require Import TsoCtx.

(* FsAbsCreateFire.v -- the create AU's SUCCESS FIRE AT A NON-DIRECTORY
   CHILD, and the [T_FILE] row reading that instantiates it.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the T_FILE
   create-AU carry).  (WAS A LEAF, iris/FsAbsCreateFire.v, for the mirror's
   reason the campaign's other leaves record: the build mirror forbids
   touching a tracked file.  FUSED IN 2026-08-30 -- "fuse the fire leaves
   when one of them is next edited", as far as the cone allows: the OTHER
   fire leaves each stand on a different [Spec*AU] that requires this file,
   so they cannot follow without a cycle.)

   ==== WHY THIS FILE EXISTS ============================================

   [FsAbsMknodFire.mkf_acre_fire] is PINNED at [ADev ma mi] in exactly one
   place: it discharges the delta's collapse with
   [SpecSysMknodAU.delta_create_dev], the "under [cre_pre] with a DEVICE
   child, the fused delta IS the one-row parent insert" lemma.  Reading
   that lemma's proof shows the device-ness is not used -- what is used is
   that the child is NOT A DIRECTORY, which is what makes
   [SpecSysMknodAU.acre_bump] zero (so the parent's count does not move)
   and what makes [cre_pre_ne] separate parent from child (so the child's
   insert is the identity on its already-minted row).

   So the two lemmas below are the [ADev]-free restatements:

     [caf_delta_create_nondir]  -- [delta_create_dev] at any non-[ADir] [c]
     [caf_acre_fire]            -- [mkf_acre_fire] at any non-[ADir] [c]

   and [caf_child_file] is the [T_FILE] instance of the minted child's row
   ([FsAbsMknodFire.mkf_child_dev]'s twin): [SpecCreate.create_made T_FILE
   major minor] reads as [AFile []] at nlink 1, because that record's size
   is zero and [fn_file_bytes] of a zero-size node is [file_bytes _ 0 = []]
   -- the same arithmetic [FsAbsOpenFire.opf_trunc_bytes] does at itrunc's
   own zeroing.

   R10: neither [FsAbsMknodFire] nor [SpecSysMknodAU] moves.  The device
   fire keeps its own name and its own proof; a caller that wants the
   device instance is not asked to route through the general form.

   BINDERS: [FsAbsMknodFire]'s section list VERBATIM (which is
   [SpecSysMknodAU]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve
   only through its fields (SpecCreate's header: a standalone [icfg] beside
   [fileG] gives two instance paths and the propositions print identically
   while failing to unify). *)

(* ===================================================================== *)
(*  1.  THE DELTA'S COLLAPSE AT A NON-DIRECTORY CHILD (pure)              *)
(* ===================================================================== *)

(* [acre_bump] is zero at everything but a directory: the parent's count
   moves only when the child's ".." takes a token. *)
Lemma caf_acre_bump_nondir (c : absnode) :
  (forall e, c <> ADir e) -> acre_bump c = 0%nat.
Proof.
  intros Hc. destruct c as [bs | ents | ma mi]; [reflexivity | | reflexivity].
  exfalso. exact (Hc ents eq_refl).
Qed.

(* [SpecSysMknodAU.delta_create_dev] with the device-ness dropped: under
   [cre_pre] at a NON-DIRECTORY child the fused delta IS the one-row parent
   insert.  The child's own insert is the identity on the row [cre_pre]'s
   third conjunct already observes, and [cre_pre_ne] is what keeps the two
   inserts from being at the same key. *)
Lemma caf_delta_create_nondir (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  (forall e, c <> ADir e) ->
  cre_pre av d nm ents nl i c ->
  delta_create d nm i c av
  = <[d := MkAnode (ADir (<[nm := i]> ents)) nl]> av.
Proof.
  intros Hc Hp.
  assert (Hne : d <> i) by exact (cre_pre_ne av d nm ents nl i c Hp Hc).
  destruct Hp as (Hd & Hnm & Hi).
  rewrite /delta_create Hd /= (caf_acre_bump_nondir c Hc) Nat.add_0_r.
  rewrite (insert_commute _ i d); [| congruence].
  by rewrite (insert_id av i (MkAnode c 1%nat) Hi).
Qed.

(* ===================================================================== *)
(*  2.  THE MINTED CHILD'S ROW AT [T_FILE]                                *)
(* ===================================================================== *)

(* [SpecSysMknodAU.abs_of_create_dev]'s twin.  Three readings, each off
   [create_made]'s own fields: the type is not [T_DIR_z] (so the row is not
   an [ADir]) and IS [T_FILE_z] (so it is an [AFile]); the size is zero, so
   the byte list is [file_bytes _ 0 = []]; the count is one. *)
Lemma caf_abs_of_create_file (n : fs_node) (major minor : mword 16) :
  fn_rec n = create_made T_FILE major minor ->
  abs_of n = MkAnode (AFile []) 1%nat.
Proof.
  intros Hr.
  assert (Hnd : fn_is_dir n = false).
  { rewrite /fn_is_dir /fn_type Hr. by apply bool_decide_eq_false_2. }
  assert (Hfl : fn_type n = FsImg.T_FILE_z)
    by (rewrite /fn_type Hr; reflexivity).
  assert (Hbytes : fn_file_bytes n = []).
  { rewrite /fn_file_bytes /fn_size Hr. reflexivity. }
  assert (Hnl : fn_nlink n = 1%nat)
    by (rewrite /fn_nlink Hr; reflexivity).
  rewrite /abs_of Hnl. f_equal.
  change (abs_node n) with (an_node (abs_of n)).
  by rewrite (abs_of_file n Hnd Hfl) Hbytes.
Qed.

(* ...and at the era node, which is the shape a walk holds
   ([FsAbsMknodFire.mkf_child_dev]'s spelling). *)
Lemma caf_child_file (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (major minor : mword 16) :
  dn = create_made T_FILE major minor ->
  abs_of (era_node dn bm data) = MkAnode (AFile []) 1%nat.
Proof.
  intros ->. apply (caf_abs_of_create_file _ major minor).
  by rewrite era_node_rec.
Qed.

Section CreateFire.
  (* [FsAbsMknodFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  3.  THE SUCCESS FIRE AT A NON-DIRECTORY CHILD                       *)
  (* =================================================================== *)

  (* [FsAbsMknodFire.mkf_acre_fire] with [ADev ma mi] replaced by an
     arbitrary non-[ADir] [c]: same premises, same [ghost_map_update], same
     one [ftopN] critical section with the caller's two phases on either
     side of it, same payout.  The device instance is [mkf_acre_fire]
     itself and is NOT rerouted through this (R10). *)
  Lemma caf_acre_fire (γfs : fs_names) (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    (forall e, c <> ADir e) ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode c 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) fsabsE c Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i c⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hc Hloc Hdir Hnone Habsp' Habsc.
    iIntros "#Hi Hcm Hfp Hfc".
    (* the same re-spelling [mkf_acre_fire] does, and for the same reason:
       [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot
       solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hfc") as %Hlkc.
    assert (Hpre : cre_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) i c).
    { rewrite /cre_pre. split_and!.
      - by rewrite (abs_view_lookup I d np Hlkp) (mkf_abs_of_dir np Hdir).
      - exact Hnone.
      - by rewrite (abs_view_lookup I i nc Hlkc) Habsc. }
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_create d nm i c (abs_view I)).
    { rewrite (abs_view_insert I d np') Habsp'.
      by rewrite (caf_delta_create_nondir (abs_view I) d nm (dir_entries np)
                    (fn_nlink np) i c Hc Hpre). }
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I d i nm (dir_entries np) (fn_nlink np)
            with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update np' with "Hta Hfp") as "[Hta Hfp]".
    iMod ("Hph2" $! (<[d := np']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = d)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hfp Hfc". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [AFile []] instance, which is the one the T_FILE create-AU fires:
     a file child is never an [ADir]. *)
  Lemma caf_acre_fire_file (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode (AFile []) 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) fsabsE (AFile []) Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i (AFile [])⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hloc Hdir Hnone Habsp' Habsc.
    iIntros "Hi Hcm Hfp Hfc".
    iApply (caf_acre_fire γfs E (AFile []) Φ d i nm dqc np np' nc HE
              ltac:(intros e Hc; discriminate Hc)
              Hloc Hdir Hnone Habsp' Habsc with "Hi Hcm Hfp Hfc").
  Qed.

End CreateFire.
