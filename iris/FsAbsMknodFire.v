(* FsAbsMknodFire.v -- THE MKNOD AU's TWO FIRE POINTS, DISCHARGED AGAINST
   THE INVARIANT, plus the two bridges [SpecSysMknodAU]'s header owes its
   prover (items 2 and 4).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the mknod
   AU prover).  A NEW LEAF rather than an append to [FsAbsEraMknod.v], for
   the mirror's reason the campaign's other leaves record ([FsAbsNpar],
   [FsAbsPins]): the build mirror forbids touching a tracked file.  Fuse
   the two when [FsAbsEraMknod.v] is next edited.

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
    ↑ftopN ⊆ E ->
    fn_is_dir n = true ->
    dir_entries n !! nm = Some i ->
    ftop_inv γfs -∗
    dlookup_commit_at (fs_gamma_L γfs) ∅ Φ -∗
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
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! d
                   = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))).
    { by rewrite (abs_view_lookup I d n Hlk) (mkf_abs_of_dir n Hdir). }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
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
    ↑ftopN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode (ADev ma mi) 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) ∅ (ADev ma mi) Φ -∗
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
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
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
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
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
