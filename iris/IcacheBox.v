(* IcacheBox.v -- THE ICACHE INSTANCE OF THE TRANSIT BOX (endgame §4.2,
   R3), AS A TYPE-CHECKED SKELETON: definitions + site-shaped statements,
   proofs [Admitted].  The second instantiation of CtxBox.v (the "rule of
   two"); bcache's is BioInv v6.

   WHAT THIS FILE PINS, so R3 does not re-derive it in prose:

   M-1' THE DEAD SLOT IS AN IDENTITY, NOT A SHAPE.  id := option (dev × inum);
        None is "never identified or evicted".  P_hdr None x forces x = IcRaw
        (a fixed raw header: cells at any value, no payload ghost), so the
        recycler's (a) at c = 0 KNOWS the shape from the register's identity
        -- no refutation of Unloaded/Loaded is needed.  The vetted M-1
        discharge ("the pool owns sr_ident's inum after eviction") does not
        hold once the evicted inum has been re-cached in another slot k' --
        k' 's box owns the inum's pool resource then, and the recycler of k
        cannot see it.  Encoding deadness in the identity avoids the
        discharge entirely, and the L1 row's tie ⌜sr_ident r = ci !! k⌝
        mirrors the table's identification map exactly (ic_id retires).

   M-3  X := IcRaw | IcUnloaded g | IcLoaded g dn bm.  The generation rides
        the shape (the vetting's addition).  P_hdr = i_valid (full) ∗ the
        identity halves ∗ i_nlink ∗ the payload GHOST at (inum, x) -- the
        loaded/unloaded ghost with its frozen alternative, exactly today's
        ic_payload_arm minus its two cell conjuncts; P_rest = the other four
        meta cells + addrs at x.  Regrouping lemma: ic_payload_regroup.

   M-4  The holder's handle row: ic_deposit at DepShr redefined as
        l2_hold at the SHARE SINGLETON {[(Some (dev,inum), t) := s]} (keys and
        mass pinned, R-1) ∗ the share's identity cells ∗ its liveness slice.

   M-5  THE STAMPS MASS: a whole reference carries mass 1; a share of
        identity fraction s carries mass s; a parent that has lent identity
        (qt − qi) carries mass 1 − (qt − qi).  Σ mass over a slot's
        references = the count, as CtxBox's row (Σ) requires.  The doc's
        "mass q / s" (identity fractions) would break (Σ): a whole reference
        holds identity q ≤ 1/2 but must weigh 1.

   M-6  L2 payload := CtxBox.l2_row at tok := ic_tok; L1 row := ic_slot_row.

   Names (F19): the four box gnames per slot become a FIELD of ic_names
   (icn_box : nat → box_names; six MkIcNames sites, the smaller sweep, and
   what lets [ic_deposit cn k d] keep its name and arity).  In this
   skeleton the record [ic_boxes] stands in for that field so the file is
   self-contained; every [b] below is [cn] at R3.

   AFTER REVIEWER 1's RULE-0 AUDIT (F14–F20, applied here):
   F14  the recycle and the eviction CHANGE the shape at (b): CtxBox gains
        box_deposit_L1_shape (target x1, client entailment P_rest x0 ⊢
        P_rest x1); ic_rest_raw_unloaded / ic_rest_to_raw are the icache's
        two entailments.
   F15  the holder has the share MINUS slh_tok (acquiresleep deposited it):
        (e)/(f) take and return [ic_body k d], the descriptor's cells and
        slice; the client re-forms inode_shr2 after releasesleep.
   F16  iput's own (e)/(f) run at mass 1 with the WHOLE unit: DepRef stays
        as the descriptor of that hold (its identity fraction q, its slice,
        its count fragment, hold mass 1).  ic_deposit2 has both arms.
   F17  ic_slot_row carries the cnt half (tied to M !! k's count, 0 at
        None); the table's dead row keeps [islot_free_at] as the
        complement of the dead header's identity halves.
   F18  ic_decr over any identity (the eviction's (d) is at None).
   F20  boot deposits ic_rest k IcRaw. *)
From Stdlib Require Import ZArith Lia QArith Qcanon.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap ufrac.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import SleepLock.
Require Import Xv6Cameras Xv6G.
Require Import CtxBox.
Require Import FsBlocks.
Require Import FsState.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import DirViewG.
Require Import DirViewLend.
Require Import FsStateEra.
Require Import IrefSlots.
Require Import InodeInv.
Require Import InodeLock.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SepThread.   (* the boot threads own_context through the slots *)

(* the identity, the shape and the cameras live in Xv6Cameras §15; the
   per-slot box names are [icfg_box k] (IcacheRef.icfg, canonical) *)
Definition ic_x_loaded (x : ic_x) : bool :=
  match x with IcLoaded _ _ _ => true | _ => false end.
Definition ic_x_gen (x : ic_x) : option gname :=
  match x with IcRaw => None | IcUnloaded g => Some g | IcLoaded g _ _ => Some g end.

Definition icBoxN : namespace := nroot .@ "xv6icbox".

(* ====================================================================== *)
(*  The bundle, at the AMBIENT context (the box λs instantiate XI := ξ)    *)
(* ====================================================================== *)
Section IcacheBoxAmb.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* the payload's GHOST side: [ic_loaded] minus its two cell conjuncts
     ([inode_meta], [inode_addrs]), verbatim otherwise *)
  Definition ic_loaded_ghost (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       dlinks γfs (bv_unsigned inum) dn bm data ∗
       inode_owned_era γfs γi inum (era_node dn bm data) ∗
       dv_ride (bv_unsigned inum) (dv_of dn data) ∗
       fv_ride (bv_unsigned inum) (fv_of dn data))%I.

  (* the identity-keyed payload at a shape: today's [ic_payload_arm] with
     the cells removed.  An IDENTIFIED slot is never raw. *)
  Definition ic_pay (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (inum : mword 32) (x : ic_x) : iProp Σ :=
    match x with
    | IcRaw => False%I
    | IcUnloaded g =>
        ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true))%I
    | IcLoaded g dn bm =>
        ((ic_loaded_ghost γfs γi cov logstart inum dn bm ∗ ity_shot g (di_type dn) ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true))%I
    end.

  (* the four meta cells P_rest keeps (nlink is L1-side: iput's guard) *)
  Definition ic_meta_rest (ip : mword 64) (d : dinode) : iProp Σ :=
    (i_type  ip ↦₂ di_type  d ∗
     i_major ip ↦₂ di_major d ∗
     i_minor ip ↦₂ di_minor d ∗
     i_size  ip ↦₄ di_size  d)%I.

  (* P_rest at a shape: cells at the record's values when loaded, at any
     values otherwise; the addrs likewise.  [i_size] is the FULL cell
     P_rest_excl runs on. *)
  Definition ic_rest_amb (k : nat) (x : ic_x) : iProp Σ :=
    match x with
    | IcLoaded _ dn bm =>
        (⌜length (bm_cells bm) = 13%nat⌝ ∗
         ic_meta_rest (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))%I
    | _ =>
        ((∃ d : dinode, ic_meta_rest (ientry k) d) ∗
         (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l))%I
    end.

  (* P_hdr at an identity and a shape.  DEAD (None): the raw header, shape
     forced to IcRaw.  IDENTIFIED: valid at the shape's polarity, the two
     identity halves, nlink (at the record's value when loaded), the payload
     ghost.  [i_valid] is the FULL cell P_hdr_excl runs on. *)
  Definition ic_hdr_amb (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) : iProp Σ :=
    match i with
    | None =>
        (⌜x = IcRaw⌝ ∗
         (∃ v : mword 32, i_valid (ientry k) ↦₄ v) ∗
         (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) ∗
         (∃ n : bv 16, i_nlink (ientry k) ↦₂ n))%I
    | Some (dev, inum) =>
        (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
         inode_ident k (DfracOwn (1/2)) dev inum ∗
         (match x with
          | IcLoaded _ dn _ => i_nlink (ientry k) ↦₂ di_nlink dn
          | _ => ∃ n : bv 16, i_nlink (ientry k) ↦₂ n
          end) ∗
         ic_pay γfs γi cov logstart k inum x)%I
    end.

  (* M-1': the dead header's shape is known *)
  Lemma ic_hdr_dead_raw γfs γi cov logstart k x :
    ic_hdr_amb γfs γi cov logstart k None x -∗ ⌜x = IcRaw⌝.
  Proof. iIntros "(% & _)". by iPureIntro. Qed.

  (* F14: the two P_rest entailments the shape-changing (b) needs *)
  Lemma ic_rest_raw_unloaded k g :
    ic_rest_amb k IcRaw ⊣⊢ ic_rest_amb k (IcUnloaded g).
  Proof. reflexivity. Qed.
  Lemma ic_rest_to_raw k x :
    ic_rest_amb k x ⊢ ic_rest_amb k IcRaw.
  Proof.
    destruct x as [|g|g dn bm]; simpl; [iIntros "H"; iExact "H" | iIntros "H"; iExact "H" |].
    iIntros "(%Hlen & Hm & Ha)". iSplitL "Hm". { iExists dn. iExact "Hm". }
    iExists (bm_cells bm). iFrame "Ha". by iPureIntro.
  Qed.

  (* THE REGROUPING (F2's icache twin), PER SHAPE.  Today's rows for a loaded
     / unloaded entry ⇄ the box bundle at IcLoaded g dn bm / IcUnloaded g.
     The frozen alternative has no cell side of its own: the freer deposits
     it with the raw P_rest it holds, so no iff over today's arm is stated. *)
  (* PEEL ONE CONNECTIVE PER STEP (optimization.md / BioInv's tl_struct): a
     single [apply _] over these ∃/∗/∨ towers backtracks across the whole
     instance space and takes minutes. *)
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- Timeless (bi_pure _)  => apply bi.pure_timeless
    | |- _ => apply _
    end.
  Global Instance ic_loaded_ghost_timeless γfs γi cov logstart inum dn bm :
    Timeless (ic_loaded_ghost γfs γi cov logstart inum dn bm).
  Proof. rewrite /ic_loaded_ghost. tl_struct. Qed.
  Global Instance ic_pay_timeless γfs γi cov logstart k inum x :
    Timeless (ic_pay γfs γi cov logstart k inum x).
  Proof. rewrite /ic_pay. destruct x; tl_struct. Qed.
  Global Instance ic_meta_rest_timeless ip d : Timeless (ic_meta_rest ip d).
  Proof. rewrite /ic_meta_rest. tl_struct. Qed.
  Global Instance ic_rest_amb_timeless k x : Timeless (ic_rest_amb k x).
  Proof. rewrite /ic_rest_amb. destruct x; tl_struct. Qed.
  Global Instance ic_hdr_amb_timeless γfs γi cov logstart k i x :
    Timeless (ic_hdr_amb γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr_amb /inode_ident. destruct i as [[dev inum]|]; [destruct x|]; tl_struct.
  Qed.

  Lemma ic_bundle_loaded_intro γfs γi cov logstart k dev inum g dn bm :
    length (bm_cells bm) = 13%nat ->
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    ity_shot g (di_type dn) -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) ∗
    ic_rest_amb k (IcLoaded g dn bm).
  Proof.
    iIntros (Hlen) "Hid Hv Hl Hty Hoff Hlg".
    rewrite /ic_loaded. iDestruct "Hl" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hmeta & Haddr & Hdv & Hfv)".
    rewrite /inode_meta. iDestruct "Hmeta" as "(Hty2 & Hmaj & Hmin & Hnl & Hsz)".
    iSplitR "Hty2 Hmaj Hmin Hsz Haddr".
    - rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl". rewrite /ic_pay. iLeft.
      iFrame "Hty Hoff Hlg". rewrite /ic_loaded_ghost. iExists data. iFrame "Hdl Hera Hdv Hfv". done.
    - rewrite /ic_rest_amb /ic_meta_rest. iFrame "Hty2 Hmaj Hmin Hsz Haddr". done.
  Qed.
  Lemma ic_bundle_loaded_elim γfs γi cov logstart k dev inum g dn bm :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) -∗
    ic_rest_amb k (IcLoaded g dn bm) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word true ∗
    ((ic_loaded γfs γi cov logstart k inum dn bm ∗ ity_shot g (di_type dn) ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true ∗
        inode_meta (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb /ic_meta_rest.
    iIntros "(Hv & Hid & Hnl & Hpay) (%Hlen & (Hty2 & Hmaj & Hmin & Hsz) & Haddr)".
    iFrame "Hid Hv". rewrite /ic_pay.
    iDestruct "Hpay" as "[(Hg & Hty & Hoff & Hlg) | [Hfo Hfs]]".
    - iLeft. iFrame "Hty Hoff Hlg". rewrite /ic_loaded /ic_loaded_ghost.
      iDestruct "Hg" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hdv & Hfv)".
      iExists data. rewrite /inode_meta. iFrame "Hdl Hera Hdv Hfv Haddr Hty2 Hmaj Hmin Hnl Hsz". done.
    - iRight. iFrame "Hfo Hfs Haddr". rewrite /inode_meta. iFrame "Hty2 Hmaj Hmin Hnl Hsz".
  Qed.
  Lemma ic_bundle_unloaded_intro γfs γi cov logstart k dev inum g :
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word false -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) -∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) -∗
    ipool_shape_np γfs γi cov logstart inum -∗
    ity_pending g -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ∗
    ic_rest_amb k (IcUnloaded g).
  Proof.
    iIntros "Hid Hv Hnl Hm Ha Hpool Hty Hoff Hlg".
    rewrite /ic_hdr_amb /ic_rest_amb. iFrame "Hv Hid Hnl Hm Ha".
    rewrite /ic_pay. iLeft. iFrame "Hpool Hty Hoff Hlg".
  Qed.
  Lemma ic_bundle_unloaded_elim γfs γi cov logstart k dev inum g :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) -∗
    ic_rest_amb k (IcUnloaded g) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word false ∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) ∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) ∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) ∗
    ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true)).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb. iIntros "(Hv & Hid & Hnl & Hpay) (Hm & Ha)".
    iFrame "Hid Hv Hnl Hm Ha". iExact "Hpay".
  Qed.
  (* the dead header from raw cells *)
  Lemma ic_hdr_dead_intro γfs γi cov logstart k :
    (∃ v : mword 32, i_valid (ientry k) ↦₄ v) -∗
    (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    ic_hdr_amb γfs γi cov logstart k None IcRaw.
  Proof. iIntros "Hv Hid Hnl". rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl". done. Qed.
End IcacheBoxAmb.

(* ====================================================================== *)
(*  The instantiation                                                      *)
(* ====================================================================== *)
Section IcacheBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  (* the ambient context for the HOLDER-side rows (inode_ref / inode_shr /
     the handle's identity cells); the box λs below take an explicit ξ *)
  Context `{XI : CurCtx}.

  Implicit Types (cn : ic_names).

  (* the box λs: the ambient bundle at an explicit context *)
  Definition ic_hdr (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_hdr_amb (XI := ξ) γfs γi cov logstart k i x.
  Definition ic_rest (k : nat) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_rest_amb (XI := ξ) k x.

  (* ---- the client obligations (CtxBox's section Context) ------------ *)
  Global Instance ic_hdr_morph γfs γi cov logstart k i x : CtxMorph (ic_hdr γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr /ic_hdr_amb /inode_ident.
    destruct i as [[dev inum]|].
    - apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_sep; apply ctx_morph_word4|].
      apply ctx_morph_sep; [| apply ctx_morph_const].
      destruct x; [apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_word2].
    - apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_exist => v; apply ctx_morph_word4|].
      apply ctx_morph_sep.
      + apply ctx_morph_exist => d. apply ctx_morph_exist => n. apply ctx_morph_sep; apply ctx_morph_word4.
      + apply ctx_morph_exist => n. apply ctx_morph_word2.
  Qed.
  Global Instance ic_rest_morph k x : CtxMorph (ic_rest k x).
  Proof.
    rewrite /ic_rest /ic_rest_amb /ic_meta_rest /inode_addrs.
    destruct x as [|g|g dn bm].
    1,2: apply ctx_morph_sep;
         [apply ctx_morph_exist => d; apply ctx_morph_sep; [apply ctx_morph_word2|];
          apply ctx_morph_sep; [apply ctx_morph_word2|]; apply ctx_morph_sep; [apply ctx_morph_word2 | apply ctx_morph_word4]
         | apply ctx_morph_exist => l; apply ctx_morph_sep; [apply ctx_morph_const|];
           apply ctx_morph_big_sepL; intros j a; apply ctx_morph_word4].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep;
      [apply ctx_morph_sep; [apply ctx_morph_word2|]; apply ctx_morph_sep; [apply ctx_morph_word2|];
       apply ctx_morph_sep; [apply ctx_morph_word2 | apply ctx_morph_word4]
      | apply ctx_morph_big_sepL; intros j a; apply ctx_morph_word4].
  Qed.
  Global Instance ic_hdr_timeless γfs γi cov logstart k i x ξ : Timeless (ic_hdr γfs γi cov logstart k i x ξ).
  Proof. rewrite /ic_hdr. apply ic_hdr_amb_timeless. Qed.
  Global Instance ic_rest_timeless k x ξ : Timeless (ic_rest k x ξ).
  Proof. rewrite /ic_rest. apply ic_rest_amb_timeless. Qed.
  Lemma ic_hdr_excl γfs γi cov logstart k : forall (i i' : ic_bid) (x x' : ic_x) (ξ ξ' : CtxId),
    ic_hdr γfs γi cov logstart k i x ξ -∗ ic_hdr γfs γi cov logstart k i' x' ξ' -∗ False.
  Proof.
    iIntros (i i' x x' ξ ξ') "H1 H2".
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ (i_valid (ientry k)) (DfracOwn 1) w)%I
      with "[H1]" as (w1) "H1".
    { rewrite /ic_hdr /ic_hdr_amb. destruct i as [[dev inum]|].
      - iDestruct "H1" as "(Hv & _)". iExists _. iExact "Hv".
      - iDestruct "H1" as "(_ & Hv & _)". iExact "Hv". }
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ' (i_valid (ientry k)) (DfracOwn 1) w)%I
      with "[H2]" as (w2) "H2".
    { rewrite /ic_hdr /ic_hdr_amb. destruct i' as [[dev inum]|].
      - iDestruct "H2" as "(Hv & _)". iExists _. iExact "Hv".
      - iDestruct "H2" as "(_ & Hv & _)". iExact "Hv". }
    iApply (ctx_word4_excl_x with "H1 H2").
  Qed.
  Lemma ic_rest_excl k : forall (x x' : ic_x) (ξ ξ' : CtxId),
    ic_rest k x ξ -∗ ic_rest k x' ξ' -∗ False.
  Proof.
    iIntros (x x' ξ ξ') "H1 H2".
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ (i_size (ientry k)) (DfracOwn 1) w)%I
      with "[H1]" as (w1) "H1".
    { rewrite /ic_rest /ic_rest_amb /ic_meta_rest. destruct x.
      1,2: iDestruct "H1" as "[(%d & _ & _ & _ & Hs) _]"; iExists _; iExact "Hs".
      iDestruct "H1" as "(_ & (_ & _ & _ & Hs) & _)". iExists _. iExact "Hs". }
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ' (i_size (ientry k)) (DfracOwn 1) w)%I
      with "[H2]" as (w2) "H2".
    { rewrite /ic_rest /ic_rest_amb /ic_meta_rest. destruct x'.
      1,2: iDestruct "H2" as "[(%d & _ & _ & _ & Hs) _]"; iExists _; iExact "Hs".
      iDestruct "H2" as "(_ & (_ & _ & _ & Hs) & _)". iExists _. iExact "Hs". }
    iApply (ctx_word4_excl_x with "H1 H2").
  Qed.
  Lemma ic_tok_excl cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof. apply ic_tok_exclusive. Qed.

  (* THE BOX, per slot: tok := ic_tok (ghost, R-4), Q := emp *)
  Definition ic_box cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    is_box (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k) icBoxN (icfg_box k).
  Definition ic_boxes_all cn γfs γi cov logstart : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, ic_box cn γfs γi cov logstart k)%I.

  (* ---- registers, named per slot ------------------------------------- *)
  Definition ic_cnt k (c : nat) : iProp Σ := cnt_half (X := ic_x) (icfg_box k) c.
  Definition ic_regd k (r : slot_reg ic_bid ic_x) : iProp Σ := slotd_half (icfg_box k) r.
  Definition ic_regp k (s : l2_reg ic_bid) : iProp Σ := slotp_half (X := ic_x) (icfg_box k) s.

  (* ---- the reference rows (M-5) --------------------------------------- *)
  (* stamps of mass μ at the slot's identity: whole reference μ = 1, share
     μ = its identity fraction s, lending parent μ = 1 − lent *)
  Definition ic_ref_stamps_at k (i : ic_bid) (μ : Qp) : iProp Σ :=
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc μ⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) i m)%I.
  Definition ic_ref_stamps k (dev inum : mword 32) (μ : Qp) : iProp Σ :=
    ic_ref_stamps_at k (Some (dev, inum)) μ.

  Definition inode_ref2 (k : nat) (q : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_ref k q dev inum ∗ ic_ref_stamps k dev inum 1%Qp)%I.
  Definition inode_shr2 (k : nat) (s : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_shr k s dev inum ∗ ic_ref_stamps k dev inum s)%I.
  (* the short parent (IcacheRef.inode_refp_short's tie): identity qt lent
     down to qi, stamps mass 1 − (qt − qi) *)
  (* (F24 build note: the lent parent is today's [inode_ref_short] -- the count
     fragment stays at the total qt while identity/liveness/token drop to qi --
     so that is the row here, not [inode_ref k qi]) *)
  Definition inode_ref_lent2 (k : nat) (qt qi s : Qp) (dev inum : mword 32) : iProp Σ :=
    (⌜(qi + s)%Qp = qt⌝ ∗ inode_ref_short k qt qi dev inum ∗
     ∃ μ : Qp, ⌜(μ + s)%Qp = 1%Qp⌝ ∗ ic_ref_stamps k dev inum μ)%I.

  (* a share carves off a reference and merges back: the identity fraction
     and the stamps mass move together *)
  Lemma inode_ref2_carve k q s dev inum :
    (s < q)%Qp -> (s < 1)%Qp ->
    inode_ref2 k q dev inum -∗
    ∃ qi : Qp, ⌜(qi + s)%Qp = q⌝ ∗ inode_ref_lent2 k q qi s dev inum ∗ inode_shr2 k s dev inum.
  Proof.
    iIntros (Hsq Hs1) "[Href Hst]".
    apply Qp.lt_sum in Hsq as [qi Hqi]. apply Qp.lt_sum in Hs1 as [s' Hs'].
    iDestruct "Hst" as (m) "[%Hm Href2]".
    iDestruct (reference_split _ _ m s' s with "Href2") as "[Hp Hs]".
    { rewrite Qp.add_comm. done. }
    iExists qi. iSplitR; [iPureIntro; rewrite Qp.add_comm; done|].
    rewrite Hqi. rewrite (Qp.add_comm s qi) inode_ref_carve. iDestruct "Href" as "[Hshort Hshr]".
    iSplitL "Hshort Hp".
    - rewrite /inode_ref_lent2. iSplitR; [done|]. rewrite -(Qp.add_comm s qi). iFrame "Hshort".
      iExists s'. iSplitR; [iPureIntro; rewrite Qp.add_comm; done|].
      rewrite /ic_ref_stamps /ic_ref_stamps_at. iExists (mscale s' m). iFrame "Hp".
      iPureIntro. rewrite qsum_mscale Hm Qp_to_Qc_1. by rewrite Qcmult_1_l.
    - rewrite /inode_shr2. iFrame "Hshr". rewrite /ic_ref_stamps /ic_ref_stamps_at.
      iExists (mscale s m). iFrame "Hs". iPureIntro. rewrite qsum_mscale Hm Qp_to_Qc_1.
      by rewrite Qcmult_1_l.
  Qed.
  Lemma inode_ref2_gather k qt qi s dev inum :
    inode_ref_lent2 k qt qi s dev inum -∗ inode_shr2 k s dev inum -∗
    inode_ref2 k qt dev inum.
  Proof.
    iIntros "(%Hq & Hshort & Hst1) [Hshr Hst2]".
    iDestruct "Hst1" as (μ) "[%Hμ Hst1]".
    iDestruct "Hst1" as (m1) "[%Hm1 Href1]". iDestruct "Hst2" as (m2) "[%Hm2 Href2]".
    rewrite /inode_ref2. iSplitL "Hshort Hshr".
    { rewrite -Hq. iApply (inode_ref_gather with "Hshort Hshr"). }
    rewrite /ic_ref_stamps /ic_ref_stamps_at. iExists (m1 ⋅ m2).
    iSplitR.
    { iPureIntro. rewrite qsum_op Hm1 Hm2 -Qp.to_Qc_inj_add Hμ. done. }
    iApply (reference_join with "Href1 Href2").
  Qed.

  (* ---- the holder's handle row (M-4, F7's tool, R-1) ----------------- *)
  (* F21: the parked fragment is ANY map of the descriptor's mass -- a unit
     gathered from shares that parked at different stamps has several keys
     and may legitimately be checked out.  The MASS is pinned by the pure
     row (all (d) needs: R-1's reason); the KEYS are recovered at (f) by
     agreement on the register, which records the exact map. *)
  Definition ic_hold k (dev inum : mword 32) (μ : Qp) : iProp Σ :=
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc μ⌝ ∗
       CtxBox.l2_hold (X := ic_x) (icfg_box k) (Some (dev, inum)) m)%I.
  (* what the holder has IN HAND of its share / reference once acquiresleep
     has deposited slh_tok into the tracked lock (F15): the identity cells
     and the liveness slice, plus the count fragment for a whole reference
     (F16).  DepFrz dies (the receipt is a payload-arm alternative). *)
  Definition ic_body (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepShr s dev inum g lo =>
        (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo)%I
    | DepRef q dev inum g lo =>
        (inode_ident k (DfracOwn q) dev inum ∗ live_genlo k q g lo ∗ iref_frag k q)%I
    | _ => False%I
    end.
  (* the stamps mass the descriptor's holder parked: a share its fraction
     (M-5), a whole reference 1 *)
  Definition ic_dep_mass (d : ic_dep) : Qp :=
    match d with DepShr s _ _ _ _ => s | _ => 1%Qp end.
  Definition ic_dep_id (d : ic_dep) : ic_bid :=
    match d with
    | DepShr _ dev inum _ _ | DepRef _ dev inum _ _ => Some (dev, inum)
    | _ => None
    end.
  (* [ic_deposit cn k d] REDEFINED (name and arity kept for its opaque
     sites): the parked-fragment register half at the holder's singleton --
     keys and mass pinned (R-1) -- and the holder's body.  The sleeplock
     holder carries this and nothing else of the box's across its hold. *)
  Definition ic_deposit2 (k : nat) (d : ic_dep) : iProp Σ :=
    match ic_dep_id d with
    | Some (dev, inum) => (ic_hold k dev inum (ic_dep_mass d) ∗ ic_body k d)%I
    | None => False%I
    end.

  (* ---- the two payload rows (M-6) ------------------------------------ *)
  (* L2: the inode sleeplock's λ payload -- CtxBox.l2_row at ic_tok *)
  Definition ic_slp cn k : CtxId -> iProp Σ :=
    fun ξ => (∃ s : l2_reg ic_bid,
      CtxBox.l2_row (X := ic_x) (ic_tok cn k) (icfg_box k) s ξ)%I.
  (* L1: the slot's row in itable_res2 -- the register half, shut and
     empty, IDENTITY = the table's ci !! k (None when unidentified: M-1'),
     bounded by the payload's floor slot [tl] *)
  Definition ic_slot_row k (oi : ic_bid) (c : nat) (tl : nat) : iProp Σ :=
    (∃ r : slot_reg ic_bid ic_x,
       ic_regd k r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗ ⌜sr_ident r = oi⌝ ∗
       llb loglen_name (sr_td r) ∗ ⌜(sr_td r ≤ tl)%nat⌝ ∗
       ic_cnt k c)%I.
  (* F17: [c] is M !! k's count (0 at None).  The table's DEAD row keeps
     today's [islot_free_at k dev inum] -- the identity halves complementary
     to the dead header's, which the recycler joins for its stores; the
     map's deletion of islot_free is withdrawn. *)

  (* ====================================================================== *)
  (*  THE SITES (R3's map), as statements over CtxBox's six lemmas            *)
  (* ====================================================================== *)

  (* iget's RECYCLE, part 1 -- (a) at c = 0 on a DEAD slot: the raw header
     comes out, its shape known from the identity (M-1'). *)
  Lemma ic_recycle_withdraw `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (Kd : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = None -> (sr_td r <= Kd)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗
    ic_regd k r -∗ ic_cnt k 0 ={E}=∗
    own_context ξ ∗ ic_cnt k 0 ∗
    ic_regd k (SlotReg (sr_td r) true None (Some IcRaw)) ∗
    ic_hdr γfs γi cov logstart k None IcRaw ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfl Hrd Hc".
    iMod (own_unit (authUR (gmapUR (ic_bid * nat) ufracR)) (bx_stamps (icfg_box k))) as "Hf0".
    assert (Hq0 : qsum (∅ : gmap (ic_bid * nat) ufrac) = nat_Qc 0).
    { rewrite /qsum map_fold_empty /nat_Qc /=. symmetry. apply Z2Qc_inj_0. }
    assert (Hm0 : (max_stamp (∅ : gmap (ic_bid * nat) ufrac) <= 0)%nat).
    { rewrite /max_stamp map_fold_empty. lia. }
    iMod (CtxBox.box_withdraw_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 0 ∅ Kd 0 E HE Hw Hq0 HKd Hm0
            with "Hbox Hrun Hfl [] Hrd Hc [Hf0]") as "(Hrun & Hc & Hout)".
    { iApply ctx_floor_0. }
    { rewrite /stamps_frag. iExact "Hf0". }
    iDestruct "Hout" as (x0) "[Hrd Hhdr]". rewrite Hid.
    iDestruct (ic_hdr_dead_raw (XI := ξ) γfs γi cov logstart k x0 with "Hhdr") as %Hx0. subst x0.
    iModIntro. iFrame "Hrun Hc Hrd". iExact "Hhdr".
  Qed.

  (* iget's RECYCLE, part 2 -- (b') at c = 0 with the bump (F14: x0 = IcRaw,
     x1 = IcUnloaded g, entailment ic_rest_raw_unloaded): the header
     re-deposited at the NEW identity, UNLOADED at a fresh generation (the
     pool's bundle for inum taken under itable.lock, [live_slot_alloc]'s
     half and pending); the new reference is a unit at the deposit stamp. *)
  Lemma ic_recycle_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (g : gname) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some IcRaw ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 0 -∗
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 0 (Some (dev, inum)) IcRaw (IcUnloaded g) E HE Hw Hx
            ltac:(intros ξb; rewrite /ic_rest; simpl; reflexivity)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb".
    iSplitL "Hc"; [iExact "Hc"|].
    rewrite /ic_ref_stamps /ic_ref_stamps_at. iExists _. iFrame "Href".
    iPureIntro. rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r.
    change (unit_mass 0) with 1%Qp. reflexivity.
  Qed.

  (* iget's HIT -- (c) at c ≥ 1 (xv6 matches only ref > 0 slots) *)
  Lemma ic_hit_incr cn γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    ic_regd k r -∗ ic_cnt k (S c) ={E}=∗
    ic_regd k r ∗ ic_cnt k (S (S c)) ∗ ic_ref_stamps k dev inum 1%Qp.
  Proof.
    iIntros (HE Hw Hid) "#Hbox Hrd Hc".
    iMod (CtxBox.box_ref_incr (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) r (S c) E HE Hw with "Hbox Hrd Hc") as "(Hrd & Hc & %T & Href)".
    iModIntro. iFrame "Hrd Hc". iEval (rewrite Hid) in "Href".
    rewrite /ic_ref_stamps /ic_ref_stamps_at. iExists _. iFrame "Href".
    iPureIntro. rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. reflexivity.
  Qed.

  (* iput's ref-- -- (d): the unit's debt paid into the L1 register *)
  Lemma ic_decr cn γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (i : ic_bid) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false ->
    ic_box cn γfs γi cov logstart k -∗
    ic_regd k r -∗ llb loglen_name (sr_td r) -∗ ic_cnt k (S c) -∗
    ic_ref_stamps_at k i 1%Qp ={E}=∗
    ∃ td' : nat, ⌜(sr_td r <= td')%nat⌝ ∗
      ic_regd k (SlotReg td' false (sr_ident r) (sr_x r)) ∗ ic_cnt k c ∗
      llb loglen_name td'.
  Proof.
    iIntros (HE Hw) "#Hbox Hrd #Hllb Hc Href". iDestruct "Href" as (m) "[%Hm Href]".
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_ref_decr (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) r c i m E HE Hw Hq with "Hbox Hrd Hllb Hc Href") as "(Hrd & Hc & #Hllb')".
    iModIntro. iExists (Nat.max (sr_td r) (max_stamp m)). iSplitR; [iPureIntro; lia|].
    iFrame "Hrd Hc Hllb'".
  Qed.

  (* ilock's and iput's CHECKOUT -- (e) with the descriptor's holder body
     (F15: the share minus slh_tok; F16: iput's whole unit at DepRef).  R1
     at the genl_llb acquiresleep presents the fragment's stamp; the L2
     row's pieces come from the payload.  Out: the bundle at the identity
     (one binder over the shape), and the handle row [ic_deposit2 k d]. *)
  Lemma ic_checkout `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32)
      (s0 : l2_reg ic_bid) (Kt Kp : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
    lr_hold s0 = None -> (lr_tp s0 <= Kp)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗ ctx_floor ξ Kp -∗
    ic_body k d -∗
    (* F21: any fragment of the descriptor's mass, its stamps covered by Kt
       (R1 at Tl := max_stamp m) -- what ic_ref_stamps / inode_shr2 give *)
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc (ic_dep_mass d)⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) -∗
    ic_tok cn k -∗ ic_regp k s0 ={E}=∗
    own_context ξ ∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) ∗
    ic_deposit2 k d.
  Proof.
    iIntros (HE Hid Hs0 HKp) "#Hbox Hrun #Hflt #Hflp Hbody Href Htok Hrp".
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    iMod (CtxBox.box_checkout (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            (ic_tok_excl cn k) icBoxN (icfg_box k) ξ (Some (dev, inum)) m s0 Kt Kp E HE Hs0 Hmt HKp
            with "Hbox Hrun Hflt Hflp Href [] Htok Hrp") as "(Hrun & Hbun & Hhold)".
    { done. }
    iModIntro. iFrame "Hrun". iSplitL "Hbun"; [iExact "Hbun"|].
    rewrite /ic_deposit2 Hid. iFrame "Hbody". rewrite /ic_hold. iExists m. iFrame "Hhold". done.
  Qed.

  (* iunlock's and iput's PARK -- (f): the bundle back at the identity the
     handle names (the register agrees, (I) ties it), the fragment re-minted
     at the park stamp at the descriptor's mass, the holder's body back, the
     L2 row's pieces for the genin releasesleep (the client re-forms
     inode_shr2 / the reference once releasesleep returns slh_tok) *)
  Lemma ic_park `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) -∗
    ic_deposit2 k d ={E}=∗
    own_context ξ ∗ ic_tok cn k ∗ ic_body k d ∗
    ∃ T' : nat,
      ic_regp k (L2Reg T' None) ∗
      CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum))
        {[ (Some (dev, inum), T') := ic_dep_mass d ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hid) "#Hbox Hrun Hbun Hdep".
    rewrite /ic_deposit2 Hid. iDestruct "Hdep" as "[Hhold Hbody]".
    iDestruct "Hhold" as (m) "[%Hm Hhold]".
    iMod (CtxBox.box_park (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            (ic_hdr_excl γfs γi cov logstart k) (ic_rest_excl k) icBoxN (icfg_box k) ξ (Some (dev, inum)) m E HE
            with "Hbox Hrun Hbun Hhold") as "(Hrun & _ & Htok & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    assert (q = ic_dep_mass d) as ->. { apply Qp.to_Qc_inj_iff. by rewrite Hq Hm. }
    iModIntro. iFrame "Hrun Htok Hbody". iExists T'. iFrame "Hrp Href Hllb".
  Qed.

  (* iput's ref == 1 GUARD -- (a) at c = 1 with the WHOLE unit (inode_refp,
     shares gathered): the header comes out at a NAMED shape, so the guard's
     valid and nlink reads are exact; (b) re-deposits at that shape with no
     bump (cnt stays 1).  One lemma per half. *)
  Lemma ic_guard_withdraw `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (Kd Kt : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) -> (sr_td r <= Kd)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗ ctx_floor ξ Kt -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    (* the unit, its stamps covered by Kt (R1 at the itable acquire) *)
    (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) ={E}=∗
    own_context ξ ∗ ic_cnt k 1 ∗
    ∃ x0 : ic_x, ⌜x0 ≠ IcRaw⌝ ∗
      ic_regd k (SlotReg (sr_td r) true (Some (dev, inum)) (Some x0)) ∗
      ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfld #Hflt Hrd Hc Href".
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    iDestruct "Href" as "(%Hne & %Hk & Hf & #Hl)".
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_withdraw_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 m Kd Kt E HE Hw Hq HKd Hmt
            with "Hbox Hrun Hfld Hflt Hrd Hc Hf") as "(Hrun & Hc & Hout)".
    iDestruct "Hout" as (x0) "[Hrd Hhdr]". rewrite Hid.
    destruct x0 as [|g|g dn bm].
    { rewrite /ic_hdr /ic_hdr_amb. iDestruct "Hhdr" as "(_ & _ & _ & Hpay)".
      rewrite /ic_pay. iDestruct "Hpay" as %[]. }
    all: iModIntro; iFrame "Hrun Hc"; iExists _; iSplitR; [| iFrame "Hrd"; iExact "Hhdr"];
         iPureIntro; congruence.
  Qed.

  Lemma ic_guard_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (x0 : ic_x) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some x0 -> sr_ident r = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hid) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 (Some (dev, inum)) x0 E HE Hw Hx
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
    rewrite /ic_ref_stamps /ic_ref_stamps_at. iExists _. iFrame "Href". iPureIntro.
    rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. change (unit_mass 1) with 1%Qp. reflexivity.
  Qed.

  (* iput's LAST CLOSE with eviction -- (a) at c = 1 as above, the client
     returns the payload to the pool (icnt_half 0 in hand under itable), then
     (b') at c = 1 with the DEAD identity and the raw header (F14: x0 the
     withdrawn shape, x1 = IcRaw, entailment ic_rest_to_raw): the slot is
     dead from here (M-1'), and (d) at None drops the unit (F18). *)
  Lemma ic_evict_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (x0 : ic_x) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some x0 ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    ic_hdr γfs γi cov logstart k None IcRaw ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false None None) ∗
      ic_cnt k 1 ∗
      (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗
         CtxBox.reference (X := ic_x) (icfg_box k) None m) ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 None x0 IcRaw E HE Hw Hx
            ltac:(intros ξb; apply ic_rest_to_raw)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
    iExists _. iFrame "Href". iPureIntro.
    rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. change (unit_mass 1) with 1%Qp. reflexivity.
  Qed.

  (* boot: every slot dead and IN, at the boot deposit's stamp.  Over
     PRE-MINTED names (CtxBox.box_alloc_at, as bio_init does): with F19 the
     box gnames are fields of ic_names, minted before MkIcNames -- the
     caller presents the fresh ghosts and receives the boxes. *)
  Lemma ic_box_alloc_at `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (ξ : CtxId) (E : coPset) :
    own_context ξ -∗
    ([∗ list] k ∈ seq 0 NINODE,
       CtxBox.stamps_auth (X := ic_x) (icfg_box k) ∅ ∗
       ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (icfg_box k)) 1 0%nat ∗
       ghost_var (bx_slotd (icfg_box k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
       ghost_var (bx_slotp (icfg_box k)) 1 (inhabitant : l2_reg ic_bid) ∗
       ic_hdr γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
    own_context ξ ∗
    ic_boxes_all cn γfs γi cov logstart ∗
    ([∗ list] k ∈ seq 0 NINODE, ∃ T_boot : nat,
       ic_regd k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
       ic_cnt k 0 ∗ ic_regp k (L2Reg 0 None)).
  Proof.
    iIntros "Hrun Hall".
    iAssert ([∗ list] i↦k ∈ seq 0 NINODE,
               own_context ξ -∗
               (CtxBox.stamps_auth (X := ic_x) (icfg_box k) ∅ ∗
                ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (icfg_box k)) 1 0%nat ∗
                ghost_var (bx_slotd (icfg_box k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
                ghost_var (bx_slotp (icfg_box k)) 1 (inhabitant : l2_reg ic_bid) ∗
                ic_hdr γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
               own_context ξ ∗
               (ic_box cn γfs γi cov logstart k ∗
                ∃ T_boot : nat,
                  ic_regd k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
                  ic_cnt k 0 ∗ ic_regp k (L2Reg 0 None)))%I as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (i k _) "Hrun (Hst & Hc & Hd & Hp & Hhdr & Hrest)".
      iEval (rewrite -Qp.half_half) in "Hc". iDestruct (ghost_var_split with "Hc") as "[Hc1 Hc2]".
      iMod (ghost_var_update (L2Reg 0 None) with "Hp") as "Hp".
      iEval (rewrite -Qp.half_half) in "Hp". iDestruct (ghost_var_split with "Hp") as "[Hp1 Hp2]".
      iMod (CtxBox.box_alloc_at (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
              icBoxN (icfg_box k) ξ None E with "Hrun Hst Hc1 [Hd] Hp1 [Hhdr Hrest]")
        as "(Hrun & %Tb & #Hbx & Hrd & #Hllb)".
      { iExists _. iExact "Hd". }
      { iExists IcRaw. iFrame "Hhdr Hrest". }
      iModIntro. iFrame "Hrun". iSplitR; [iExact "Hbx"|]. iExists Tb. iFrame "Hrd Hllb Hc2 Hp2". }
    iMod (big_sepL_fupd_thread E (own_context ξ) _ _ (seq 0 NINODE) with "Hrun Hstep Hall")
      as "[Hrun Hpost]".
    iModIntro. iFrame "Hrun". rewrite big_sepL_sep. iDestruct "Hpost" as "[Hboxes Hrows]".
    iFrame "Hrows". iExact "Hboxes".
  Qed.

End IcacheBox.
