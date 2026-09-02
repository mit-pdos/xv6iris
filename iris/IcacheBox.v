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

   Names: the four box gnames per slot come from a new record [ic_boxes]
   beside [ic_names] (extending MkIcNames would sweep its 21 constructors'
   sites; the record is passed alongside instead). *)
From Stdlib Require Import ZArith Lia.
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

(* ---- the identity and the shape ------------------------------------- *)
Notation ic_bid := (option bio_id).

Inductive ic_x : Type :=
  | IcRaw
  | IcUnloaded (g : gname)
  | IcLoaded (g : gname) (dn : dinode) (bm : blkmap).

Global Instance ic_bid_eq_dec : EqDecision ic_bid | 0 := _.
Global Instance ic_bid_countable : Countable ic_bid | 0 := _.
Global Instance ic_bid_inhabited : Inhabited ic_bid := populate None.
Global Instance ic_x_inhabited : Inhabited ic_x := populate IcRaw.

Definition ic_x_loaded (x : ic_x) : bool :=
  match x with IcLoaded _ _ _ => true | _ => false end.
Definition ic_x_gen (x : ic_x) : option gname :=
  match x with IcRaw => None | IcUnloaded g => Some g | IcLoaded g _ _ => Some g end.

(* ---- cameras (to Xv6Cameras §15 at R3) ------------------------------ *)
Class icboxG (Σ : gFunctors) := IcboxG {
  icbox_stampsG :: inG Σ (stampsR ic_bid);
  icbox_slotdG  :: ghost_varG Σ (slot_reg ic_bid ic_x);
  icbox_slotpG  :: ghost_varG Σ (l2_reg ic_bid);
}.
Definition icboxΣ : gFunctors :=
  #[ GFunctor (stampsR ic_bid); ghost_varΣ (slot_reg ic_bid ic_x); ghost_varΣ (l2_reg ic_bid) ].
Global Instance subG_icboxΣ {Σ} : subG icboxΣ Σ -> icboxG Σ.
Proof. solve_inG. Qed.
Global Instance icbox_boxG {Σ} `{!icboxG Σ} `{!kallocG Σ} : boxG ic_bid ic_x Σ :=
  {| box_stampsG := icbox_stampsG; box_cntG := kalloc_count_inG;
     box_slotdG := icbox_slotdG; box_slotpG := icbox_slotpG |}.

(* the per-slot box names, beside [ic_names] *)
Record ic_boxes := MkIcBoxes { icb : nat -> box_names }.

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
        (ic_meta_rest (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))%I
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

  (* THE REGROUPING (F2's icache twin): today's parked bundle -- the two
     identity halves, the valid cell and [ic_payload_arm] at (inum, g, v) --
     IS the box bundle at Some (dev,inum) and a shape with generation g and
     polarity v.  What R3 rewrites every ic_swap_* site through. *)
  Lemma ic_payload_regroup γfs γi cov logstart k dev inum g (v : bool) :
    (inode_ident k (DfracOwn (1/2)) dev inum ∗
     i_valid (ientry k) ↦₄ valid_word v ∗
     ic_payload_arm γfs γi cov logstart k inum g v)
    ⊣⊢
    (∃ x : ic_x, ⌜ic_x_gen x = Some g⌝ ∗ ⌜ic_x_loaded x = v⌝ ∗
       ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) x ∗ ic_rest_amb k x).
  Proof.
  Admitted.
End IcacheBoxAmb.

(* ====================================================================== *)
(*  The instantiation                                                      *)
(* ====================================================================== *)
Section IcacheBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ, !icboxG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  (* the ambient context for the HOLDER-side rows (inode_ref / inode_shr /
     the handle's identity cells); the box λs below take an explicit ξ *)
  Context `{XI : CurCtx}.

  Implicit Types (cn : ic_names) (b : ic_boxes).

  (* the box λs: the ambient bundle at an explicit context *)
  Definition ic_hdr (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_hdr_amb (XI := ξ) γfs γi cov logstart k i x.
  Definition ic_rest (k : nat) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_rest_amb (XI := ξ) k x.

  (* ---- the client obligations (CtxBox's section Context) ------------ *)
  Global Instance ic_hdr_morph γfs γi cov logstart k i x : CtxMorph (ic_hdr γfs γi cov logstart k i x).
  Proof. Admitted.
  Global Instance ic_rest_morph k x : CtxMorph (ic_rest k x).
  Proof. Admitted.
  Global Instance ic_hdr_timeless γfs γi cov logstart k i x ξ : Timeless (ic_hdr γfs γi cov logstart k i x ξ).
  Proof. Admitted.
  Global Instance ic_rest_timeless k x ξ : Timeless (ic_rest k x ξ).
  Proof. Admitted.
  Lemma ic_hdr_excl γfs γi cov logstart k : forall (i i' : ic_bid) (x x' : ic_x) (ξ ξ' : CtxId),
    ic_hdr γfs γi cov logstart k i x ξ -∗ ic_hdr γfs γi cov logstart k i' x' ξ' -∗ False.
  Proof. (* the full i_valid cell in every arm of both matches: ctx_word4_excl_x *) Admitted.
  Lemma ic_rest_excl k : forall (x x' : ic_x) (ξ ξ' : CtxId),
    ic_rest k x ξ -∗ ic_rest k x' ξ' -∗ False.
  Proof. (* the full i_size cell: ctx_word4_excl_x *) Admitted.
  Lemma ic_tok_excl cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof. apply ic_tok_exclusive. Qed.

  (* THE BOX, per slot: tok := ic_tok (ghost, R-4), Q := emp *)
  Definition ic_box cn b (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    is_box (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k) icBoxN (icb b k).
  Definition ic_boxes_all cn b γfs γi cov logstart : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, ic_box cn b γfs γi cov logstart k)%I.

  (* ---- registers, named per slot ------------------------------------- *)
  Definition ic_cnt b k (c : nat) : iProp Σ := cnt_half (X := ic_x) (icb b k) c.
  Definition ic_regd b k (r : slot_reg ic_bid ic_x) : iProp Σ := slotd_half (icb b k) r.
  Definition ic_regp b k (s : l2_reg ic_bid) : iProp Σ := slotp_half (X := ic_x) (icb b k) s.

  (* ---- the reference rows (M-5) --------------------------------------- *)
  (* stamps of mass μ at the slot's identity: whole reference μ = 1, share
     μ = its identity fraction s, lending parent μ = 1 − lent *)
  Definition ic_ref_stamps b k (dev inum : mword 32) (μ : Qp) : iProp Σ :=
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc μ⌝ ∗
       CtxBox.reference (X := ic_x) (icb b k) (Some (dev, inum)) m)%I.

  Definition inode_ref2 b (k : nat) (q : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_ref k q dev inum ∗ ic_ref_stamps b k dev inum 1%Qp)%I.
  Definition inode_shr2 b (k : nat) (s : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_shr k s dev inum ∗ ic_ref_stamps b k dev inum s)%I.
  (* the short parent (IcacheRef.inode_refp_short's tie): identity qt lent
     down to qi, stamps mass 1 − (qt − qi) *)
  Definition inode_ref_lent2 b (k : nat) (qt qi s : Qp) (dev inum : mword 32) : iProp Σ :=
    (⌜(qi + s)%Qp = qt⌝ ∗ inode_ref k qi dev inum ∗
     ∃ μ : Qp, ⌜(μ + s)%Qp = 1%Qp⌝ ∗ ic_ref_stamps b k dev inum μ)%I.

  (* a share carves off a reference and merges back: the identity fraction
     and the stamps mass move together *)
  Lemma inode_ref2_carve b k q s dev inum :
    (s < q)%Qp ->
    inode_ref2 b k q dev inum -∗
    ∃ qi : Qp, ⌜(qi + s)%Qp = q⌝ ∗ inode_ref_lent2 b k q qi s dev inum ∗ inode_shr2 b k s dev inum.
  Proof. Admitted.
  Lemma inode_ref2_gather b k qt qi s dev inum :
    inode_ref_lent2 b k qt qi s dev inum -∗ inode_shr2 b k s dev inum -∗
    inode_ref2 b k qt dev inum.
  Proof. Admitted.

  (* ---- the holder's handle row (M-4, F7's tool, R-1) ----------------- *)
  Definition ic_hold b k (dev inum : mword 32) (s : Qp) : iProp Σ :=
    (∃ t : nat,
       CtxBox.l2_hold (X := ic_x) (icb b k) (Some (dev, inum))
         {[ (Some (dev, inum), t) := s ]})%I.
  (* [ic_deposit cn k (DepShr s dev inum g lo)] REDEFINED (name and arity
     kept for the 21 opaque sites; DepRef/DepFrz die): the parked-fragment
     register half at the share singleton, the share's identity cells and
     its liveness slice.  The sleeplock holder carries this and nothing else
     of the box's between ilock and iunlock. *)
  Definition ic_deposit2 b (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepShr s dev inum g lo =>
        (ic_hold b k dev inum s ∗ inode_ident k (DfracOwn s) dev inum ∗
         live_genlo k s g lo)%I
    | _ => False%I
    end.

  (* ---- the two payload rows (M-6) ------------------------------------ *)
  (* L2: the inode sleeplock's λ payload -- CtxBox.l2_row at ic_tok *)
  Definition ic_slp cn b k : CtxId -> iProp Σ :=
    fun ξ => (∃ s : l2_reg ic_bid,
      CtxBox.l2_row (X := ic_x) (ic_tok cn k) (icb b k) s ξ)%I.
  (* L1: the slot's row in itable_res2 -- the register half, shut and
     empty, IDENTITY = the table's ci !! k (None when unidentified: M-1'),
     bounded by the payload's floor slot [tl] *)
  Definition ic_slot_row b k (oi : ic_bid) (tl : nat) : iProp Σ :=
    (∃ r : slot_reg ic_bid ic_x,
       ic_regd b k r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗ ⌜sr_ident r = oi⌝ ∗
       llb loglen_name (sr_td r) ∗ ⌜(sr_td r ≤ tl)%nat⌝)%I.

  (* ====================================================================== *)
  (*  THE SITES (R3's map), as statements over CtxBox's six lemmas            *)
  (* ====================================================================== *)

  (* iget's RECYCLE, part 1 -- (a) at c = 0 on a DEAD slot: the raw header
     comes out, its shape known from the identity (M-1'). *)
  Lemma ic_recycle_withdraw `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (Kd : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = None -> (sr_td r <= Kd)%nat ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗
    ic_regd b k r -∗ ic_cnt b k 0 ={E}=∗
    own_context ξ ∗ ic_cnt b k 0 ∗
    ic_regd b k (SlotReg (sr_td r) true None (Some IcRaw)) ∗
    ic_hdr γfs γi cov logstart k None IcRaw ξ.
  Proof. Admitted.

  (* iget's RECYCLE, part 2 -- (b) at c = 0 with the bump: the header
     re-deposited at the NEW identity, UNLOADED at a fresh generation (the
     pool's bundle for inum taken under itable.lock, [live_slot_alloc]'s
     half and pending); the new reference is a unit at the deposit stamp. *)
  Lemma ic_recycle_deposit `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (g : gname) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some IcRaw ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd b k r -∗ ic_cnt b k 0 -∗
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd b k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt b k 1 ∗
      ic_ref_stamps b k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof. Admitted.

  (* iget's HIT -- (c) at c ≥ 1 (xv6 matches only ref > 0 slots) *)
  Lemma ic_hit_incr cn b γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) ->
    ic_box cn b γfs γi cov logstart k -∗
    ic_regd b k r -∗ ic_cnt b k (S c) ={E}=∗
    ic_regd b k r ∗ ic_cnt b k (S (S c)) ∗ ic_ref_stamps b k dev inum 1%Qp.
  Proof. Admitted.

  (* iput's ref-- -- (d): the unit's debt paid into the L1 register *)
  Lemma ic_decr cn b γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false ->
    ic_box cn b γfs γi cov logstart k -∗
    ic_regd b k r -∗ llb loglen_name (sr_td r) -∗ ic_cnt b k (S c) -∗
    ic_ref_stamps b k dev inum 1%Qp ={E}=∗
    ∃ td' : nat, ⌜(sr_td r <= td')%nat⌝ ∗
      ic_regd b k (SlotReg td' false (sr_ident r) (sr_x r)) ∗ ic_cnt b k c ∗
      llb loglen_name td'.
  Proof. Admitted.

  (* ilock -- (e) with a SHARE (SpecIlock: one share, consumed).  R1 at the
     genl_llb acquiresleep presents the share's stamp; the L2 row's pieces
     come from the payload.  Out: the bundle at the identity (one binder
     over the shape), and the handle row the holder carries to iunlock. *)
  Lemma ic_ilock_checkout `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat)
      (s0 : l2_reg ic_bid) (Kt Kp : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    lr_hold s0 = None -> (lr_tp s0 <= Kp)%nat ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗ ctx_floor ξ Kp -∗
    (* the share, its stamp covered by Kt (the R1 post at Tl := its stamp) *)
    inode_shr_genlo k s dev inum g lo -∗
    (∃ t : nat, ⌜(t <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icb b k) (Some (dev, inum)) {[ (Some (dev, inum), t) := s ]}) -∗
    ic_tok cn k -∗ ic_regp b k s0 ={E}=∗
    own_context ξ ∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) ∗
    ic_deposit2 b k (DepShr s dev inum g lo).
  Proof. Admitted.

  (* iunlock -- (f): the bundle back at the identity the handle names (the
     register agrees, (I) ties it), the share re-minted at the park stamp,
     the L2 row's pieces for the genin releasesleep *)
  Lemma ic_iunlock_park `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) -∗
    ic_deposit2 b k (DepShr s dev inum g lo) ={E}=∗
    own_context ξ ∗ ic_tok cn k ∗
    ∃ T' : nat,
      ic_regp b k (L2Reg T' None) ∗
      inode_shr_genlo k s dev inum g lo ∗
      CtxBox.reference (X := ic_x) (icb b k) (Some (dev, inum)) {[ (Some (dev, inum), T') := s ]} ∗
      llb loglen_name T'.
  Proof. Admitted.

  (* iput's ref == 1 GUARD -- (a) at c = 1 with the WHOLE unit (inode_refp,
     shares gathered): the header comes out at a NAMED shape, so the guard's
     valid and nlink reads are exact; (b) re-deposits at that shape with no
     bump (cnt stays 1).  One lemma per half. *)
  Lemma ic_guard_withdraw `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (Kd Kt : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) -> (sr_td r <= Kd)%nat ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗ ctx_floor ξ Kt -∗
    ic_regd b k r -∗ ic_cnt b k 1 -∗
    (* the unit, its stamps covered by Kt (R1 at the itable acquire) *)
    (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icb b k) (Some (dev, inum)) m) ={E}=∗
    own_context ξ ∗ ic_cnt b k 1 ∗
    ∃ x0 : ic_x, ⌜x0 ≠ IcRaw⌝ ∗
      ic_regd b k (SlotReg (sr_td r) true (Some (dev, inum)) (Some x0)) ∗
      ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ.
  Proof. Admitted.

  Lemma ic_guard_deposit `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (x0 : ic_x) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some x0 -> sr_ident r = Some (dev, inum) ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd b k r -∗ ic_cnt b k 1 -∗
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd b k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt b k 1 ∗
      ic_ref_stamps b k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof. Admitted.

  (* iput's LAST CLOSE with eviction -- (a) at c = 1 as above, the client
     returns the payload to the pool (icnt_half 0 in hand under itable), then
     (b) at c = 1 with the DEAD identity and the raw header: the slot is
     dead from here (M-1'), and (d) drops the unit. *)
  Lemma ic_evict_deposit `{CID : RiscvLang.CpuId} cn b γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (x0 : ic_x) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some x0 ->
    ic_box cn b γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd b k r -∗ ic_cnt b k 1 -∗
    ic_hdr γfs γi cov logstart k None IcRaw ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd b k (SlotReg T' false None None) ∗
      ic_cnt b k 1 ∗
      (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗
         CtxBox.reference (X := ic_x) (icb b k) None m) ∗
      llb loglen_name T'.
  Proof. Admitted.

  (* boot: every slot dead and IN, at the boot deposit's stamp *)
  Lemma ic_box_alloc `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (ξ : CtxId) (E : coPset) :
    own_context ξ -∗
    ([∗ list] k ∈ seq 0 NINODE,
       ic_hdr γfs γi cov logstart k None IcRaw ξ ∗ ∃ x, ic_rest k x ξ) ={E}=∗
    own_context ξ ∗
    ∃ b : ic_boxes,
      ic_boxes_all cn b γfs γi cov logstart ∗
      ([∗ list] k ∈ seq 0 NINODE, ∃ T_boot : nat,
         ic_regd b k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
         ic_cnt b k 0 ∗ ic_regp b k (L2Reg 0 None)).
  Proof. Admitted.

End IcacheBox.
