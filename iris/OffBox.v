(* OffBox.v -- THE OFF BOX: f->off under the transit-box law (tso-cutover
   endgame §6‴ P4 as corrected, §6⁗, §6⁵ ruling item 3, §6⁶ (A)), over
   CtxBox.  PROVEN (L6): the three skeleton statements the proofs corrected
   (off_filealloc, off_dup, off_close) each carry a [STATEMENT CHANGE (L6
   skeleton→proof)] comment above the lemma.

   WHY A BOX.  Main's off ledger (off-ledger.md) keeps `a_foff k ↦₄ v` inside
   a plain inv at the ambient context and parks the INODE's valid cell as its
   checkout marker -- a ξ-bodied invariant, and a cell the inode box owns
   whole.  Under the allowed-forms law the cell is T2 custody in a box.

   THE PROTOCOL (xv6): the cell is written by the opener (`f->off = 0`, under
   ip->lock, ftable.lock RELEASED), read and written by fileread/filewrite
   under ip->lock, and RECLAIMED at fileclose's last reference under
   ftable.lock with no inode lock.  Three locks touch it; the box's two are
   L1 = ftable.lock (the count is f->ref) and L2 = ip->lock of whichever
   inode the file is published on.

   THE INSTANCE:
     id     := nat        the FILE SLOT k (fixed at birth; never changes --
                          the off box needs no (b)/(b′) at all)
     X      := unit       the cell has no shared witness
     P_hdr  := off_resident at ξ (the one cell, wf)      P_rest := emp
     Q      := emp                                        (no L2 residue)
   Born at FILEALLOC under ftable.lock (box_alloc_at with the free-slot
   row's cell, then (c) minting the exclusive unit); the L1 register half
   lives in ftable's payload row for slot k for the box's whole life; the
   L2 half goes to the exclusive owner.  PUBLISH (sys_open, under ip->lock)
   is (e) with the owner-held L2 half -- (C)'s left disjunct: the unit is
   at the birth stamp, presented at the acquiresleep -- then the store,
   then (f), then the returned L2 row is INSERTED into the inode payload's
   append-only set.  fileread/filewrite select their row from that set by
   MEMBERSHIP (a persistent auth-gset fragment on the fd row), (e)/(f)
   under ip->lock.  filedup (c), non-last close (d), LAST CLOSE (a) at
   c = 1 with the gathered unit (mass by F21) under ftable.lock -- the cell
   returns to the free-slot row and the box is abandoned (its L1 half
   dropped; its stale L2 row in the inode payload is garbage, one per
   publish to that inode, ghost only).

   WHY THE SET IS APPEND-ONLY AND KEYED BY THE BOX (§6⁗): the reclaim runs
   under ftable.lock only and can never remove the box's L2 half from the
   inode's payload, and a slot-keyed ghost map cannot be insert-or-replaced
   without the old element.  So each publish inserts a FRESH box's row;
   membership is a core-id fragment; rows are never removed.  Main's
   `fsc_foff i` map of referring files is untouched (it serves the FD_INODE
   fragment, not the box).

   WHAT THIS FILE NEEDS FROM CtxBoxNext AND NOT FROM CtxBox: a one-cell
   client has no second cell for `P_rest_excl` and no natural token; §6⁶ (A)
   removed both obligations because the registers select the arm. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap ufrac gset.
From iris.base_logic.lib Require Import own ghost_var invariants ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import CtxMorphTac.
Require Import Xv6Cameras Xv6G.
Require Import CtxBox.
Require Import IcacheRef.   (* [icfg] -- the two names ride in it (r25 shapes) *)
Require Import FileOffCell.   (* [off_resident] -- the boxed cell; this file builds BEFORE FileInvDefs (r25 shapes) *)

(* F35: the per-inode-slot set is keyed by the WHOLE names record, so a
   member's fragment names exactly the box whose row it selects (keying by
   one gname would give bx_stamps γ' = bx_stamps γ and not γ' = γ -- the
   F6/F13 class).  A record of four gnames is countable. *)
(* [box_names]'s countability, [offboxG] and [offbox_boxG] MOVED to
   Xv6Cameras.v (r25 shapes): [xv6G] bundles the class. *)

(* THE NAMES.  Per inode SLOT the set of published boxes (rows outlive a
   recycle of the slot: dead γ, harmless -- F37), and the file table's
   slot -> box-names agreement map.  Both are [icfg] fields ([icfg_off],
   [icfg_obox]); [off_cfg] is the record every consumer spells. *)
Record off_names := MkOffNames { on_set : nat -> gname; on_obox : gname }.
Definition off_cfg `{ICFG : icfg} : off_names := MkOffNames icfg_off icfg_obox.


Definition offBoxN : namespace := nroot .@ "xv6offbox".

Section OffBox.
  (* the box's own cameras, not the [xv6G] bundle: FileInvDefs binds classes
     one by one and must be able to name these rows (r25 shapes) *)
  Context `{!riscvGS Σ, !kallocG Σ, !lockG Σ, !offboxG Σ}.
  (* FileInvDefs' rows are ambient; the box λs take an explicit ξ *)
  Context `{XI : CurCtx}.

  Implicit Types (on : off_names) (γ : box_names) (k i : nat).

  (* ---- the instance's parameters --------------------------------------- *)
  Definition off_hdr (k : nat) (_ : unit) (ξ : CtxId) : iProp Σ :=
    off_resident (XI := ξ) k.
  Definition off_rest (_ : unit) (_ : CtxId) : iProp Σ := emp%I.

  Global Instance off_hdr_morph k x : CtxMorph (off_hdr k x).
  Proof. rewrite /off_hdr /off_resident. ctx_morph_solve. Qed.
  Global Instance off_rest_morph x : CtxMorph (off_rest x).
  Proof. rewrite /off_rest. apply ctx_morph_const. Qed.
  Global Instance off_hdr_timeless k x ξ : Timeless (off_hdr k x ξ).
  Proof. rewrite /off_hdr /off_resident. apply _. Qed.
  Global Instance off_rest_timeless x ξ : Timeless (off_rest x ξ).
  Proof. rewrite /off_rest. apply _. Qed.

  (* THE BOX of file slot k, at names γ (fresh per publish lifetime) *)
  Definition off_box (k : nat) γ : iProp Σ :=
    CtxBox.is_box (X := unit) off_hdr off_rest (λ _ : nat, emp%I) emp%I (offBoxN .@ k) γ.
  Global Instance off_box_persistent k γ : Persistent (off_box k γ).
  Proof. rewrite /off_box /CtxBox.is_box. apply _. Qed.

  (* ---- registers, per box ------------------------------------------------ *)
  Definition off_cnt γ (c : nat) : iProp Σ := CtxBox.cnt_half (X := unit) γ c.
  Definition off_regd γ (r : slot_reg nat unit) : iProp Σ := CtxBox.slotd_half γ r.
  Definition off_regp γ (s : l2_reg nat) : iProp Σ := CtxBox.slotp_half (X := unit) γ s.

  (* a reference unit / share of the off box: the fd row's stamps at slot k *)
  Definition off_ref_stamps γ k (μ : Qp) : iProp Σ :=
    (∃ m : gmap (nat * nat) ufrac,
       ⌜qsum m = Qp_to_Qc μ⌝ ∗ CtxBox.reference (X := unit) γ k m)%I.

  (* ---- the L1 row: ftable's payload for a slot that has a box ---------- *)
  (* F36/F37: this row lives in fslot's ALLOCATED arm beside a floor row
     `ctx_floor ξ tl` that every ftable.lock release re-folds through `_in`
     (R2) -- which requires is_ftable's λ-flip and a floor slot in
     ftable_res FIRST (L7/L8 move ahead of L6).  fslot's FREE arm keeps the
     cell and has no box.  The publisher's ilock presents ONE Tl := max
     (the inode share's stamp, this box's unit stamp) for its two boxes. *)
  (* the register half, shut and empty, identity = k, its llb; the count is
     f->ref (M !! k's count), beside which the cnt half sits in fslot's arm *)
  Definition off_l1_row γ k (c tl : nat) : iProp Σ :=
    (∃ r : slot_reg nat unit,
       off_regd γ r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗ ⌜sr_ident r = k⌝ ∗
       llb loglen_name (sr_td r) ∗ ⌜(sr_td r ≤ tl)%nat⌝ ∗
       off_cnt γ c)%I.

  (* ---- the L2 side: the inode payload's APPEND-ONLY set of rows --------- *)
  Definition off_set_auth on i (L : gset box_names) : iProp Σ := own (on_set on i) (● L).
  Definition off_member on i γ : iProp Σ := own (on_set on i) (◯ {[ γ ]}).
  Global Instance off_member_persistent on i γ : Persistent (off_member on i γ).
  Proof. rewrite /off_member. apply _. Qed.

  (* one published box's L2 row at rest, with its llb (so the releasesleep
     fold can re-floor every row at the maximum) *)
  Definition off_l2_row γ (s : l2_reg nat) (ξ : CtxId) : iProp Σ :=
    (CtxBox.l2_row (X := unit) γ s ξ ∗ llb loglen_name (lr_tp s))%I.

  (* what rides in inode slot i's sleeplock payload (a conjunct of ic_slp):
     the set authority and every member box's row *)
  Definition off_rows on i (ξ : CtxId) : iProp Σ :=
    (∃ L : gset box_names,
       off_set_auth on i L ∗
       [∗ set] γ ∈ L, ∃ s : l2_reg nat, off_l2_row γ s ξ)%I.
  (* the row is [l2_row]'s morph beside a ξ-constant llb *)
  Global Instance off_l2_row_morph γ (s : l2_reg nat) : CtxMorph (off_l2_row γ s).
  Proof.
    rewrite /off_l2_row.
    apply ctx_morph_sep; [apply CtxBox.l2_row_morph | apply ctx_morph_const].
  Qed.

  Global Instance off_rows_morph on i : CtxMorph (off_rows on i).
  Proof.
    rewrite /off_rows.
    apply ctx_morph_exist. intros L.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepS. intros γ.
    apply ctx_morph_exist. intros s.
    apply off_l2_row_morph.
  Qed.

  (* a member selects its own row and puts it back *)
  Lemma off_rows_take on i γ (ξ : CtxId) :
    off_member on i γ -∗ off_rows on i ξ -∗
    (∃ s, off_l2_row γ s ξ) ∗ (∀ s', off_l2_row γ s' ξ -∗ off_rows on i ξ).
  Proof.
    rewrite /off_rows /off_member /off_set_auth.
    iIntros "Hmem (%L & Hauth & Hset)".
    iDestruct (own_valid_2 with "Hauth Hmem") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply gset_included in Hincl.
    assert (HγL : γ ∈ L) by set_solver.
    iDestruct (big_sepS_delete _ _ _ HγL with "Hset") as "[Hrow Hset]".
    iSplitL "Hrow"; [iExact "Hrow"|].
    iIntros (s') "Hrow'". iExists L. iFrame "Hauth".
    rewrite (big_sepS_delete _ L γ HγL). iFrame "Hset".
    iExists s'. iExact "Hrow'".
  Qed.

  (* the publisher, under ip->lock, appends a fresh box's row *)
  Lemma off_rows_insert on i γ (s : l2_reg nat) (ξ : CtxId) :
    off_rows on i ξ -∗ off_l2_row γ s ξ ==∗ off_rows on i ξ ∗ off_member on i γ.
  Proof.
    rewrite /off_rows /off_member /off_set_auth.
    iIntros "(%L & Hauth & Hset) Hrow".
    iMod (own_update _ _ (● ({[γ]} ∪ L) ⋅ ◯ ({[γ]} ∪ L)) with "Hauth")
      as "[Hauth Hfrag]".
    { apply auth_update_alloc, gset_local_update. set_solver. }
    assert (Hsub : (◯ ({[γ]} : gset box_names) : authR (gsetUR box_names))
                     ≼ ◯ ({[γ]} ∪ L)).
    { apply auth_frag_mono, gset_included. set_solver. }
    iDestruct (own_mono _ _ _ Hsub with "Hfrag") as "#Hmem".
    iModIntro. iFrame "Hmem". iExists ({[γ]} ∪ L). iFrame "Hauth".
    destruct (decide (γ ∈ L)) as [Hin | Hnin].
    - assert (({[γ]} ∪ L) = L) as -> by set_solver. iExact "Hset".
    - rewrite (big_sepS_insert _ L γ Hnin). iFrame "Hset".
      iExists s. iExact "Hrow".
  Qed.

  (* the park's form of the same append: the ghost move happens under the
     fupd, and the ROW is assembled afterwards from the floor the caller
     re-mints at its releasesleep (ctx_floor is persistent, so the wand is
     pure assembly -- which is what lets [off_publish_park] hand the set
     back behind a [ctx_floor ξ T'] wand rather than a fupd). *)
  Lemma off_rows_insert_row on i γ (T' : nat) (ξ : CtxId) :
    off_rows on i ξ -∗
    CtxBox.slotp_half (X := unit) γ (L2Reg T' None) -∗
    llb loglen_name T' ==∗
    (ctx_floor ξ T' -∗ off_rows on i ξ) ∗ off_member on i γ.
  Proof.
    rewrite /off_rows /off_member /off_set_auth.
    iIntros "(%L & Hauth & Hset) Hp #Hllb".
    iMod (own_update _ _ (● ({[γ]} ∪ L) ⋅ ◯ ({[γ]} ∪ L)) with "Hauth")
      as "[Hauth Hfrag]".
    { apply auth_update_alloc, gset_local_update. set_solver. }
    assert (Hsub : (◯ ({[γ]} : gset box_names) : authR (gsetUR box_names))
                     ≼ ◯ ({[γ]} ∪ L)).
    { apply auth_frag_mono, gset_included. set_solver. }
    iDestruct (own_mono _ _ _ Hsub with "Hfrag") as "#Hmem".
    iModIntro. iFrame "Hmem". iIntros "#Hfl".
    iExists ({[γ]} ∪ L). iFrame "Hauth".
    destruct (decide (γ ∈ L)) as [Hin | Hnin].
    - assert (({[γ]} ∪ L) = L) as -> by set_solver. iExact "Hset".
    - rewrite (big_sepS_insert _ L γ Hnin). iFrame "Hset".
      iExists (L2Reg T' None). rewrite /off_l2_row /CtxBox.l2_row /=.
      iFrame "Hp Hfl Hllb". by iPureIntro.
  Qed.

  (* ---- what the fd row's FD_INODE arm carries for the off cell ----------- *)
  (* replaces main's [ioff_ref (fc_ip C) k q]: the box, membership in the
     inode slot's set, and this row's STAMPS MASS μ.  F34 (M-5): μ is NOT
     the fd row's cell fraction q -- a counted reference (one of M !! k's n)
     weighs 1 whatever its q; a share carved from it (fileread's
     `fileread_pay_carve`) weighs its share fraction and the lending parent
     1 − that (inode_ref_short's tie).  Σ over the slot's rows = f->ref. *)
  (* THE SLOT -> BOX TIE (r25 shapes, STATEMENT CHANGE to the skeleton's
     [off_fd_row]): a file slot's fd rows and its table row ([fslot]'s
     allocated arm, [off_l1_row]) must name ONE box, and nothing in the box
     itself relates two names at the same slot.  So the fd side carries a
     fraction of a ghost-map pointsto [k ↦ γ] beside its stamps, the table
     holds the map's authority ([ftable_res]), and the free slot row holds
     the whole pointsto (stale names) so filealloc can update it under
     ftable.lock when it births the next box. *)
  Definition obox_frag on (k : nat) (q : Qp) γ : iProp Σ :=
    (k ↪[on_obox on]{#q} γ)%I.
  Definition obox_full on (k : nat) γ : iProp Σ := (k ↪[on_obox on] γ)%I.
  Definition obox_auth on (B : gmap nat box_names) : iProp Σ :=
    ghost_map_auth (on_obox on) 1 B.
  Definition off_fd_row on (i k : nat) (μ : Qp) : iProp Σ :=
    (∃ γ : box_names,
       off_box k γ ∗ obox_frag on k μ γ ∗ off_member on i γ ∗ off_ref_stamps γ k μ)%I.

  (* THE ROWS' CONTEXT-FREE FORM (r25 shapes; SKELETON statements, proofs in
     lane (ii)).  What an [_in] release of ip->lock holds: every row's L2
     register half with its park stamp bounded by [T], and [llb T] so the
     release can present one lower bound for the combined maximum
     (reviewer 2's correction 2: the register's [lr_tp] cannot be raised,
     so the fold takes one floor at [T ≥ max] and weakens per row by
     [TsoCtx.ctx_floor_le]). *)
  Definition off_rows_dep on i (T : nat) : iProp Σ :=
    (∃ L : gset box_names,
       off_set_auth on i L ∗ llb loglen_name T ∗
       [∗ set] γ ∈ L, ∃ s : l2_reg nat,
         off_regp γ s ∗ ⌜lr_hold s = None⌝ ∗ llb loglen_name (lr_tp s) ∗
         ⌜(lr_tp s ≤ T)%nat⌝)%I.
  Lemma off_rows_fold on i (T : nat) (ξ : CtxId) :
    off_rows_dep on i T ∗ ctx_floor ξ T ⊢ off_rows on i ξ.
  Proof. (* SKELETON r25 (lane ii): per row, [ctx_floor_le] from T down to lr_tp *) Admitted.
  Lemma off_rows_to_dep on i (ξ : CtxId) :
    off_rows on i ξ -∗ ∃ T : nat, off_rows_dep on i T.
  Proof. (* SKELETON r25 (lane ii): T := the rows' maximum, llb by the maximum lemma *) Admitted.

  (* ================================================================== *)
  (*  THE SITES                                                            *)
  (* ================================================================== *)

  (* filealloc, under ftable.lock: the free-slot row's cell becomes a box
     (fresh names, box_alloc_at) and (c) mints the exclusive unit.  Out: the
     L1 row's pieces for ftable's payload (c = 1), the owner's L2 half at
     {| 0; None |}, the owner's unit, the persistent box. *)
  (* STATEMENT CHANGE (L6 skeleton→proof): two premises added.  (1) the
     cell is presented AT ξ ([off_resident (XI := ξ) k]) -- the skeleton
     wrote it at the ambient context, but [box_alloc_at] deposits the
     bundle out of the ξ the caller runs at, and nothing moves a cell
     between two unrelated contexts.  Every other lemma here already
     spells the cell at ξ.  (2) [↑(offBoxN .@ k) ⊆ E], which is what the
     (c) step (box_ref_incr, minting the birth unit) needs to open the box
     it has just allocated.  (3) the cnt ghost is pinned at the box's own
     [ghost_varG] instance ([kalloc_count_inG], which is what [offbox_boxG]
     sets [box_cntG] to), exactly as BioInv and IcacheEscrow spell it: with
     the instance left to search the premise is a DIFFERENT camera from the
     one [box_alloc_at] consumes. *)
  Lemma off_filealloc `{CID : RiscvLang.CpuId} k γ (ξ : CtxId) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    CtxBox.stamps_auth (X := unit) γ ∅ -∗
    ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γ) 1 0%nat -∗
    ghost_var (bx_slotd γ) 1 (inhabitant : slot_reg nat unit) -∗
    ghost_var (bx_slotp γ) 1 (inhabitant : l2_reg nat) -∗
    own_context ξ -∗
    off_resident (XI := ξ) k ={E}=∗
    own_context ξ ∗ off_box k γ ∗
    ∃ T_boot : nat,
      off_regd γ (SlotReg T_boot false k None) ∗ llb loglen_name T_boot ∗
      off_cnt γ 1 ∗
      off_regp γ (L2Reg 0 None) ∗
      off_ref_stamps γ k 1%Qp.
  Proof. (* box_alloc_at, then box_ref_incr (the unit at T_boot) *)
    intros HE.
    rewrite /off_box /off_regd /off_cnt /off_regp /off_ref_stamps.
    iIntros "Hst Hc Hd Hp Hrun Hcell".
    iMod (CtxBox.box_alloc_at off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k E with "Hst Hc Hd Hp Hrun [Hcell]")
      as "(Hrun & %Tb & #Hbx & Hrd & #Hllb & Hcnt & Hrp)".
    { iExists tt. rewrite /off_rest. iSplitL; [iExact "Hcell"|done]. }
    iMod (CtxBox.box_ref_incr off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ (SlotReg Tb false k None) 0 E HE eq_refl
            with "Hbx Hrd Hcnt") as "(Hrd & Hcnt & %T & Href)".
    iModIntro. iFrame "Hrun Hbx". iExists Tb. iFrame "Hrd Hllb Hcnt Hrp".
    iExists {[ (k, T) := 1%Qp ]}.
    iSplitR; [iPureIntro; by rewrite qsum_singleton|].
    iExact "Href".
  Qed.

  (* sys_open's PUBLISH, under ip->lock, ftable.lock released: (e) with the
     owner-held L2 half -- cover (C)-left, the unit at the birth stamp
     presented at the acquiresleep (Kt ≥ its stamp), lr_tp = 0 needs no
     floor -- the cell in hand for `f->off = 0`, then (f), then the returned
     row is appended to inode i's set.  Stated as the two box steps. *)
  Lemma off_publish_checkout `{CID : RiscvLang.CpuId} k γ (ξ : CtxId)
      (m : gmap (nat * nat) ufrac) (Kt : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    qsum m = Qp_to_Qc 1 -> (max_stamp m ≤ Kt)%nat ->
    off_box k γ -∗ own_context ξ -∗ ctx_floor ξ Kt -∗
    CtxBox.reference (X := unit) γ k m -∗
    off_regp γ (L2Reg 0 None) ={E}=∗
    own_context ξ ∗ off_resident (XI := ξ) k ∗ CtxBox.l2_hold (X := unit) γ k m.
  Proof. (* box_checkout at Q := emp, Kp := 0 *)
    intros HE Hq HKt. rewrite /off_box /off_regp.
    iIntros "#Hbox Hrun #Hflt Href Hrp".
    assert (Hh0 : lr_hold (L2Reg 0 None : l2_reg nat) = None) by reflexivity.
    assert (Hp0 : (lr_tp (L2Reg 0 None : l2_reg nat) ≤ 0)%nat) by (simpl; lia).
    iMod (CtxBox.box_checkout off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k m (L2Reg 0 None) Kt 0 E HE Hh0 HKt Hp0
            with "Hbox Hrun Hflt [] Href [] Hrp") as "(Hrun & Hbun & Hhold)".
    { iApply ctx_floor_0. }
    { done. }
    iDestruct "Hbun" as (x) "[Hcell _]".
    iModIntro. iFrame "Hrun Hhold". iExact "Hcell".
  Qed.

  Lemma off_publish_park `{CID : RiscvLang.CpuId} on i k γ (ξ : CtxId)
      (m : gmap (nat * nat) ufrac) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    off_box k γ -∗ own_context ξ -∗
    off_resident (XI := ξ) k -∗
    CtxBox.l2_hold (X := unit) γ k m -∗
    off_rows on i ξ ={E}=∗
    own_context ξ ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum m⌝ ∗
      CtxBox.reference (X := unit) γ k {[ (k, T') := q ]} ∗
      llb loglen_name T' ∗
      (* the row goes into the inode payload at the fresh box; the caller
         re-floors the set at its _in releasesleep *)
      (ctx_floor ξ T' -∗ off_rows on i ξ) ∗ off_member on i γ.
  Proof. (* box_park at Q := emp, then off_rows_insert *)
    intros HE. rewrite /off_box.
    iIntros "#Hbox Hrun Hcell Hhold Hrows".
    iMod (CtxBox.box_park off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k m E HE with "Hbox Hrun [Hcell] Hhold")
      as "(Hrun & _ & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    { iExists tt. rewrite /off_rest. iSplitL; [iExact "Hcell"|done]. }
    iMod (off_rows_insert_row on i γ T' ξ with "Hrows Hrp Hllb")
      as "[Hback #Hmem]".
    iModIntro. iFrame "Hrun". iExists T', q.
    iSplitR; [iPureIntro; exact Hq|].
    iFrame "Href Hllb Hback Hmem".
  Qed.

  (* fileread / filewrite, under ip->lock: select the row by membership,
     (e), the cell in hand, (f), the row back (re-floored at the fold) *)
  Lemma off_read_checkout `{CID : RiscvLang.CpuId} on i k γ (ξ : CtxId)
      (m : gmap (nat * nat) ufrac) (Kt Kp : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    (max_stamp m ≤ Kt)%nat ->
    off_box k γ -∗ own_context ξ -∗ ctx_floor ξ Kt -∗ ctx_floor ξ Kp -∗
    off_member on i γ -∗
    CtxBox.reference (X := unit) γ k m -∗
    (* the row, taken from the inode payload's set: its floor is Kp *)
    (∃ s : l2_reg nat, ⌜lr_hold s = None⌝ ∗ ⌜(lr_tp s ≤ Kp)%nat⌝ ∗ off_regp γ s) ={E}=∗
    own_context ξ ∗ off_resident (XI := ξ) k ∗ CtxBox.l2_hold (X := unit) γ k m.
  Proof. (* box_checkout at Q := emp, the row's own floor as Kp *)
    intros HE HKt. rewrite /off_box /off_regp.
    iIntros "#Hbox Hrun #Hflt #Hflp #Hmem Href (%s & %Hh & %Htp & Hrp)".
    iMod (CtxBox.box_checkout off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k m s Kt Kp E HE Hh HKt Htp
            with "Hbox Hrun Hflt Hflp Href [] Hrp") as "(Hrun & Hbun & Hhold)".
    { done. }
    iDestruct "Hbun" as (x) "[Hcell _]".
    iModIntro. iFrame "Hrun Hhold". iExact "Hcell".
  Qed.

  Lemma off_read_park `{CID : RiscvLang.CpuId} k γ (ξ : CtxId)
      (m : gmap (nat * nat) ufrac) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    off_box k γ -∗ own_context ξ -∗
    off_resident (XI := ξ) k -∗
    CtxBox.l2_hold (X := unit) γ k m ={E}=∗
    own_context ξ ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum m⌝ ∗
      off_regp γ (L2Reg T' None) ∗
      CtxBox.reference (X := unit) γ k {[ (k, T') := q ]} ∗
      llb loglen_name T'.
  Proof. (* box_park at Q := emp *)
    intros HE. rewrite /off_box /off_regp.
    iIntros "#Hbox Hrun Hcell Hhold".
    iMod (CtxBox.box_park off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k m E HE with "Hbox Hrun [Hcell] Hhold")
      as "(Hrun & _ & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    { iExists tt. rewrite /off_rest. iSplitL; [iExact "Hcell"|done]. }
    iModIntro. iFrame "Hrun". iExists T', q.
    iSplitR; [iPureIntro; exact Hq|].
    iFrame "Hrp Href Hllb".
  Qed.

  (* filedup, under ftable.lock: (c) *)
  (* STATEMENT CHANGE (L6 skeleton→proof): [sr_ident r = k] added.  (c)
     mints the unit at the REGISTER's identity ([box_ref_incr] returns
     [reference γ (sr_ident r) …]), so the row it hands back is keyed at k
     only when the register says k.  The L1 row (off_l1_row) carries
     exactly this equation, so every call site has it. *)
  Lemma off_dup k γ (r : slot_reg nat unit) (c : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E -> sr_win r = false -> sr_ident r = k ->
    off_box k γ -∗ off_regd γ r -∗ off_cnt γ (S c) ={E}=∗
    off_regd γ r ∗ off_cnt γ (S (S c)) ∗ off_ref_stamps γ k 1%Qp.
  Proof.
    intros HE Hw Hid.
    rewrite /off_box /off_regd /off_cnt /off_ref_stamps.
    iIntros "#Hbox Hrd Hcnt".
    iMod (CtxBox.box_ref_incr off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ r (S c) E HE Hw with "Hbox Hrd Hcnt")
      as "(Hrd & Hcnt & %T & Href)".
    iModIntro. iFrame "Hrd Hcnt". rewrite -Hid.
    iExists {[ (sr_ident r, T) := 1%Qp ]}.
    iSplitR; [iPureIntro; by rewrite qsum_singleton|].
    iExact "Href".
  Qed.

  (* fileclose, non-last, under ftable.lock: (d) *)
  (* STATEMENT CHANGE (L6 skeleton→proof): [sr_ident r = k] added, for the
     same reason as (c) -- [box_ref_decr] re-stamps the register AT ITS OWN
     identity, so the returned [SlotReg td' false k (sr_x r)] is the box's
     register only when the register's identity is k. *)
  Lemma off_close k γ (r : slot_reg nat unit) (c : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E -> sr_win r = false -> sr_ident r = k ->
    off_box k γ -∗ off_regd γ r -∗ llb loglen_name (sr_td r) -∗ off_cnt γ (S (S c)) -∗
    off_ref_stamps γ k 1%Qp ={E}=∗
    ∃ td' : nat, ⌜(sr_td r ≤ td')%nat⌝ ∗
      off_regd γ (SlotReg td' false k (sr_x r)) ∗ off_cnt γ (S c) ∗ llb loglen_name td'.
  Proof.
    intros HE Hw Hid.
    rewrite /off_box /off_regd /off_cnt /off_ref_stamps.
    iIntros "#Hbox Hrd #Hllb Hcnt (%m & %Hq & Href)".
    assert (Hq1 : qsum m = nat_Qc 1).
    { rewrite Hq Qp_to_Qc_1 nat_Qc_1. reflexivity. }
    iMod (CtxBox.box_ref_decr off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ r (S c) k m E HE Hw Hq1
            with "Hbox Hrd Hllb Hcnt Href") as "(Hrd & Hcnt & #Hllb')".
    iModIntro. iExists (Nat.max (sr_td r) (max_stamp m)).
    iSplitR; [iPureIntro; lia|].
    rewrite -Hid. iFrame "Hrd Hcnt Hllb'".
  Qed.

  (* fileclose, LAST reference, under ftable.lock, no inode lock: (a) at
     c = 1 with the gathered unit (its stamps re-minted by every fileread
     park; R1 at fileclose's ftable acquire presents their max), the cell
     comes back for the free-slot row, and the box is abandoned. *)
  Lemma off_reclaim `{CID : RiscvLang.CpuId} k γ (ξ : CtxId) (r : slot_reg nat unit)
      (m : gmap (nat * nat) ufrac) (Kd Kt : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    sr_win r = false -> sr_ident r = k -> (sr_td r ≤ Kd)%nat ->
    qsum m = Qp_to_Qc 1 -> (max_stamp m ≤ Kt)%nat ->
    off_box k γ -∗ own_context ξ -∗ ctx_floor ξ Kd -∗ ctx_floor ξ Kt -∗
    off_regd γ r -∗ off_cnt γ 1 -∗
    CtxBox.reference (X := unit) γ k m ={E}=∗
    own_context ξ ∗ off_resident (XI := ξ) k.
    (* the window stays open forever: the box is dead; its L1 half and cnt
       half are dropped by the caller (affine) *)
  Proof. (* box_withdraw_L1 at Q := emp; drop the returned register half *)
    intros HE Hw Hid HKd Hq HKt.
    rewrite /off_box /off_regd /off_cnt.
    iIntros "#Hbox Hrun #Hfld #Hflt Hrd Hcnt Href".
    assert (Hq1 : qsum m = nat_Qc 1).
    { rewrite Hq Qp_to_Qc_1 nat_Qc_1. reflexivity. }
    iDestruct "Href" as "(%Hne & %Hkey & Hfr & #HllbM)".
    iMod (CtxBox.box_withdraw_L1 off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ r 1 m Kd Kt E HE Hw Hq1 HKd HKt
            with "Hbox Hrun Hfld Hflt HllbM Hrd Hcnt Hfr []")
      as "(Hrun & Hcnt & %x0 & %T0 & %HT0 & Hrd & Hhdr)".
    { done. }
    iModIntro. iFrame "Hrun". rewrite -Hid. iExact "Hhdr".
  Qed.

End OffBox.
