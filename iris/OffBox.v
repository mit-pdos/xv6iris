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
Require Import TsoGhost.
Require Import TsoCtx.
Require Import CtxMorphTac.
Require Import Xv6Cameras.
Require Import CtxBox.
Require Import RiscvModelBytes.   (* [pa_add] -- the free bytes of the last close (item 24) *)
Require Import IcacheRef.   (* [icfg] -- the two names ride in it (r25 shapes) *)
Require Import FileOffCell.   (* [off_resident] -- the boxed cell; this file builds BEFORE FileInvDefs (r25 shapes) *)

(* F35: the per-inode-slot set is keyed by the WHOLE names record, so a
   member's fragment names exactly the box whose row it selects (keying by
   one gname would give bx_stamps γ' = bx_stamps γ and not γ' = γ -- the
   F6/F13 class).  A record of four gnames is countable. *)
(* [box_names]'s countability, [offboxG] and [offbox_boxG] MOVED to
   Xv6Cameras.v (r25 shapes): [xv6G] bundles the class. *)

(* THE NAMES.  Per inode SLOT the set of published boxes (rows outlive a
   recycle of the slot: dead γ, harmless -- F37), an [icfg] field
   ([icfg_off]); [off_cfg] is the record every consumer spells.  The fd
   names ITS box through [FileInvDefs.fpnames.fp_obox] (plan §9 item 24).
   SUCCESSIVE BOXES OF ONE SLOT SHARE [offBoxN .@ k] (item 25 note 5): a
   slot's box is born at each publish with fresh names and left OUT_L1 at
   its last close; the stale invariants are not a leak -- no proof opens
   two off boxes at once and the collection never opens one. *)
Record off_names := MkOffNames { on_set : nat -> gname }.
Definition off_cfg `{ICFG : icfg} : off_names := MkOffNames icfg_off.


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
  (* peel the connectives and let [apply _] see only the LEAVES: a single
     [apply _] over the [∃ ∗ ⌜⌝] tower unifies up to delta, walks straight
     through [↦₄]'s own instance into the byte tower and backtracks over the
     lot (claude-notes/optimization.md, "prove a big Timeless/Persistent
     instance STRUCTURALLY").  This one instance was over half of the file. *)
  Proof.
    rewrite /off_hdr /off_resident.
    apply bi.exist_timeless; intros ?.
    apply bi.sep_timeless; apply _.
  Qed.
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
  (* NO L1 ROW (plan §9 item 24): the cell is at the visibility-free tier
     whenever no one needs it, so the table holds no box ghost. *)

  (* ---- the L2 side: the inode payload's APPEND-ONLY set of rows --------- *)
  (* the share splits and joins by mass (item 24: "shares split by mass") --
     [IcacheRef.ic_ref_stamps_split]'s proof over this box's reference *)
  Lemma off_ref_stamps_mass_eq γ k (μ1 μ2 : Qp) :
    μ1 = μ2 -> off_ref_stamps γ k μ1 -∗ off_ref_stamps γ k μ2.
  Proof. intros ->. iIntros "$". Qed.
  Lemma off_ref_stamps_join γ k (μ1 μ2 : Qp) :
    off_ref_stamps γ k μ1 -∗ off_ref_stamps γ k μ2 -∗ off_ref_stamps γ k (μ1 + μ2)%Qp.
  Proof.
    rewrite /off_ref_stamps.
    iIntros "(%m1 & %Hq1 & H1) (%m2 & %Hq2 & H2)".
    iDestruct (CtxBox.reference_join with "H1 H2") as "H".
    iExists (m1 ⋅ m2). iFrame "H". iPureIntro.
    rewrite CtxBox.qsum_op Hq1 Hq2 Qp.to_Qc_inj_add. reflexivity.
  Qed.
  Lemma off_ref_stamps_split γ k (μ1 μ2 : Qp) :
    off_ref_stamps γ k (μ1 + μ2)%Qp -∗ off_ref_stamps γ k μ1 ∗ off_ref_stamps γ k μ2.
  Proof.
    rewrite /off_ref_stamps. iIntros "(%m & %Hq & H)".
    iDestruct (CtxBox.reference_split _ _ _ (μ1 / (μ1 + μ2))%Qp (μ2 / (μ1 + μ2))%Qp
                 with "H") as "[H1 H2]".
    { rewrite -Qp.div_add_distr Qp.div_diag. reflexivity. }
    iSplitL "H1".
    - iExists (CtxBox.mscale (μ1 / (μ1 + μ2))%Qp m). iFrame "H1". iPureIntro.
      rewrite CtxBox.qsum_mscale Hq -Qp.to_Qc_inj_mul Qp.mul_div_r. reflexivity.
    - iExists (CtxBox.mscale (μ2 / (μ1 + μ2))%Qp m). iFrame "H2". iPureIntro.
      rewrite CtxBox.qsum_mscale Hq -Qp.to_Qc_inj_mul Qp.mul_div_r. reflexivity.
  Qed.

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
  (* NO TIE, NO UNIT (item 24): the fd's reference is a SHARE at the fd's
     fraction ([FileInvDefs.off_fd]), the box named by [fp_obox]. *)

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
  Proof.
    rewrite /off_rows_dep /off_rows /off_l2_row /CtxBox.l2_row /off_regp.
    iIntros "[(%L & Hauth & #HllbT & Hset) #Hfl]".
    iExists L. iFrame "Hauth".
    iApply (big_sepS_impl with "Hset").
    iIntros "!#" (γ Hγ) "(%s & Hp & %Hh & #Hllbs & %Hle)".
    iExists s. iFrame "Hp Hllbs". iSplitR; [by iPureIntro|].
    iApply (TsoCtx.ctx_floor_le with "Hfl"). exact Hle.
  Qed.

  (* the rows' maximum, by [set_ind_L]: each row's llb joins into one bound
     ([llb_max]) and every row's [lr_tp] stays under it *)
  Lemma off_rows_bound (L : gset box_names) (ξ : CtxId) :
    ([∗ set] γ ∈ L, ∃ s : l2_reg nat, off_l2_row γ s ξ) -∗
    ∃ T : nat, llb loglen_name T ∗
      [∗ set] γ ∈ L, ∃ s : l2_reg nat,
        off_regp γ s ∗ ⌜lr_hold s = None⌝ ∗ llb loglen_name (lr_tp s) ∗
        ⌜(lr_tp s ≤ T)%nat⌝.
  Proof.
    rewrite /off_l2_row /CtxBox.l2_row /off_regp.
    induction L as [|γ L Hγ IH] using set_ind_L.
    - iIntros "_". iExists 0%nat. rewrite !big_sepS_empty.
      iSplitR; [iApply llb_0 | done].
    - iIntros "Hset". rewrite big_sepS_insert; [|exact Hγ].
      iDestruct "Hset" as "[Hrow Hset]".
      iDestruct "Hrow" as (s) "[(Hp & %Hh & _) #Hllbs]".
      iDestruct (IH with "Hset") as (T) "[#HllbT Hset]".
      iExists (Nat.max (lr_tp s) T).
      iSplitR; [iApply (llb_max with "Hllbs HllbT")|].
      rewrite big_sepS_insert; [|exact Hγ].
      iSplitL "Hp".
      + iExists s. iFrame "Hp Hllbs". iPureIntro. split; [exact Hh | lia].
      + iApply (big_sepS_impl with "Hset").
        iIntros "!#" (γ' Hγ') "(%s' & Hp' & %Hh' & #Hl' & %Hle')".
        iExists s'. iFrame "Hp' Hl'". iPureIntro. split; [exact Hh' | lia].
  Qed.

  (* THE REMAINDER WITH ONE ROW TAKEN OUT, IN DEP FORM (plan §9 item 36,
     pre-empt 1): what a reader holds while its own box is checked out.  The
     set authority still names the taken box; its row is re-inserted by
     [off_rows_dep_insert] at whatever stamp the park gave it -- no floor
     needed, which is the point: after a park the parker has none. *)
  Definition off_rows_dep_but on i (γ : box_names) (T : nat) : iProp Σ :=
    (∃ L : gset box_names,
       ⌜γ ∈ L⌝ ∗ off_set_auth on i L ∗ llb loglen_name T ∗
       [∗ set] γ' ∈ L ∖ {[ γ ]}, ∃ s : l2_reg nat,
         off_regp γ' s ∗ ⌜lr_hold s = None⌝ ∗ llb loglen_name (lr_tp s) ∗
         ⌜(lr_tp s ≤ T)%nat⌝)%I.

  Lemma off_rows_take_dep on i γ (ξ : CtxId) :
    off_member on i γ -∗ off_rows on i ξ -∗
    (∃ s, off_l2_row γ s ξ) ∗ ∃ T : nat, off_rows_dep_but on i γ T.
  Proof.
    rewrite /off_rows /off_member /off_rows_dep_but /off_set_auth.
    iIntros "Hmem (%L & Hauth & Hset)".
    iDestruct (own_valid_2 with "Hauth Hmem") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply gset_included in Hincl.
    assert (HγL : γ ∈ L) by set_solver.
    iDestruct (big_sepS_delete _ _ _ HγL with "Hset") as "[Hrow Hset]".
    iSplitL "Hrow"; [iExact "Hrow"|].
    iDestruct (off_rows_bound with "Hset") as (T) "[#HllbT Hset]".
    iExists T, L. iFrame "Hauth HllbT Hset". iPureIntro. exact HγL.
  Qed.

  Lemma off_rows_dep_insert on i γ (T : nat) (s' : l2_reg nat) :
    lr_hold s' = None ->
    off_rows_dep_but on i γ T -∗ off_regp γ s' -∗ llb loglen_name (lr_tp s') -∗
    off_rows_dep on i (Nat.max T (lr_tp s')).
  Proof.
    iIntros (Hh) "(%L & %HγL & Hauth & #HllbT & Hset) Hrp #Hllbs".
    rewrite /off_rows_dep. iExists L. iFrame "Hauth".
    iSplitR; [iApply (llb_max with "HllbT Hllbs")|].
    rewrite (big_sepS_delete _ L γ HγL).
    iSplitL "Hrp".
    { iExists s'. iFrame "Hrp Hllbs". iPureIntro. split; [exact Hh | lia]. }
    iApply (big_sepS_impl with "Hset"). iIntros "!>" (γ' _) "(%s & Hp & %Hh' & #Hl & %Hb)".
    iExists s. iFrame "Hp Hl". iPureIntro. split; [exact Hh' | lia].
  Qed.

  Lemma off_rows_to_dep on i (ξ : CtxId) :
    off_rows on i ξ -∗ ∃ T : nat, off_rows_dep on i T.
  Proof.
    rewrite /off_rows /off_rows_dep.
    iIntros "(%L & Hauth & Hset)".
    iDestruct (off_rows_bound with "Hset") as (T) "[#HllbT Hset]".
    iExists T, L. iFrame "Hauth HllbT Hset".
  Qed.

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

  (* sys_open's PUBLISH, under ip->lock, ftable.lock released: (e) with the
     owner-held L2 half -- cover (C)-left, the unit at the birth stamp
     presented at the acquiresleep (Kt ≥ its stamp), lr_tp = 0 needs no
     floor -- the cell in hand for `f->off = 0`, then (f), then the returned
     row is appended to inode i's set.  Stated as the two box steps. *)

  (* THE BIRTH, AT THE PUBLISH (item 24, note 4's order): sys_open has just
     stored [f->off = 0] over the free word ([wp_store_s_sconf_free_gen],
     re-minting the cell at its context) under ip->lock at [ref = 1]; then
     [box_alloc_at] deposits the cell (the creator never absorbs it -- the
     self-absorb line holds), (c) mints the reference at mass 1, and the L2
     row is inserted into inode [i]'s set.  What comes out is exactly
     [FileInvDefs.off_fd]'s pieces at [q = 1]: the two register halves, the
     share, membership, the handle. *)
  Lemma off_publish_park `{CID : RiscvLang.CpuId} on i k γ (ξ : CtxId) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    CtxBox.stamps_auth (X := unit) γ ∅ -∗
    ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γ) 1 0%nat -∗
    ghost_var (bx_slotd γ) 1 (inhabitant : slot_reg nat unit) -∗
    ghost_var (bx_slotp γ) 1 (inhabitant : l2_reg nat) -∗
    own_context ξ -∗
    off_resident (XI := ξ) k -∗
    off_rows on i ξ ={E}=∗
    own_context ξ ∗ off_box k γ ∗
    ∃ (T0 T : nat),
      off_regd γ (SlotReg T0 false k None) ∗ llb loglen_name T0 ∗
      off_cnt γ 1 ∗
      CtxBox.reference (X := unit) γ k {[ (k, T) := 1%Qp ]} ∗
      off_member on i γ ∗
      off_rows on i ξ.
  Proof. (* box_alloc_at (the deposit), box_ref_incr (the birth share),
            off_rows_insert_row at [L2Reg 0 None] -- whose floor the lemma
            discharges itself with [ctx_floor_0], so what comes out is the
            next link's premise (item 31 (a)) *)
    intros HE.
    rewrite /off_box /off_regd /off_cnt /off_regp.
    iIntros "Hst Hc Hd Hp Hrun Hcell Hrows".
    iMod (CtxBox.box_alloc_at off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ ξ k E with "Hst Hc Hd Hp Hrun [Hcell]")
      as "(Hrun & %Tb & #Hbx & Hrd & #Hllb & Hcnt & Hrp)".
    { iExists tt. rewrite /off_rest. iSplitL; [iExact "Hcell"|done]. }
    iMod (CtxBox.box_ref_incr off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ (SlotReg Tb false k None) 0 E HE eq_refl
            with "Hbx Hrd Hcnt") as "(Hrd & Hcnt & %T & Href)".
    iMod (off_rows_insert_row on i γ 0 ξ with "Hrows Hrp []") as "[Hfold #Hmem]".
    { iApply llb_0. }
    iModIntro. iFrame "Hrun Hbx". iExists Tb, T.
    iFrame "Hrd Hllb Hcnt Href Hmem".
    iApply "Hfold". iApply TsoCtx.ctx_floor_0.
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

  (* fileclose, non-last, under ftable.lock: (d) *)
  (* STATEMENT CHANGE (L6 skeleton→proof): [sr_ident r = k] added, for the
     same reason as (c) -- [box_ref_decr] re-stamps the register AT ITS OWN
     identity, so the returned [SlotReg td' false k (sr_x r)] is the box's
     register only when the register's identity is k. *)

  (* fileclose, LAST reference, under ftable.lock, no inode lock: (a) at
     c = 1 with the gathered unit (its stamps re-minted by every fileread
     park; R1 at fileclose's ftable acquire presents their max), the cell
     comes back for the free-slot row, and the box is abandoned. *)

  (* THE LAST CLOSE (item 24; ruled R2): with the fd's whole share in hand
     (q = 1: its own fraction plus the remainder from [file_rest]), the
     closer drops the parked header to the free tier INSIDE the box at ξb
     by [CtxBox.box_withdraw_L1_free] -- nothing absorbed, no floor, no
     [own_context]; the box is left OUT_L1 with the whole mass inside (a
     stale reader would hold mass > 0 beside it: refuted by Σ).  What comes
     out is the free word, which the retype to FD_NONE puts in the free row. *)
  Lemma off_last_close k γ (T0 : nat) (m : gmap (nat * nat) ufrac) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E ->
    qsum m = Qp_to_Qc 1 ->
    off_box k γ -∗
    off_regd γ (SlotReg T0 false k None) -∗
    off_cnt γ 1 -∗
    CtxBox.reference (X := unit) γ k m ={E}=∗
    off_cnt γ 1 ∗
    ([∗ list] j ∈ seq 0 4, TsoCtx.mem_free (pa_add (a_foff k) j) (DfracOwn 1)).
  Proof. (* [box_withdraw_L1_free] at [Qc := emp], [Q1 1 = emp]; the hook is
            the plain entailment [off_resident (XI := ξb) k ⊢ the four free
            bytes] -- one [ctx_pointsto_free] per byte, at the box's own
            context, with no floor and no [own_context] *)
    intros HE Hq. rewrite /off_box /off_regd /off_cnt.
    iIntros "#Hbox Hrd Hcnt Href".
    iDestruct "Href" as "(%Hne & %Hkeyed & HfD & #HllbD)".
    assert (Hq1 : qsum m = CtxBox.nat_Qc 1).
    { rewrite Hq CtxBox.nat_Qc_1. exact Qp_to_Qc_1. }
    assert (Hhook : ∀ (x : unit) (ξb : CtxId),
              emp ∗ off_hdr k x ξb
              ={E ∖ ↑(offBoxN .@ k)}=∗
              ([∗ list] j ∈ seq 0 4, TsoCtx.mem_free (pa_add (a_foff k) j) (DfracOwn 1))
              ∗ emp).
    { intros x ξb. rewrite /off_hdr /off_resident.
      iIntros "[_ (%v & Hw & _)]".
      rewrite TsoCtx.ctx_word4_pointsto_unfold.
      iDestruct "Hw" as "[_ Hbytes]".
      iModIntro. iSplitL; [| done].
      iApply (big_sepL_impl with "Hbytes").
      iIntros "!#" (j y Hy) "Hb". iApply (TsoCtx.ctx_pointsto_free with "Hb"). }
    iMod (CtxBox.box_withdraw_L1_free off_hdr off_rest (λ _ : nat, emp%I) emp%I
            (offBoxN .@ k) γ (SlotReg T0 false k None) 1 m emp%I
            ([∗ list] j ∈ seq 0 4, TsoCtx.mem_free (pa_add (a_foff k) j) (DfracOwn 1))%I
            E HE eq_refl Hq1 Hhook
            with "Hbox Hrd Hcnt HfD HllbD []") as "(Hcnt & Hfree & _)".
    { done. }
    iModIntro. iFrame "Hcnt Hfree".
  Qed.
End OffBox.
