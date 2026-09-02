(* OffBox.v -- THE OFF BOX: f->off under the transit-box law (tso-cutover
   endgame §6‴ P4 as corrected, §6⁗, §6⁵ ruling item 3, §6⁶ (A)), AS A
   TYPE-CHECKED SKELETON over CtxBox.  Proofs [Admitted].

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
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import SleepLock.
Require Import Xv6Cameras Xv6G.
Require Import CtxBox.
Require Import FileInvDefs.

(* F35: the per-inode-slot set is keyed by the WHOLE names record, so a
   member's fragment names exactly the box whose row it selects (keying by
   one gname would give bx_stamps γ' = bx_stamps γ and not γ' = γ -- the
   F6/F13 class).  A record of four gnames is countable. *)
Global Instance box_names_eq_dec : EqDecision box_names.
Proof. solve_decision. Defined.
Global Instance box_names_countable : Countable box_names.
Proof.
  apply (inj_countable'
           (λ b, (bx_stamps b, bx_cnt b, bx_slotd b, bx_slotp b))
           (λ t, BoxNames t.1.1.1 t.1.1.2 t.1.2 t.2)).
  by intros [].
Qed.

(* ---- cameras (to Xv6Cameras §15 at R4b) ----------------------------- *)
Class offboxG (Σ : gFunctors) := OffboxG {
  offbox_stampsG :: inG Σ (stampsR nat);
  offbox_slotdG  :: ghost_varG Σ (slot_reg nat unit);
  offbox_slotpG  :: ghost_varG Σ (l2_reg nat);
  (* the per-inode append-only set of published off boxes *)
  offbox_setG    :: inG Σ (authR (gsetUR box_names));
}.
Global Instance offbox_boxG {Σ} `{!offboxG Σ} `{!kallocG Σ} : boxG nat unit Σ :=
  {| box_stampsG := offbox_stampsG; box_cntG := kalloc_count_inG;
     box_slotdG := offbox_slotdG; box_slotpG := offbox_slotpG |}.

(* the per-inode-SLOT set gnames (a fscfg field at R4b; a parameter here).
   Per slot, not per inode: rows outlive a recycle of the slot (dead γ,
   harmless -- F37). *)
Record off_names := MkOffNames { on_set : nat -> gname }.

Definition offBoxN : namespace := nroot .@ "xv6offbox".

Section OffBox.
  Context `{!riscvGS Σ, !xv6G Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !offboxG Σ}.
  (* FileInvDefs' rows are ambient; the box λs take an explicit ξ *)
  Context `{XI : CurCtx}.

  Implicit Types (on : off_names) (γ : box_names) (k i : nat).

  (* ---- the instance's parameters --------------------------------------- *)
  Definition off_hdr (k : nat) (_ : unit) (ξ : CtxId) : iProp Σ :=
    off_resident (XI := ξ) k.
  Definition off_rest (_ : unit) (_ : CtxId) : iProp Σ := emp%I.

  Global Instance off_hdr_morph k x : CtxMorph (off_hdr k x).
  Proof. Admitted.
  Global Instance off_rest_morph x : CtxMorph (off_rest x).
  Proof. rewrite /off_rest. apply ctx_morph_const. Qed.
  Global Instance off_hdr_timeless k x ξ : Timeless (off_hdr k x ξ).
  Proof. Admitted.
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
  Global Instance off_rows_morph on i : CtxMorph (off_rows on i).
  Proof. Admitted.

  (* a member selects its own row and puts it back *)
  Lemma off_rows_take on i γ (ξ : CtxId) :
    off_member on i γ -∗ off_rows on i ξ -∗
    (∃ s, off_l2_row γ s ξ) ∗ (∀ s', off_l2_row γ s' ξ -∗ off_rows on i ξ).
  Proof. Admitted.

  (* the publisher, under ip->lock, appends a fresh box's row *)
  Lemma off_rows_insert on i γ (s : l2_reg nat) (ξ : CtxId) :
    off_rows on i ξ -∗ off_l2_row γ s ξ ==∗ off_rows on i ξ ∗ off_member on i γ.
  Proof. Admitted.

  (* ---- what the fd row's FD_INODE arm carries for the off cell ----------- *)
  (* replaces main's [ioff_ref (fc_ip C) k q]: the box, membership in the
     inode slot's set, and this row's STAMPS MASS μ.  F34 (M-5): μ is NOT
     the fd row's cell fraction q -- a counted reference (one of M !! k's n)
     weighs 1 whatever its q; a share carved from it (fileread's
     `fileread_pay_carve`) weighs its share fraction and the lending parent
     1 − that (inode_ref_short's tie).  Σ over the slot's rows = f->ref. *)
  Definition off_fd_row on (i k : nat) (μ : Qp) : iProp Σ :=
    (∃ γ : box_names,
       off_box k γ ∗ off_member on i γ ∗ off_ref_stamps γ k μ)%I.

  (* ================================================================== *)
  (*  THE SITES                                                            *)
  (* ================================================================== *)

  (* filealloc, under ftable.lock: the free-slot row's cell becomes a box
     (fresh names, box_alloc_at) and (c) mints the exclusive unit.  Out: the
     L1 row's pieces for ftable's payload (c = 1), the owner's L2 half at
     {| 0; None |}, the owner's unit, the persistent box. *)
  Lemma off_filealloc `{CID : RiscvLang.CpuId} k γ (ξ : CtxId) (E : coPset) :
    CtxBox.stamps_auth (X := unit) γ ∅ -∗
    ghost_var (bx_cnt γ) 1 0%nat -∗
    ghost_var (bx_slotd γ) 1 (inhabitant : slot_reg nat unit) -∗
    ghost_var (bx_slotp γ) 1 (inhabitant : l2_reg nat) -∗
    own_context ξ -∗
    off_resident k ={E}=∗
    own_context ξ ∗ off_box k γ ∗
    ∃ T_boot : nat,
      off_regd γ (SlotReg T_boot false k None) ∗ llb loglen_name T_boot ∗
      off_cnt γ 1 ∗
      off_regp γ (L2Reg 0 None) ∗
      off_ref_stamps γ k 1%Qp.
  Proof. (* box_alloc_at, then box_ref_incr (the unit at T_boot) *) Admitted.

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
  Proof. (* box_checkout at Q := emp, Kp := 0 *) Admitted.

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
  Proof. (* box_park at Q := emp, then off_rows_insert *) Admitted.

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
  Proof. Admitted.

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
  Proof. (* box_park at Q := emp *) Admitted.

  (* filedup, under ftable.lock: (c) *)
  Lemma off_dup k γ (r : slot_reg nat unit) (c : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E -> sr_win r = false ->
    off_box k γ -∗ off_regd γ r -∗ off_cnt γ (S c) ={E}=∗
    off_regd γ r ∗ off_cnt γ (S (S c)) ∗ off_ref_stamps γ k 1%Qp.
  Proof. Admitted.

  (* fileclose, non-last, under ftable.lock: (d) *)
  Lemma off_close k γ (r : slot_reg nat unit) (c : nat) (E : coPset) :
    ↑(offBoxN .@ k) ⊆ E -> sr_win r = false ->
    off_box k γ -∗ off_regd γ r -∗ llb loglen_name (sr_td r) -∗ off_cnt γ (S (S c)) -∗
    off_ref_stamps γ k 1%Qp ={E}=∗
    ∃ td' : nat, ⌜(sr_td r ≤ td')%nat⌝ ∗
      off_regd γ (SlotReg td' false k (sr_x r)) ∗ off_cnt γ (S c) ∗ llb loglen_name td'.
  Proof. Admitted.

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
  Proof. (* box_withdraw_L1 at Q := emp; drop the returned register half *) Admitted.

End OffBox.
