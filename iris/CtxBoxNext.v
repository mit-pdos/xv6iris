(* CtxBoxNext.v -- THE ONE CtxBox EDIT (tso-cutover endgame §6⁵, owner ruling
   2026-09-02), AS TYPE-CHECKED STATEMENTS.  Proofs [Admitted]; each carries
   its case skeleton.  This file REPLACES CtxBox.v's Section box at the edit:
   the build agent moves these statements into CtxBox.v, re-proves them (the
   proofs are the current ones with the case selection changed as noted),
   retargets BioInv/IcacheEscrow, and deletes this file.  The helper section
   (qsum, max_stamp, keyed, the share kit) is CtxBox's, imported unchanged.

   WHAT CHANGES, AND WHY EACH IS A SIMPLIFICATION:

   1. Q IS THE RESIDUE OF BOTH OUT ARMS (ruling item 2, F32).  OUT_L1 :=
      hdr_out ∗ P_rest ∗ Q.  (a) takes Q, (b)/(b′) return it, (g) exchanges
      it.  The commit's collection can refute or read an OUT_L1 slot through
      Q exactly as it does OUT_L2.  bcache: Q = emp, nothing changes.

   2. THE ARM IS SELECTED BY THE TWO REGISTERS, NOT REFUTED BY CELLS.  With
      the L2 register recording the hold (F7/F21), the three states are
      determined by (sr_win r, lr_hold s):
          IN      : win = false, hold = None
          OUT_L1  : win = true,  hold = None
          OUT_L2  : win = false, hold = Some (i, m)
      and the body is a match on lr_hold, then on sr_win.  Every L1-side
      lemma already selects by win; (f) now selects OUT_L2 by hold agreement
      (it holds the L2 half naming its fragment) instead of refuting IN and
      OUT_L1 by cell clashes; (e) still refutes OUT_L1 by Σ (it holds no L1
      half) and no longer needs a token to refute OUT_L2 -- its L2 half says
      hold = None.  CONSEQUENCE: the client obligations P_hdr_excl,
      P_rest_excl, tok and tok_excl are GONE.  The "park principle" (every
      arm the park can meet must contain a cell) was the workaround for a
      parker that held only cells; F7 gave it the register half, and the
      principle is obsolete.  This is what lets a ONE-CELL client (the off
      box, R4b) instantiate the box at all: it has no second cell for
      P_rest_excl and no natural token.  bown / ic_tok stay in their lock
      payloads for the clients' own purposes; the box does not see them.

   3. (e′) box_checkout_split AND (f′) box_park_join (ruling item 1, F31).
      A checkout may leave part of the header's GHOST in the box: the client
      supplies a split wand  ∀ x ξ', P_hdr i x ξ' -∗ P_hdr' i x ξ' ∗ Q  which
      the lemma applies to the arm's header at ξb before the absorb, parking
      Q in OUT_L2 and handing out P_hdr'.  The park is the mirror: a join
      wand  ∀ x ξ', P_hdr' i x ξ' ∗ Q -∗ P_hdr i x ξ' ∗ Q'  applied at the
      holder's ξ with the Q the arm returns, depositing the full header and
      handing the caller the residue Q'.  (e)/(f) are the instances at
      P_hdr' := P_hdr with the wands that pass Q through.  Reviewer 1's
      "(f) needs no twin" does not hold: (f) takes the FULL header as input
      and the holder cannot re-form it before the box returns Q.

   THE LAW is unchanged in count of TRANSITIONS: (a) (b) (c) (d) (e) (f) (g),
   with (b′) (e′) (f′) the shape-generalizations of (b) (e) (f).  Rule 0 was
   run on every statement below; the producers are listed per lemma. *)
From Stdlib Require Import ZArith Lia QArith Qcanon.
From stdpp Require Import gmap countable.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap ufrac.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import TsoCtxPark.
Require Import TsoCtxAbsorbLb.
Require Import Xv6Cameras.
Require Import CtxBox.

Section box.
  Context `{!riscvGS Σ}.
  Context {id : Type} `{Countable id} `{!Inhabited id}.
  Context {X : Type}.
  Context `{!boxG id X Σ}.

  (* ---- the client's parameters: THREE, and no exclusivity laws ------- *)
  Context (P_hdr : id → X → CtxId → iProp Σ).
  Context (P_rest : X → CtxId → iProp Σ).
  Context (Q : iProp Σ).
  Context `{!∀ i x, CtxMorph (P_hdr i x)} `{!∀ x, CtxMorph (P_rest x)}.
  Context `{!∀ i x ξ, Timeless (P_hdr i x ξ)} `{!∀ x ξ, Timeless (P_rest x ξ)}.
  Context `{!Timeless Q}.

  Implicit Types (γ : box_names) (m : gmap (id * nat) ufrac).

  (* the ghosts and the reference: CtxBox's, unchanged *)
  Notation stamps_auth := (CtxBox.stamps_auth (X := X)).
  Notation stamps_frag := (CtxBox.stamps_frag (X := X)).
  Notation cnt_half := (CtxBox.cnt_half (X := X)).
  Notation slotd_half := (CtxBox.slotd_half (id := id) (X := X)).
  Notation slotp_half := (CtxBox.slotp_half (X := X)).
  Notation reference := (CtxBox.reference (X := X)).
  Notation l2_hold := (CtxBox.l2_hold (X := X)).

  (* the L1 out-window's ghost: the withdrawer's unit(s) with their llb *)
  Definition hdr_out γ m : iProp Σ :=
    (∃ m', ⌜qsum m' = qsum m⌝ ∗ stamps_frag γ m' ∗ llb loglen_name (max_stamp m'))%I.

  Definition in_arm (i : id) (ξb : CtxId) : iProp Σ :=
    (∃ x, P_hdr i x ξb ∗ P_rest x ξb)%I.

  (* THE BODY: arms selected by (lr_hold s, sr_win r). *)
  Definition box_body γ : iProp Σ :=
    (∃ (T : nat) (ξb : CtxId) m (c : nat) (r : slot_reg id X) (s : l2_reg id),
       ctx_parked ξb T ∗ llb loglen_name T ∗
       stamps_auth γ m ∗ cnt_half γ c ∗ slotd_half γ r ∗ slotp_half γ s ∗
       ⌜qsum m = nat_Qc c⌝ ∗                                        (* Σ *)
       ⌜keyed m (sr_ident r)⌝ ∗                                     (* I *)
       ⌜(∀ p, p ∈ dom m → (T ≤ p.2)%nat) ∨ (T ≤ lr_tp s)%nat⌝ ∗     (* C *)
       ⌜(T ≤ sr_td r)%nat ∨ ∃ p, p ∈ dom m ∧ p.2 = T⌝ ∗            (* D *)
       match lr_hold s with
       | Some (i, mh) =>                                          (* OUT_L2 *)
           ⌜sr_win r = false⌝ ∗ ⌜mh ≠ ∅⌝ ∗ ⌜keyed mh i⌝ ∗ stamps_frag γ mh ∗ Q
       | None =>
           if sr_win r
           then hdr_out γ m ∗ (∃ x, ⌜sr_x r = Some (x, T)⌝ ∗ P_rest x ξb) ∗ Q   (* OUT_L1 *)
           else in_arm (sr_ident r) ξb                                          (* IN *)
       end)%I.

  Definition is_box (N : namespace) γ : iProp Σ := inv N (box_body γ).

  (* the two payload rows.  L2's row has NO token. *)
  Definition l1_row γ (r : slot_reg id X) (ξ : CtxId) : iProp Σ :=
    (slotd_half γ r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗
     ctx_floor ξ (sr_td r) ∗ llb loglen_name (sr_td r))%I.
  Definition l2_row γ (s : l2_reg id) (ξ : CtxId) : iProp Σ :=
    (slotp_half γ s ∗ ⌜lr_hold s = None⌝ ∗ ctx_floor ξ (lr_tp s))%I.
  Global Instance l2_row_morph γ (s : l2_reg id) : CtxMorph (l2_row γ s).
  Proof.
    rewrite /l2_row. apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const| apply _].
  Qed.

  (* ================================================================== *)
  (*  (a) withdraw_L1 : IN → OUT_L1, under L1.  NEW: takes Q.             *)
  (* ================================================================== *)
  (* select: slot_d agree ⇒ win = false ⇒ hold = None ∧ IN, or hold = Some
     ∧ OUT_L2 -- refuted by Σ (the parked fragment + the caller's units >
     Σ m).  Producers as in CtxBox (D-cover, absorb); the close puts the
     caller's Q into OUT_L1 beside hdr_out and P_rest at the recorded x. *)
  Lemma box_withdraw_L1 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (mD : gmap (id * nat) ufrac) (Kd Kt : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    qsum mD = nat_Qc c →
    (sr_td r ≤ Kd)%nat →
    (max_stamp mD ≤ Kt)%nat →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kd -∗
    ctx_floor ξ Kt -∗
    llb loglen_name (max_stamp mD) -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    stamps_frag γ mD -∗
    Q ={E}=∗
    own_context ξ ∗
    cnt_half γ c ∗
    ∃ (x0 : X) (T0 : nat),
      ⌜(T0 ≤ Nat.max Kd Kt)%nat⌝ ∗
      slotd_half γ (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T0))) ∗
      P_hdr (sr_ident r) x0 ξ.
  Proof. Admitted.

  (* ================================================================== *)
  (*  (b′) deposit_L1 with a shape change : OUT_L1 → IN.  NEW: returns Q. *)
  (*  (b) is the instance x1 := x0 with the reflexive entailment.         *)
  (* ================================================================== *)
  (* select: slot_d agree ⇒ win = true ⇒ hold = None (the OUT_L2 arm
     carries ⌜win = false⌝) ⇒ OUT_L1: nothing to refute.  Producers as in
     CtxBox's (b′); Q comes back out of the arm. *)
  Lemma box_deposit_L1_shape `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 x1 : X) (T0 : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (∀ ξb : CtxId, P_rest x0 ξb ⊢ P_rest x1 ξb) →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    P_hdr i' x1 ξ ={E}=∗
    own_context ξ ∗ Q ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof. Admitted.

  (* ================================================================== *)
  (*  (c) ref_incr, (d) ref_decr : unchanged (select win = false; the arm  *)
  (*  -- IN or OUT_L2 -- is framed).                                       *)
  (* ================================================================== *)
  Lemma box_ref_incr (N : namespace) γ (r : slot_reg id X) (c : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    is_box N γ -∗
    slotd_half γ r -∗
    cnt_half γ c ={E}=∗
    slotd_half γ r ∗
    cnt_half γ (S c) ∗
    ∃ T : nat, reference γ (sr_ident r) {[ (sr_ident r, T) := 1%Qp ]}.
  Proof. Admitted.

  Lemma box_ref_decr (N : namespace) γ (r : slot_reg id X) (c : nat) (i : id)
      (mD : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    qsum mD = nat_Qc 1 →
    is_box N γ -∗
    slotd_half γ r -∗
    llb loglen_name (sr_td r) -∗
    cnt_half γ (S c) -∗
    reference γ i mD ={E}=∗
    slotd_half γ (SlotReg (Nat.max (sr_td r) (max_stamp mD)) false (sr_ident r) (sr_x r)) ∗
    cnt_half γ c ∗
    llb loglen_name (Nat.max (sr_td r) (max_stamp mD)).
  Proof. Admitted.

  (* ================================================================== *)
  (*  (e′) checkout with a header split : IN → OUT_L2, under L2.           *)
  (*  (e) is the instance P_hdr' := P_hdr, split := λ h, (h, Q) with the    *)
  (*  caller's Q in hand.  NO TOKEN.                                       *)
  (* ================================================================== *)
  (* select: slot_p agree ⇒ hold = None ⇒ IN or OUT_L1 (by win, unknown):
       OUT_L1: hdr_out's m' (qsum m' = qsum m) ⋅ the caller's mh (≠ ∅) ≼ m
               ⇒ qsum m > qsum m.  Contradiction (as today).
       IN:     (I) on mh ⇒ i = sr_ident r; (C) ⇒ T ≤ Kt or T ≤ Kp;
               the split wand at ξb: P_hdr i x ξb ⊢ P_hdr' i x ξb ∗ Q;
               absorb ∃ x, P_hdr' i x ∗ P_rest x to ξ (one binder);
               close OUT_L2 with Q, the caller's whole fragment (keyed, ≠ ∅)
               and slot_p := {| tp; Some (i, mh) |} (both halves in hand).
     rows unchanged (m, T, r, s.tp). *)
  Lemma box_checkout_split `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) `{!∀ i x, CtxMorph (P_hdr' i x)}
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    (∀ (x : X) (ξ' : CtxId), P_hdr i x ξ' ⊢ P_hdr' i x ξ' ∗ Q) →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof. Admitted.

  (* (e): the instance -- the caller's Q passes straight into the arm *)
  Lemma box_checkout `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    Q -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof. (* box_checkout_split at P_hdr' := P_hdr; the wand frames the caller's Q *) Admitted.

  (* ================================================================== *)
  (*  (f′) park with a header join : OUT_L2 → IN, under L2.               *)
  (*  (f) is the instance P_hdr' := P_hdr, Q' := Q (the arm's Q handed     *)
  (*  back untouched).  NO TOKEN; no cell refutation.                      *)
  (* ================================================================== *)
  (* select: slot_p agree ⇒ hold = Some (i, mh) ⇒ the OUT_L2 arm, by the
     body's match -- nothing to refute.  (I) on mh's keys + keyed mh i ⇒
     i = sr_ident r.  The join wand at ξ with the arm's Q: P_hdr' i x ξ ∗ Q
     ⊢ P_hdr i x ξ ∗ Q'; deposit ∃ x, P_hdr i x ∗ P_rest x at ξb ⇒ T';
     move mh to {[(i, T') := mass mh]}; slot_p := {| T'; None |} both
     halves; close IN.  rows: (Σ) same mass, (I) i = ident, (C) right via
     tp = T', (D) T' ∈ dom.  Out: Q', the re-minted reference, llb T'. *)
  Lemma box_park_join `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) (Q' : iProp Σ)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    (∀ (x : X) (ξ' : CtxId), P_hdr' i x ξ' ∗ Q ⊢ P_hdr i x ξ' ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q' ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof. Admitted.

  Lemma box_park `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof. (* box_park_join at P_hdr' := P_hdr, Q' := Q *) Admitted.

  (* ================================================================== *)
  (*  (g) l1_to_l2 : OUT_L1 → OUT_L2, under both locks.  NEW: exchanges Q  *)
  (*  (in: the new L2 residue; out: the window's).  NO TOKEN.              *)
  (* ================================================================== *)
  (* select: slot_d agree ⇒ win = true ⇒ (hold = None by the OUT_L2 arm's
     ⌜win = false⌝) ⇒ OUT_L1.  Producers as in CtxBox's (g): T = T0 by the
     recorded pair; cover K ≥ T0; P_rest out; hdr_out's m' = m (equal
     sums), keyed by (I), ≠ ∅ by Σ at c = 1; L1 closes at its own td;
     slot_p := {| tp; Some (ident, m') |} (both halves); the arm's Q comes
     out, the caller's Q goes in. *)
  Lemma box_l1_to_l2 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (x0 : X) (T0 K : nat) (s0 : l2_reg id) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (T0 ≤ K)%nat →
    lr_hold s0 = None →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ K -∗
    slotd_half γ r -∗
    cnt_half γ 1 -∗
    Q -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗ Q ∗
    P_rest x0 ξ ∗
    slotd_half γ (SlotReg (sr_td r) false (sr_ident r) None) ∗
    cnt_half γ 1 ∗
    ∃ m', ⌜qsum m' = nat_Qc 1⌝ ∗ l2_hold γ (sr_ident r) m'.
  Proof. Admitted.

  (* ================================================================== *)
  (*  boot over pre-minted names (box_alloc_at): unchanged in shape        *)
  (* ================================================================== *)
  Lemma box_alloc_at `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i0 : id) (E : coPset) :
    stamps_auth γ ∅ -∗
    ghost_var (bx_cnt γ) 1 0%nat -∗
    ghost_var (bx_slotd γ) 1 (inhabitant : slot_reg id X) -∗
    ghost_var (bx_slotp γ) 1 (inhabitant : l2_reg id) -∗
    own_context ξ -∗
    (∃ x, P_hdr i0 x ξ ∗ P_rest x ξ) ={E}=∗
    own_context ξ ∗
    ∃ T_boot : nat,
      is_box N γ ∗
      slotd_half γ (SlotReg T_boot false i0 None) ∗ llb loglen_name T_boot ∗
      cnt_half γ 0 ∗
      slotp_half γ (L2Reg 0 None).
  Proof. Admitted.

  Lemma l1_row_fold γ (r : slot_reg id X) (ξ : CtxId) :
    sr_win r = false → sr_x r = None →
    slotd_half γ r -∗ ctx_floor ξ (sr_td r) -∗ llb loglen_name (sr_td r) -∗
    l1_row γ r ξ.
  Proof. iIntros (Hw Hx) "Hd #Hfl #Hllb". iFrame "Hd Hfl Hllb". by iPureIntro. Qed.
  Lemma l2_row_fold γ (T' : nat) (ξ : CtxId) :
    slotp_half γ (L2Reg T' None) -∗ ctx_floor ξ T' -∗ l2_row γ (L2Reg T' None) ξ.
  Proof. iIntros "Hp #Hfl". iFrame "Hp Hfl". by iPureIntro. Qed.
End box.
