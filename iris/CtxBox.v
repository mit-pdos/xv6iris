(* CtxBox.v -- THE TRANSIT BOX, v2 (claude-notes/design/tso-escrow-endgame.md
   §2/§3), AS A TYPE-CHECKED SKELETON.

   STATUS: statements only.  Every proof is [Admitted]; each carries the
   case skeleton the proof must follow (destruct the window flag, destruct
   the arm, name the refutation or the transition, list the rows the close
   re-establishes).  This file is the design of record for the box's
   LEMMAS: the endgame doc points here for premises and conclusions, and a
   change to a lemma's shape is a change to this file first.

   WHY A SKELETON.  Five design leaks in one day (F1, F6, F7, F8, F9) were
   all of the kind a statement catches and prose does not: a missing arm
   case, a conclusion asserted from a spec parameter rather than derived
   from a premise, a binder scoped over the wrong parameter.  Typing the
   statements and writing the case split BEFORE building is the fix.  The
   first rule-0 audit of this file (F10–F13) then found four conclusions
   without a producing premise in the statements themselves -- fixed
   here: (a)/(b) name the window's x through the register, (d) takes
   llb td, (e) takes Q, out_l2 records keyed m i for (f).

   THE BOX (parameters of the section):
     id       the client's identity type (bcache: dev × blockno)
     X        the client's shared witness type (bcache: the data bytes bs;
              P_hdr and P_rest share ONE binder over it -- F8)
     P_hdr    the header: cells the L1 side reads or writes, at an identity
     P_rest   the rest of the bundle
     Q        the client's ξ-free ghost residue during an L2 checkout
     tok      the L2 exclusivity token (bcache: bown; icache: ic_tok)
   with the two exclusivity laws the arms are refuted by.  tok and Q must
   be GHOST (no cells): CtxMorph of a constant is trivial, so only
   ξ-freedom keeps the box CtxMove-able across the fork (R-4).
   THE L2 HOLDER'S HANDLE pins the parked fragment's keys AND mass when it
   instantiates l2_hold (bcache: a unit singleton at ((dev,bno), t); icache:
   the share singleton at mass s) -- never ∃ over the map (R-1).

   THE GHOSTS (one per box; §3.2):
     stamps   authR (gmapUR (id * nat) ufracR) -- the STAMPED SHARES.  Each
              counted reference owns one unit of mass at key (identity,
              stamp of the last deposit it witnessed); shares own part of a
              unit.  Row (I): every live key names the box's identity.
     cnt      ghost_var nat -- half in the box, half beside L1's refcount.
     slot_d   ghost_var slot_reg -- THE L1 SLOT REGISTER {| td; win; ident;
              x |}, half in the box, half in L1's payload row.  The only
              state L1 and the box share.  [x] names the witness the open
              window's P_rest sits at (F10), so (b) re-deposits a header
              at the SAME x -- the bcache header ignores it, the icache's
              valid re-deposit needs it.
     slot_p   ghost_var l2_reg -- THE L2 SLOT REGISTER {| tp; hold |},
              half in the box, half in L2's payload row (at rest) or in the
              L2 holder's handle (during a checkout).  [hold] records
              exactly the fragment the checkout parked in the OUT_L2 arm --
              key(s) AND mass -- so the park can take it back and re-form
              the unit.  (F7 without the split: the vetted half-split left
              the rejoined mass ∃-bound, and refs-- needs a unit.)

   THE ARMS: IN | OUT_L2 | OUT_L1, selected by the L1 register's flag:
     win = false:  (∃ x, P_hdr ident x ξb ∗ P_rest x ξb)  ∨  OUT_L2
     win = true :  hdr_out ∗ P_rest x ξb  at the x the register names
                   (sr_x = Some x; (a) set it, (b) re-deposits at it)
   OUT_L2 := Q ∗ tok ∗ (the L2 payload's own row is NOT here: its slot_p
   half rides the holder's handle) ∗ the parked fragment named by [hold].

   THE ROWS (pure, in the body):
     (I)  ∀ p ∈ dom m, p.1 = ident          the checkout's identity tie
     (C)  (∀ p ∈ dom m, T ≤ p.2) ∨ T ≤ tp   the L2-side cover
     (D)  T ≤ td ∨ T ∈ snd <$> dom m         the L1-side cover
     (Σ)  qsum m = c                        mass = refcount

   THE SIX LEMMAS: withdraw_L1 (a), deposit_L1 (b), ref_incr (c),
   ref_decr (d), checkout (e), park (f); plus box_alloc (boot).  No others.

   The cmra/class declarations here move to Xv6Cameras §15 at R1'; they are
   local so this file type-checks standalone. *)
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

(* ---- the registers' value types ------------------------------------- *)
Record slot_reg (id X : Type) := SlotReg {
  sr_td    : nat;      (* the stamp L1's payload floor row covers *)
  sr_win   : bool;     (* the L1 out-window is open *)
  sr_ident : id;       (* the box's current identity *)
  sr_x     : option X; (* F10: the witness the open window's P_rest is at *)
}.
Arguments SlotReg {id X} _ _ _ _.
Arguments sr_td {id X} _.
Arguments sr_win {id X} _.
Arguments sr_ident {id X} _.
Arguments sr_x {id X} _.

Record l2_reg (id : Type) `{Countable id} := L2Reg {
  lr_tp   : nat;                                 (* the stamp L2's floor row covers *)
  lr_hold : option (id * gmap (id * nat) ufrac); (* the fragment parked in OUT_L2 *)
}.
Arguments L2Reg {id _ _} _ _.
Arguments lr_tp {id _ _} _.
Arguments lr_hold {id _ _} _.

(* ---- cameras (to Xv6Cameras §15 at R1') ---------------------------- *)
Definition stampsR (id : Type) `{Countable id} : cmra :=
  authR (gmapUR (id * nat) ufracR).
Class boxG (id : Type) `{Countable id} (X : Type) (Σ : gFunctors) := BoxG {
  box_stampsG :: inG Σ (stampsR id);
  box_cntG    :: ghost_varG Σ nat;
  box_slotdG  :: ghost_varG Σ (slot_reg id X);
  box_slotpG  :: ghost_varG Σ (l2_reg id);
}.

Record box_names := BoxNames {
  bx_stamps : gname;
  bx_cnt    : gname;
  bx_slotd  : gname;
  bx_slotp  : gname;
}.

(* ---- pure helpers over the stamps map ------------------------------- *)
Section helpers.
  Context {id : Type} `{Countable id}.

  (* the mass, in Q (F3's Q-valued sum: ∅ ↦ 0, no case split) *)
  Definition qsum (m : gmap (id * nat) ufrac) : Qc :=
    map_fold (λ _ (q : ufrac) acc, (Qp_to_Qc q + acc)%Qc) 0%Qc m.
  Definition nat_Qc (n : nat) : Qc := Q2Qc (inject_Z (Z.of_nat n)).

  (* the largest stamp a fragment names (0 on ∅) -- what R1 presents *)
  Definition max_stamp (m : gmap (id * nat) ufrac) : nat :=
    map_fold (λ (p : id * nat) _ acc, Nat.max p.2 acc) 0%nat m.

  (* every key of the fragment is at this identity *)
  Definition keyed (m : gmap (id * nat) ufrac) (i : id) : Prop :=
    ∀ p, p ∈ dom m → p.1 = i.

  (* the unit's mass, as a positive: 1 at c = 0 (the bump), c otherwise *)
  Definition unit_mass (c : nat) : ufrac := pos_to_Qp (Pos.of_nat (Nat.max 1 c)).
End helpers.

Section box.
  Context `{!riscvGS Σ}.
  Context {id : Type} `{Countable id}.
  Context {X : Type}.
  Context `{!boxG id X Σ}.

  (* ---- the client's parameters -------------------------------------- *)
  Context (P_hdr : id → X → CtxId → iProp Σ).
  Context (P_rest : X → CtxId → iProp Σ).
  Context (Q : iProp Σ).
  Context (tok : iProp Σ).

  (* the client's obligations *)
  Context `{!∀ i x, CtxMorph (P_hdr i x)} `{!∀ x, CtxMorph (P_rest x)}.
  Context `{!∀ i x ξ, Timeless (P_hdr i x ξ)} `{!∀ x ξ, Timeless (P_rest x ξ)}.
  Context `{!Timeless Q} `{!Timeless tok}.
  (* a FULL cell in each part: what the park and the deposit refute the
     resting arms by, across contexts (bcache: ctx_word4_excl_x on b_valid
     and b_disk) *)
  Context (P_hdr_excl : ∀ i i' x x' ξ ξ', P_hdr i x ξ -∗ P_hdr i' x' ξ' -∗ False).
  Context (P_rest_excl : ∀ x x' ξ ξ', P_rest x ξ -∗ P_rest x' ξ' -∗ False).
  Context (tok_excl : tok -∗ tok -∗ False).

  Implicit Types (γ : box_names) (m : gmap (id * nat) ufrac).

  (* ---- the ghosts, named ------------------------------------------- *)
  Definition stamps_auth γ m : iProp Σ := own (bx_stamps γ) (● m).
  Definition stamps_frag γ m : iProp Σ := own (bx_stamps γ) (◯ m).
  Definition cnt_half γ (c : nat) : iProp Σ := ghost_var (bx_cnt γ) (1/2) c.
  Definition slotd_half γ (r : slot_reg id X) : iProp Σ := ghost_var (bx_slotd γ) (1/2) r.
  Definition slotp_half γ (s : l2_reg id) : iProp Σ := ghost_var (bx_slotp γ) (1/2) s.

  (* ---- the reference: ONE spelling, ghost-only (§3.3) --------------- *)
  (* a counted reference has [qsum m = 1]; a share has any positive mass *)
  Definition reference γ (i : id) m : iProp Σ :=
    (⌜m ≠ ∅⌝ ∗ ⌜keyed m i⌝ ∗ stamps_frag γ m ∗ llb loglen_name (max_stamp m))%I.

  (* ---- the arms ----------------------------------------------------- *)
  (* the L1 out-window's ghost: the withdrawer's whole unit(s), or ∅ *)
  Definition hdr_out γ m : iProp Σ :=
    (∃ m', ⌜qsum m' = qsum m⌝ ∗ stamps_frag γ m')%I.

  (* the L2 checkout's residue: the client's ghost, the token, and the
     fragment the holder parked -- named by the L2 register's [hold] *)
  Definition out_l2 γ (s : l2_reg id) : iProp Σ :=
    (Q ∗ tok ∗
     ∃ i m, ⌜lr_hold s = Some (i, m)⌝ ∗ ⌜m ≠ ∅⌝ ∗ ⌜keyed m i⌝ ∗   (* F13 *)
            stamps_frag γ m)%I.

  Definition in_arm (i : id) (ξb : CtxId) : iProp Σ :=
    (∃ x, P_hdr i x ξb ∗ P_rest x ξb)%I.

  (* ---- the body (§2) ----------------------------------------------- *)
  Definition box_body γ : iProp Σ :=
    (∃ (T : nat) (ξb : CtxId) m (c : nat) (r : slot_reg id X) (s : l2_reg id),
       ctx_parked ξb T ∗ llb loglen_name T ∗
       stamps_auth γ m ∗ cnt_half γ c ∗ slotd_half γ r ∗ slotp_half γ s ∗
       ⌜qsum m = nat_Qc c⌝ ∗                                        (* Σ *)
       ⌜keyed m (sr_ident r)⌝ ∗                                     (* I *)
       ⌜(∀ p, p ∈ dom m → (T ≤ p.2)%nat) ∨ (T ≤ lr_tp s)%nat⌝ ∗     (* C *)
       ⌜(T ≤ sr_td r)%nat ∨ ∃ p, p ∈ dom m ∧ p.2 = T⌝ ∗            (* D *)
       (if sr_win r
        then hdr_out γ m ∗ ∃ x, ⌜sr_x r = Some x⌝ ∗ P_rest x ξb   (* F10 *)
        else in_arm (sr_ident r) ξb ∨ out_l2 γ s))%I.

  Definition is_box (N : namespace) γ : iProp Σ := inv N (box_body γ).

  (* ---- the two payload rows the locks carry (client-facing) --------- *)
  (* L1's payload row, at rest: the register half with the window shut,
     the floor row at td, and its llb.  The client adds ⌜sr_ident r = its
     identity cells' values⌝ beside it (bcache: (devs k, bnos k)). *)
  Definition l1_row γ (r : slot_reg id X) (ξ : CtxId) : iProp Σ :=
    (slotd_half γ r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗
     ctx_floor ξ (sr_td r) ∗ llb loglen_name (sr_td r))%I.

  (* L2's payload row, at rest: the token, the register half with nothing
     held, and the floor row at tp *)
  Definition l2_row γ (s : l2_reg id) (ξ : CtxId) : iProp Σ :=
    (tok ∗ slotp_half γ s ∗ ⌜lr_hold s = None⌝ ∗ ctx_floor ξ (lr_tp s))%I.

  (* what the L2 HOLDER carries across the checkout (behind the frozen
     handle's token row, F7): the register half naming the parked fragment,
     and the llb of that fragment's stamps *)
  Definition l2_hold γ (i : id) m : iProp Σ :=
    (∃ tp, slotp_half γ (L2Reg tp (Some (i, m))) ∗ llb loglen_name (max_stamp m))%I.

  (* ================================================================== *)
  (*  (a) withdraw_L1 : IN → OUT_L1, under L1                            *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut), the cnt half at c,
     ALL c units as one fragment (∅ at c = 0), and floors covering L1's row
     (Kd ≥ td) and the fragment's stamps (Kt ≥ max_stamp mD, from R1).
     Proof skeleton:
       open; agree slot_d ⇒ win = false ⇒ in_arm ∨ out_l2.
       out_l2: its fragment m0 ≠ ∅ composes with mD: qsum m ≥ qsum mD +
               qsum m0 > nat_Qc c = qsum m.  Contradiction.
       in_arm: (D) with m = mD (mD ≼ m, equal sums ⇒ equal maps):
               T ≤ td ≤ Kd  or  T ∈ snd dom mD ⇒ T ≤ Kt.
               own_context_floor_view at max Kd Kt ⇒ hart_view_lb K ≥ T;
               ctx_absorb_lb pulls P_hdr ident x to ξ; P_rest stays.
       close: win := true, sr_x := Some x0 (the arm's x, F10 -- both
              halves in hand); hdr_out := ◯ mD; P_rest stays at x0;
              rows (Σ),(I),(C),(D) unchanged (m, T, r.td, r.ident, s unchanged). *)
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
    slotd_half γ r -∗
    cnt_half γ c -∗
    stamps_frag γ mD ={E}=∗
    own_context ξ ∗
    cnt_half γ c ∗
    ∃ x0, slotd_half γ (SlotReg (sr_td r) true (sr_ident r) (Some x0)) ∗
          P_hdr (sr_ident r) x0 ξ.
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  (b) deposit_L1 : OUT_L1 → IN, under L1 (deposit AND bump at c = 0)  *)
  (* ================================================================== *)
  (* Caller holds: L1's register half with the window OPEN and sr_x =
     Some x0 (the witness (a) named), the cnt half, and the header at the
     NEW identity id' AT THAT x0 (F10: the arm's P_rest is at x0 by the
     register; the bcache header ignores x, the icache's is at the x0 it
     withdrew).
     Proof skeleton:
       open; agree slot_d ⇒ win = true, the arm's x = x0 ⇒
             hdr_out ∗ P_rest x0 ξb.
       hdr_out's ◯ m' with equal sums ⇒ m' = m: the box now holds ALL mass.
       ctx_deposit (P_hdr id' x) at ξb ⇒ T' ≥ T (P_rest clean at T ≤ T').
       stamps: dealloc m, alloc {[(id', T') := unit_mass c]}.
       cnt := max 1 c (the bump at c = 0); slot_d := {| T'; false; id';
       None |} (both halves).
       close in_arm at id' with x0; rows: (Σ) by construction,
       (I) singleton at id', (C) left disjunct (T' ≤ T'), (D) via td = T'.
       export llb T' (ctx_parked_llb). *)
  Lemma box_deposit_L1 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 : X) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some x0 →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    P_hdr i' x0 ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  (c) ref_incr, under L1 (legal at c = 0: bget's hit on a cached      *)
  (*      refcnt-0 buffer takes this path, not the recycler's)            *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut) and the cnt half.  It
     learns the identity from the register (its own row ties sr_ident to
     its identity cells) -- never from the bundle, which may be OUT_L2.
     Proof skeleton:
       open; agree slot_d ⇒ win = false; the arm is untouched.
       stamps: alloc {[(ident, T) := 1]} on ● m; cnt := S c.
       rows: (Σ) +1, (I) new key at ident, (C) T ≤ T keeps the left
       disjunct if it held (the right is untouched), (D) untouched.
       export llb T (the box's own). *)
  Lemma box_ref_incr (N : namespace) γ (r : slot_reg id X) (c : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    is_box N γ -∗
    slotd_half γ r -∗
    cnt_half γ c ={E}=∗
    slotd_half γ r ∗
    cnt_half γ (S c) ∗
    ∃ T : nat, reference γ (sr_ident r) {[ (sr_ident r, T) := 1%Qp ]}.
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  (d) ref_decr, under L1 (refs 1 → 0 is THIS, not a withdraw)         *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut), the cnt half at S c,
     ONE UNIT (qsum = 1) as a reference, and L1's row's `llb td` (F11:
     the conclusion's llb of the max needs both llbs).  It pays the
     unit's debt: td := max td (max_stamp mD); the release folds the new
     td by R2.
     Proof skeleton:
       open; agree slot_d ⇒ win = false; the arm is untouched.
       stamps: dealloc mD (mD ≼ m by validity; ufrac cancels).
       cnt := c; slot_d.td := max td (max_stamp mD) (both halves).
       rows: (Σ) −1, (I) monotone under removal, (C) monotone under
       removal (left) / untouched (right), (D): a removed witness p.2 = T
       has T ≤ max_stamp mD ≤ td'. *)
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
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  (e) checkout : IN → OUT_L2, under L2                                *)
  (* ================================================================== *)
  (* Caller holds: its reference (mass q > 0, keyed at i, stamps ≤ Kt by
     R1 at the acquire), the L2 payload row's pieces (tok, the register
     half with nothing held, its floor Kp ≥ tp), floors, and the client's
     residue Q (F12: the OUT_L2 arm is closed with it).
     Proof skeleton:
       open; the flag is NOT known (no slot_d in hand): destruct sr_win.
       win = true : hdr_out's ◯ m' (qsum m' = qsum m) composes with the
                    caller's ◯ mh (qsum > 0) ⇒ qsum m > qsum m.  Contradiction.
       win = false, out_l2 : tok vs the arm's tok (tok_excl).
       win = false, in_arm : agree slot_p ⇒ tp = lr_tp s0.
                    (I): mh's keys ∈ dom m ⇒ i = sr_ident r.
                    (C): T ≤ every key's stamp ≤ Kt, or T ≤ tp ≤ Kp.
                    own_context_floor_view at max Kt Kp; ctx_absorb_lb pulls
                    ∃ x, P_hdr i x ∗ P_rest x to ξ (ONE binder, F8).
       close out_l2 with Q, tok, the caller's WHOLE fragment parked with
       its ⌜keyed mh i⌝ (F13, from the reference), and slot_p := {| tp;
       Some (i, mh) |} (both halves in hand); the caller keeps the
       register half for its handle (l2_hold).
       rows unchanged (m, T, r untouched; s.tp untouched). *)
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
    tok -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  (f) park : OUT_L2 → IN, under L2 (before releasesleep)              *)
  (* ================================================================== *)
  (* Caller holds: the bundle at identity i (the handle's cells), and the
     handle's ghost row l2_hold naming the parked fragment (i, mh).  The
     identity witness is the REGISTER, agreed against the box, and the
     parked fragment's keys are then tied to sr_ident by (I) -- F7's gap
     closed without a spec parameter.
     Proof skeleton:
       open; destruct sr_win.
       win = true : the arm's P_rest x ξb vs the caller's P_rest x' ξ
                    (P_rest_excl).
       win = false, in_arm : the arm's P_hdr vs the caller's (P_hdr_excl).
       win = false, out_l2 : agree slot_p ⇒ the arm's fragment IS (i, mh);
                    take Q, tok, ◯ mh, ⌜keyed mh i⌝.  (I) on mh's keys
                    (◯ mh ≼ ● m, mh ≠ ∅) + keyed mh i ⇒ i = sr_ident r
                    (F13); rewrite the deposit to in_arm (sr_ident r).
                    ctx_deposit (∃ x, P_hdr i x ∗ P_rest x) at ξb ⇒ T'.
                    stamps: dealloc mh, alloc {[(i, T') := mass mh]} --
                    the caller's mass, known from the register.
                    slot_p := {| T'; None |} (both halves).
       close in_arm at sr_ident r; rows: (Σ) unchanged (same mass),
       (I) i = sr_ident r, (C) right disjunct T' ≤ tp = T', (D) T' ∈ dom.
       export llb T' for the _in releasesleep. *)
  Lemma box_park `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗
    Q ∗ tok ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
  Admitted.

  (* ================================================================== *)
  (*  boot: the box is born IN, at the boot deposit's stamp               *)
  (* ================================================================== *)
  (* The caller (bio_init / icache boot) deposits the bundle at identity
     i0 and receives: L1's register half at {| T_boot; false; i0 |} with
     llb T_boot (L1's floor row must start at td = T_boot -- the newlock
     twin over lock_pay_intro_llb folds it), the cnt half at 0, and L2's
     register half at {| 0; None |} (ctx_floor_0 serves its row).
     Proof skeleton: ctx_parked_alloc; ctx_deposit the bundle (T_boot);
     own_alloc (● ∅); ghost_var_alloc ×3; inv_alloc with m = ∅ (rows: Σ
     trivial, I vacuous, C vacuous-left, D td = T_boot). *)
  Lemma box_alloc `{CID : CpuId} (N : namespace) (ξ : CtxId) (i0 : id) (E : coPset) :
    own_context ξ -∗
    (∃ x, P_hdr i0 x ξ ∗ P_rest x ξ) ={E}=∗
    own_context ξ ∗
    ∃ (γ : box_names) (T_boot : nat),
      is_box N γ ∗
      slotd_half γ (SlotReg T_boot false i0 None) ∗ llb loglen_name T_boot ∗
      cnt_half γ 0 ∗
      slotp_half γ (L2Reg 0 None).
  Proof.
  Admitted.

  (* ---- the derived facts the client rows need ------------------------ *)

  (* the L1 payload row folds at release: the register half comes back
     shut with whatever td the lemmas set, and the caller has llb td *)
  Lemma l1_row_fold γ (r : slot_reg id X) (ξ : CtxId) :
    sr_win r = false → sr_x r = None →
    slotd_half γ r -∗ ctx_floor ξ (sr_td r) -∗ llb loglen_name (sr_td r) -∗
    l1_row γ r ξ.
  Proof. iIntros (Hw Hx) "Hd #Hfl #Hllb". iFrame "Hd Hfl Hllb". by iPureIntro. Qed.

  (* the L2 payload row folds at releasesleep (the _in form mints the
     floor from the park's llb T') *)
  Lemma l2_row_fold γ (T' : nat) (ξ : CtxId) :
    tok -∗ slotp_half γ (L2Reg T' None) -∗ ctx_floor ξ T' -∗
    l2_row γ (L2Reg T' None) ξ.
  Proof. iIntros "Ht Hp #Hfl". iFrame "Ht Hp Hfl". by iPureIntro. Qed.

  (* the L2 row is a CtxMorph payload (the floor is the only ξ-row) *)
  Global Instance l2_row_morph γ (s : l2_reg id) : CtxMorph (l2_row γ s).
  Proof.
    rewrite /l2_row. apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const| apply _].
  Qed.

End box.
