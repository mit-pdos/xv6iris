(* CtxBoxHooked.v -- THE TRANSIT BOX, CONSOLIDATED: ONE HOOK PER TRANSITION
   (claude-notes/projects/tso-cutover-endgame.md §6²⁶/§6²⁷; the second
   reviewer's side-by-side build, 2026-09-02).

   STATUS: a SIDE-BY-SIDE implementation.  It does not replace CtxBox.v; it
   imports CtxBox and reuses its ghosts, arms, rows, body, invariant, the
   reference kit, (c)/(d), the L2 residue accessor, the view and the boot
   lemmas UNCHANGED.  What it adds is the statement discipline §6²⁶ asked
   for, ready to slot in at the first quiet point (after r20b, before r21)
   or whenever the next box extension is needed:

     EVERY TRANSITION THAT MOVES A HEADER TAKES ONE CLIENT HOOK,
       Qc ∗ <the client content the transition moves> ={E ∖ ↑N}=∗
            <that content, re-shaped> ∗ Q',
     run at the transition's own step, at the box's mask (the box is open,
     so the hook may open any OTHER invariant and never the box).  The
     plain forms -- the statements CtxBox.v exports today, by the same
     names and with the same premises and conclusions -- are COROLLARIES at
     the identity hook (Qc := what the plain form took, Q' := what it gave
     back, the hook framing).

   Why: between §6¹⁰ and §6²⁵ the box grew by four per-lemma variants --
   (b′) with x1, (e′) with F33's Qc and then a view shift, (f′) with F43's
   Qc', (b″) with a view-shift join -- each individually justified, each a
   new statement over one body.  §6²⁶ named the pattern and §6²⁷ widened
   it: (a) and (g) get the same hook NOW, so the law cannot grow by
   variants again.  A new client need is met by the hook of the transition
   it belongs to, never by a fifth statement shape.

   THE LAW, AS STATED HERE:
     seven transitions
       (a) box_withdraw_L1_hook    IN → OUT_L1     hook on the header, produces Q1 c
       (b) box_deposit_L1_hook     OUT_L1 → IN     hook on Q1 c, the header, P_rest (x0 → x1)
       (c) box_ref_incr            (CtxBox, unchanged; moves no header)
       (d) box_ref_decr            (CtxBox, unchanged; moves no header)
       (e) box_checkout_hook       IN → OUT_L2     hook on the header, produces Q2
       (f) box_park_hook           OUT_L2 → IN     hook on Q2 and the header
       (g) box_l1_to_l2_hook       OUT_L1 → OUT_L2 hook on the residues, Q1 1 → Q2
     two residue accessors
       box_q_update                (CtxBox, unchanged)   OUT_L2's Q2, in place
       box_q1_update               (here)                OUT_L1's Q1 c, in place
     one view
       box_view                    (CtxBox, unchanged)
     boot
       box_alloc / box_alloc_at    (CtxBox, unchanged)

   THE COROLLARIES (the names clients use today, statements verbatim from
   CtxBox.v): box_withdraw_L1, box_deposit_L1_shape, box_deposit_L1,
   box_checkout_split, box_checkout, box_park_join, box_park, box_l1_to_l2.
   A client switches from CtxBox.<name> to CtxBoxHooked.<name> with no
   other change; a client that needs a hook calls <name>_hook.

   WHERE THE HOOK RUNS (rule 0, per statement):
     (a)  at ξb, BEFORE the absorb: the hook sees the header at the box's
          context and returns the part that travels (P_hdr', CtxMorph) and
          the residue that stays.  The guard's pin, had F42 not moved it to
          the table row, could be produced here.
     (b)  at the caller's ξ for the header and Q1 c, at ξb for P_rest:
          BEFORE the deposit.  The icache recycle rebuilds its header from
          Q1 0's live arm here (§6²⁴).  P_rest's shape change x0 → x1 (F14)
          is part of the same hook (the plain form supplies the entailment).
     (e)  at ξb, BEFORE the absorb (landed as box_checkout_split; the
          read arm refutes the frozen alternative here, §6²¹).
     (f)  at the holder's ξ, BEFORE the deposit (landed as box_park_join
          with a pure join; the hook is its view-shift form).
     (g)  at the caller's ξ on the residues only: the header is out and
          stays out; P_rest travels as before.
   None of the hooks sees a register, a stamp, the count or a row: the
   hook is CLIENT content in, client content out, and the box's own ghost
   moves exactly as in the plain form.

   PROOFS: each hooked proof is CtxBox.v's proof of the plain form with one
   [iMod (Hhook …)] where that proof read the client content; nothing else
   moves.  The corollaries are one-line instantiations.  No Admitted. *)

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

Import CtxBox.

Section hooked.
  Context `{!riscvGS Σ}.
  Context {id : Type} `{Countable id} `{!Inhabited id}.
  Context {X : Type}.
  Context `{!boxG id X Σ}.

  (* the client's parameters and obligations: CtxBox's, verbatim *)
  Context (P_hdr : id → X → CtxId → iProp Σ).
  Context (P_rest : X → CtxId → iProp Σ).
  Context (Q1 : nat → iProp Σ).
  Context (Q2 : iProp Σ).
  Context `{!∀ i x, CtxMorph (P_hdr i x)} `{!∀ x, CtxMorph (P_rest x)}.
  Context `{!∀ i x ξ, Timeless (P_hdr i x ξ)} `{!∀ x ξ, Timeless (P_rest x ξ)}.
  Context `{!∀ c, Timeless (Q1 c)} `{!Timeless Q2}.

  Implicit Types (γ : box_names) (m : gmap (id * nat) ufrac).

  (* CtxBox's parameterized definitions, at this section's parameters *)
  Local Notation is_box := (CtxBox.is_box P_hdr P_rest Q1 Q2).
  Local Notation box_arm := (CtxBox.box_arm P_hdr P_rest Q1 Q2).
  Local Notation box_body := (CtxBox.box_body P_hdr P_rest Q1 Q2).
  Local Notation in_arm := (CtxBox.in_arm P_hdr P_rest).
  Local Notation in_arm_of := (CtxBox.in_arm_of P_rest).

  (* the open, as in CtxBox *)
  Local Ltac box_open Hbox Hcl :=
    iInv Hbox as (T ξb m cb rb sb)
      "(>Hpk & >#Hllb & >Hst & >Hc & >Hrd & >Hrp & >%Hrows & Harm)" Hcl;
    lazymatch goal with
    | Hr : box_rows _ _ _ _ _ |- _ => destruct Hr as (Hsum & HI & HC & HD)
    end;
    iEval (rewrite /CtxBox.box_arm) in "Harm".

  (* the floor → view bound plumbing (CtxBox's, which is Local there) *)
  Local Lemma floor_view `{CID : CpuId} (ξ : CtxId) (K : nat) :
    own_context ξ -∗ ctx_floor ξ K -∗
    own_context ξ ∗ ∃ K' : nat, ⌜(K ≤ K')%nat⌝ ∗ hart_view_lb K'.
  Proof.
    iIntros "Hrun #Hfl".
    iDestruct (own_context_floor_view with "Hrun Hfl") as "[Hrun (%K' & #HK & %HKK)]".
    iFrame "Hrun". iExists K'. iSplitR; [done|].
    rewrite hart_view_lb_unseal /hart_view_lb_def. iExact "HK".
  Qed.

  (* ================================================================== *)
  (*  (a) withdraw_L1 : IN → OUT_L1, under L1 -- WITH THE HOOK             *)
  (* ================================================================== *)
  (* The hook runs at ξb on the header the arm holds: from the caller's Qc
     and P_hdr it returns the header that travels (P_hdr', CtxMorph) and the
     OUT_L1 residue Q1 c that stays.  Plain (a): Qc := Q1 c, P_hdr' := P_hdr. *)
  Lemma box_withdraw_L1_hook `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (mD : gmap (id * nat) ufrac) (Kd Kt : nat)
      (P_hdr' : id → X → CtxId → iProp Σ) `{!∀ i x, CtxMorph (P_hdr' i x)}
      (Qc : iProp Σ) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    qsum mD = nat_Qc c →
    (sr_td r ≤ Kd)%nat →
    (max_stamp mD ≤ Kt)%nat →
    (∀ (x : X) (ξ' : CtxId),
        Qc ∗ P_hdr (sr_ident r) x ξ' ={E ∖ ↑N}=∗ P_hdr' (sr_ident r) x ξ' ∗ Q1 c) →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kd -∗
    ctx_floor ξ Kt -∗
    llb loglen_name (max_stamp mD) -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    stamps_frag γ mD -∗
    Qc ={E}=∗
    own_context ξ ∗
    cnt_half γ c ∗
    ∃ (x0 : X) (T0 : nat),
      ⌜(T0 ≤ Nat.max Kd Kt)%nat⌝ ∗
      slotd_half γ (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T0))) ∗
      P_hdr' (sr_ident r) x0 ξ.
  Proof.
    iIntros (HE Hw HmD HKd HKt Hhook) "#Hbox Hrun #Hfld #Hflt #HllbD Hrd0 Hcnt HfD HQc".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    iDestruct (stamps_frag_incl with "Hst HfD") as %HinclD.
    destruct (lr_hold sb) as [[i0 m0]|] eqn:Hh.
    { (* OUT_L2: the parked fragment's mass beside all c units overflows Σ *)
      iDestruct "Harm" as "(_ & >%Hne0 & _ & >Hf0 & _)".
      iDestruct (stamps_frag_incl_2 with "Hst HfD Hf0") as %Hincl2.
      exfalso. apply qsum_incl_le in Hincl2. rewrite qsum_op HmD Hsum in Hincl2.
      exact (Qc_plus_pos_not_le_r _ _ (qsum_pos _ Hne0) Hincl2). }
    iEval (rewrite Hw) in "Harm". iDestruct "Harm" as ">Hin".
    (* the cover: (D) -- and its pure export, the window's stamp bound (F30) *)
    assert (HTmax : (T ≤ Nat.max Kd Kt)%nat).
    { destruct HD as [HD | (p & Hp & HpT)]; [lia|].
      assert (Hp' : p ∈ dom mD).
      { apply (qsum_eq_dom mD m HinclD); [by rewrite HmD Hsum | exact Hp]. }
      pose proof (max_stamp_ge mD p Hp'). lia. }
    iAssert (own_context ξ ∗ ∃ K : nat, ⌜(T ≤ K)%nat⌝ ∗ hart_view_lb K)%I
      with "[Hrun]" as "[Hrun (%K & %HTK & #HKv)]".
    { destruct HD as [HD | (p & Hp & HpT)].
      - iDestruct (floor_view ξ Kd with "Hrun Hfld") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia.
      - assert (Hp' : p ∈ dom mD).
        { apply (qsum_eq_dom mD m HinclD); [by rewrite HmD Hsum | exact Hp]. }
        pose proof (max_stamp_ge mD p Hp').
        iDestruct (floor_view ξ Kt with "Hrun Hflt") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia. }
    iDestruct "Hin" as (x0) "[Hhdr Hrest]".
    (* THE HOOK, at the box's context, before the absorb *)
    iMod (Hhook x0 ξb with "[$HQc $Hhdr]") as "[Hhdr' HQ]".
    iMod (ctx_absorb_lb (P_hdr' (sr_ident r) x0) ξb ξ T K HTK with "Hrun HKv Hpk Hhdr'")
      as "(Hrun & Hpk & Hhdr')".
    iMod (ghost_var_update_2 (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T))) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HfD Hrest HQ]") as "_".
    { iNext. iExists T, ξb, m, c, (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T))), sb.
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /CtxBox.box_arm.
      rewrite Hh. simpl.
      iSplitL "HfD".
      { iExists mD. iSplitR; [iPureIntro; by rewrite HmD Hsum|]. iFrame "HfD". iExact "HllbD". }
      iSplitL "Hrest"; [iExists x0; iFrame "Hrest"; done | iExact "HQ"]. }
    iModIntro. iFrame "Hrun Hcnt". iExists x0, T. iFrame "Hrd0 Hhdr'". iPureIntro. exact HTmax.
  Qed.

  (* (a) plain: CtxBox.box_withdraw_L1, verbatim -- the identity hook *)
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
    Q1 c ={E}=∗
    own_context ξ ∗
    cnt_half γ c ∗
    ∃ (x0 : X) (T0 : nat),
      ⌜(T0 ≤ Nat.max Kd Kt)%nat⌝ ∗
      slotd_half γ (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T0))) ∗
      P_hdr (sr_ident r) x0 ξ.
  Proof.
    intros HE Hw HmD HKd HKt.
    apply (box_withdraw_L1_hook N γ ξ r c mD Kd Kt P_hdr (Q1 c) E HE Hw HmD HKd HKt).
    intros x ξ'. iIntros "[HQ Hh]". iModIntro. iFrame.
  Qed.

  (* ================================================================== *)
  (*  (b) deposit_L1 : OUT_L1 → IN, under L1 -- WITH THE HOOK              *)
  (* ================================================================== *)
  (* The hook runs before the deposit, with everything the transition
     touches in hand: the caller's Qc, the arm's residue Q1 c, the caller's
     header-so-far P_hdr' at ξ, and the arm's P_rest at the register's shape
     x0 at ξb.  It returns the whole header at the target shape x1 (at ξ),
     P_rest at x1 (at ξb) and what the caller keeps, Q'.  The shape change
     x0 → x1 (F14) is thereby part of the hook; the plain forms supply the
     entailment and frame the rest.  The icache recycle (§6²⁴) rebuilds its
     header from Q1 0's live arm here; the residue's quarter is the one it
     could not otherwise reach. *)
  Lemma box_deposit_L1_hook `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 x1 : X) (T0 : nat)
      (P_hdr' : id → X → CtxId → iProp Σ) (Qc Q' : iProp Σ) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (∀ ξb : CtxId,
        Qc ∗ Q1 c ∗ P_hdr' i' x1 ξ ∗ P_rest x0 ξb ={E ∖ ↑N}=∗
        P_hdr i' x1 ξ ∗ P_rest x1 ξb ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    Qc -∗
    P_hdr' i' x1 ξ ={E}=∗
    own_context ξ ∗ Q' ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hhook) "#Hbox Hrun Hrd0 Hcnt HQc Hhdr'".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    destruct (lr_hold sb) as [[i0 m0]|] eqn:Hh.
    { (* OUT_L2 records win = false; the caller's half says true *)
      iDestruct "Harm" as "(>%Hwf & _)". congruence. }
    iEval (rewrite Hw) in "Harm".
    iDestruct "Harm" as "(>Hho & >Hrest & >HQ)". iDestruct "Hrest" as (x) "[%Hx' Hrest]".
    assert (x = x0) as -> by congruence.
    (* THE HOOK: the residue, the header-so-far and the rest, before the deposit *)
    iMod (Hhook ξb with "[$HQc $HQ $Hhdr' $Hrest]") as "(Hhdr & Hrest & HQ')".
    iDestruct "Hho" as (m') "(%Hsum' & Hf' & _)".
    iMod (stamps_dealloc with "Hst Hf'") as (m1) "(Hst & %Hq1 & _ & _)".
    assert (m1 = ∅) as ->.
    { apply qsum_zero_empty. rewrite Hsum' in Hq1.
      apply (Qc_plus_cancel_l (qsum m)). by rewrite Hq1 Qcplus_0_r. }
    iMod (ctx_deposit (P_hdr i' x1) ξ ξb T with "Hrun Hpk Hhdr")
      as "(Hrun & %T' & %HTT' & Hpk & Hhdr)".
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb']".
    iMod (own_update _ _ _ (stamps_alloc_upd ∅ (i', T') (unit_mass c)) with "Hst") as "[Hst Hfr]".
    iEval (rewrite right_id) in "Hst".
    iMod (ghost_var_update_2 (SlotReg T' false i' None) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 (Nat.max 1 c) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hhdr Hrest]") as "_".
    { iNext. iExists T', ξb, {[(i', T') := unit_mass c]}, (Nat.max 1 c), (SlotReg T' false i' None), sb.
      iFrame "Hpk Hllb' Hst Hc Hrd Hrp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - rewrite -insert_empty (qsum_insert ∅ _ _ (lookup_empty _)) qsum_empty Qcplus_0_r.
          apply unit_mass_Qc.
        - apply keyed_singleton.
        - left. intros p Hp. rewrite dom_singleton_L in Hp.
          apply elem_of_singleton in Hp. subst p. simpl. lia.
        - left. cbn [sr_td]. lia. }
      rewrite /CtxBox.box_arm Hh. simpl. iExists x1. iFrame "Hhdr Hrest". }
    iModIntro. iFrame "Hrun HQ'". iExists T'. iFrame "Hrd0 Hcnt".
    iSplitL "Hfr"; [| iExact "Hllb'"].
    rewrite /CtxBox.reference. iFrame "Hfr".
    iSplitR; [iPureIntro; apply singleton_ne_empty_map|].
    iSplitR; [iPureIntro; apply keyed_singleton|].
    rewrite max_stamp_singleton. iExact "Hllb'".
  Qed.

  (* (b′) plain: CtxBox.box_deposit_L1_shape, verbatim -- Qc := emp,
     P_hdr' := P_hdr, Q' := Q1 c, the hook frames and applies F14's entailment *)
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
    own_context ξ ∗ Q1 c ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE Hw Hx Hent.
    iIntros "#Hbox Hrun Hrd0 Hcnt Hhdr".
    iApply (box_deposit_L1_hook N γ ξ r c i' x0 x1 T0 P_hdr emp (Q1 c) E HE Hw Hx
              with "Hbox Hrun Hrd0 Hcnt [//] Hhdr").
    intros ξb. iIntros "(_ & HQ & Hh & Hr)". iModIntro. iFrame "Hh HQ". by iApply Hent.
  Qed.

  (* (b) plain: CtxBox.box_deposit_L1, verbatim -- x1 := x0 *)
  Lemma box_deposit_L1 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 : X) (T0 : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    P_hdr i' x0 ξ ={E}=∗
    own_context ξ ∗ Q1 c ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE Hw Hx.
    apply (box_deposit_L1_shape N γ ξ r c i' x0 x0 T0 E HE Hw Hx).
    intros ξb. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  (e) checkout : IN → OUT_L2, under L2 -- WITH THE HOOK                *)
  (* ================================================================== *)
  (* CtxBox.box_checkout_split, verbatim: the hook at ξb, before the absorb,
     splits the header into the part that travels (P_hdr', CtxMorph) and
     the OUT_L2 residue Q2 built beside the caller's Qc.  A view shift at
     the box's mask (§6²¹: the read arm refutes the frozen alternative
     with itable_inv open).  Plain (e): Qc := Q2, P_hdr' := P_hdr. *)
  Lemma box_checkout_hook `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) `{!∀ i x, CtxMorph (P_hdr' i x)}
      (Qc : iProp Σ)
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    (∀ (x : X) (ξ' : CtxId), Qc ∗ P_hdr i x ξ' ={E ∖ ↑N}=∗ P_hdr' i x ξ' ∗ Q2) →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    Qc -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof.
    iIntros (HE Hs0 HKt HKp Hhook) "#Hbox Hrun #Hflt #Hflp Href HQc Hrp0".
    iDestruct "Href" as "(%Hne & %Hkeyed & Hfh & #Hllbh)".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iDestruct (stamps_frag_incl with "Hst Hfh") as %Hinclh.
    iEval (rewrite Hs0 /=) in "Harm".
    destruct (sr_win rb) eqn:Hw.
    { (* OUT_L1: the window's fragment carries all of Σ; mine overflows it *)
      iDestruct "Harm" as "(>Hho & _ & _)". iDestruct "Hho" as (m') "(%Hsum' & Hf' & _)".
      iDestruct (stamps_frag_incl_2 with "Hst Hf' Hfh") as %Hincl2.
      exfalso. apply qsum_incl_le in Hincl2. rewrite qsum_op Hsum' in Hincl2.
      exact (Qc_plus_pos_not_le_r _ _ (qsum_pos _ Hne) Hincl2). }
    iDestruct "Harm" as ">Hin".
    (* the identity (F6): my keys are live, so they name the box's identity *)
    assert (Hid : i = sr_ident rb).
    { eapply keyed_agree; [exact Hne | exact (gincl_dom _ _ Hinclh) | exact Hkeyed | exact HI]. }
    (* the cover: (C) *)
    iAssert (own_context ξ ∗ ∃ K : nat, ⌜(T ≤ K)%nat⌝ ∗ hart_view_lb K)%I
      with "[Hrun]" as "[Hrun (%K & %HTK & #HKv)]".
    { destruct HC as [HC | HC].
      - destruct (map_choose mh Hne) as (p & q & Hp).
        assert (Hpd : p ∈ dom mh) by (apply elem_of_dom; by exists q).
        pose proof (HC p (gincl_dom _ _ Hinclh p Hpd)). pose proof (max_stamp_ge mh p Hpd).
        iDestruct (floor_view ξ Kt with "Hrun Hflt") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia.
      - iDestruct (floor_view ξ Kp with "Hrun Hflp") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia. }
    (* THE HOOK, at the box's context: the residue stays, the rest is absorbed *)
    iEval (rewrite -Hid /CtxBox.in_arm) in "Hin". iDestruct "Hin" as (x) "[Hhdr Hrest]".
    iMod (Hhook x ξb with "[$HQc $Hhdr]") as "[Hhdr' HQ]".
    iMod (ctx_absorb_lb (in_arm_of P_hdr' i) ξb ξ T K HTK with "Hrun HKv Hpk [Hhdr' Hrest]")
      as "(Hrun & Hpk & Hin')".
    { rewrite /CtxBox.in_arm_of. iExists x. iFrame "Hhdr' Hrest". }
    iMod (ghost_var_update_2 (L2Reg (lr_tp s0) (Some (i, mh))) with "Hrp Hrp0")
      as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HQ Hfh]") as "_".
    { iNext. iExists T, ξb, m, cb, rb, (L2Reg (lr_tp s0) (Some (i, mh))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /CtxBox.box_arm.
      iFrame "Hfh HQ". iPureIntro. split_and!; done. }
    iModIntro. iFrame "Hrun". iSplitL "Hin'". { rewrite /CtxBox.in_arm_of. iExact "Hin'". }
    rewrite /CtxBox.l2_hold. iExists (lr_tp s0). iFrame "Hrp0". iExact "Hllbh".
  Qed.

  (* (e′) plain: CtxBox.box_checkout_split, verbatim (the same statement) *)
  Lemma box_checkout_split `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) `{!∀ i x, CtxMorph (P_hdr' i x)}
      (Qc : iProp Σ)
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    (∀ (x : X) (ξ' : CtxId), Qc ∗ P_hdr i x ξ' ={E ∖ ↑N}=∗ P_hdr' i x ξ' ∗ Q2) →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    Qc -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof. exact (box_checkout_hook N γ ξ i P_hdr' Qc mh s0 Kt Kp E). Qed.

  (* (e) plain: CtxBox.box_checkout, verbatim -- Qc := Q2, P_hdr' := P_hdr.
     (In CtxBox this is proven directly because the split wand was pure
     when (e) was written; at a view-shift hook it is the identity instance.) *)
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
    Q2 -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof.
    intros HE Hs0 HKt HKp.
    apply (box_checkout_hook N γ ξ i P_hdr Q2 mh s0 Kt Kp E HE Hs0 HKt HKp).
    intros x ξ'. iIntros "[HQ Hh]". iModIntro. iFrame.
  Qed.

  (* ================================================================== *)
  (*  (f) park : OUT_L2 → IN, under L2 -- WITH THE HOOK                    *)
  (* ================================================================== *)
  (* CtxBox.box_park_join with the join as a VIEW SHIFT: at the holder's ξ,
     before the deposit, the hook sees the caller's Qc' (F43: the icache's
     descriptor half, which selects the arm within Q2), the split header
     P_hdr' and the arm's Q2, and returns the whole header and what the
     caller keeps, Q'.  Plain (f′): the entailment lifted; plain (f):
     Qc' := emp, P_hdr' := P_hdr, Q' := Q2. *)
  Lemma box_park_hook `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) (Qc' Q' : iProp Σ)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    (∀ (x : X) (ξ' : CtxId), Qc' ∗ P_hdr' i x ξ' ∗ Q2 ={E ∖ ↑N}=∗ P_hdr i x ξ' ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) -∗
    Qc' -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q' ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hhook) "#Hbox Hrun Hbun HQc Hhold".
    iDestruct "Hhold" as (tp) "[Hrp0 #Hllbh]".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    (* the register selects OUT_L2: nothing to refute *)
    iEval (cbn [lr_hold]) in "Harm".
    iDestruct "Harm" as "(>%Hwf & >%Hne0 & >%Hkeyed0 & >Hf0 & >HQ)".
    iDestruct (stamps_frag_incl with "Hst Hf0") as %Hincl0.
    (* the identity (F13): the parked keys are live, so they name the box's *)
    assert (Hid : i = sr_ident rb).
    { eapply keyed_agree; [exact Hne0 | exact (gincl_dom _ _ Hincl0) | exact Hkeyed0 | exact HI]. }
    (* THE HOOK, at the holder's context, with the arm's residue *)
    iDestruct "Hbun" as (x) "[Hhdr' Hrest]".
    iMod (Hhook x ξ with "[$HQc $Hhdr' $HQ]") as "[Hhdr HQ']".
    iMod (ctx_deposit (in_arm i) ξ ξb T with "Hrun Hpk [Hhdr Hrest]")
      as "(Hrun & %T' & %HTT' & Hpk & Hbun)".
    { rewrite /CtxBox.in_arm. iExists x. iFrame "Hhdr Hrest". }
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb']".
    iMod (stamps_dealloc with "Hst Hf0") as (m1) "(Hst & %Hq1 & %Hdom1 & _)".
    set (q := mk_Qp (qsum mh) (qsum_pos mh Hne0)).
    iMod (own_update _ _ _ (stamps_alloc_upd m1 (i, T') q) with "Hst") as "[Hst Hfr]".
    iMod (ghost_var_update_2 (L2Reg T' None) with "Hrp Hrp0") as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hbun]") as "_".
    { iNext. iExists T', ξb, ({[(i, T') := q]} ⋅ m1), cb, rb, (L2Reg T' None).
      iFrame "Hpk Hllb' Hst Hc Hrd Hrp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - rewrite qsum_singleton_op. simpl. rewrite Hq1. exact Hsum.
        - rewrite Hid. apply keyed_singleton_op. exact (keyed_sub _ _ _ Hdom1 HI).
        - right. cbn [lr_tp]. lia.
        - right. exists (i, T'). split; [| done].
          rewrite dom_op dom_singleton_L. apply elem_of_union_l. by apply elem_of_singleton. }
      rewrite /CtxBox.box_arm. simpl. rewrite Hwf -Hid. iExact "Hbun". }
    iModIntro. iFrame "Hrun HQ'". iExists T', q. iFrame "Hrp0".
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "Hfr"; [| iExact "Hllb'"].
    rewrite /CtxBox.reference. iFrame "Hfr".
    iSplitR; [iPureIntro; apply singleton_ne_empty_map|].
    iSplitR; [iPureIntro; apply keyed_singleton|].
    rewrite max_stamp_singleton. iExact "Hllb'".
  Qed.

  (* (f′) plain: CtxBox.box_park_join, verbatim -- the pure join, lifted *)
  Lemma box_park_join `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) (Qc' Q' : iProp Σ)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    (∀ (x : X) (ξ' : CtxId), Qc' ∗ P_hdr' i x ξ' ∗ Q2 ⊢ P_hdr i x ξ' ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) -∗
    Qc' -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q' ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE Hjoin.
    apply (box_park_hook N γ ξ i P_hdr' Qc' Q' mh E HE).
    intros x ξ'. iIntros "H". iModIntro. by iApply Hjoin.
  Qed.

  (* (f) plain: CtxBox.box_park, verbatim -- Qc' := emp, P_hdr' := P_hdr, Q' := Q2 *)
  Lemma box_park `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q2 ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE.
    iIntros "#Hbox Hrun Hbun Hhold".
    iApply (box_park_hook N γ ξ i P_hdr emp Q2 mh E HE with "Hbox Hrun Hbun [//] Hhold").
    intros x ξ'. iIntros "(_ & Hh & HQ)". iModIntro. iFrame.
  Qed.

  (* ================================================================== *)
  (*  (g) l1_to_l2 : OUT_L1 → OUT_L2, under BOTH locks -- WITH THE HOOK     *)
  (* ================================================================== *)
  (* The header is out and stays out; P_rest travels as before.  The hook
     runs at the caller's ξ on the RESIDUES: from the caller's Qc and the
     window's Q1 1 it returns the OUT_L2 residue Q2 and what the caller
     keeps, Q'.  Plain (g): Qc := Q2, Q' := Q1 1 (the exchange).  Stated at
     c = 1, where the free path runs (CtxBox's statement). *)
  Lemma box_l1_to_l2_hook `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (x0 : X) (T0 K : nat) (s0 : l2_reg id) (Qc Q' : iProp Σ) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (T0 ≤ K)%nat →
    lr_hold s0 = None →
    (Qc ∗ Q1 1 ={E ∖ ↑N}=∗ Q2 ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ K -∗
    slotd_half γ r -∗
    cnt_half γ 1 -∗
    Qc -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗ Q' ∗
    P_rest x0 ξ ∗
    slotd_half γ (SlotReg (sr_td r) false (sr_ident r) None) ∗
    cnt_half γ 1 ∗
    ∃ m', ⌜qsum m' = nat_Qc 1⌝ ∗ l2_hold γ (sr_ident r) m'.
  Proof.
    iIntros (HE Hw Hx HTK Hs0 Hhook) "#Hbox Hrun #Hfl Hrd0 Hcnt HQc Hrp0".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iEval (rewrite Hs0 /= Hw) in "Harm".
    iDestruct "Harm" as "(>Hho & >Hrest & >HQo)". iDestruct "Hrest" as (x) "[%Hx' Hrest]".
    rewrite Hx in Hx'. injection Hx' as -> ->.
    iDestruct "Hho" as (m') "(%Hsum' & Hf' & #Hllb')".
    iDestruct (stamps_frag_incl with "Hst Hf'") as %Hincl'.
    assert (Hne' : m' ≠ ∅).
    { intros ->. rewrite qsum_empty Hsum nat_Qc_1 in Hsum'.
      assert (H01 : (0 < 1)%Qc) by (vm_compute; reflexivity).
      exact (Qclt_not_eq _ _ H01 Hsum'). }
    assert (Hkeyed' : keyed m' (sr_ident r))
      by exact (keyed_sub _ _ _ (gincl_dom _ _ Hincl') HI).
    (* THE HOOK: the residues, at the caller's context *)
    iMod (Hhook with "[$HQc $HQo]") as "[HQn HQ']".
    (* the cover: the register's stamp IS the box's, under the caller's floor *)
    iDestruct (floor_view ξ K with "Hrun Hfl") as "[Hrun (%K' & %HKK' & #HKv)]".
    iMod (ctx_absorb_lb (P_rest x) ξb ξ T K' ltac:(lia) with "Hrun HKv Hpk Hrest")
      as "(Hrun & Hpk & Hrest)".
    iMod (ghost_var_update_2 (SlotReg (sr_td r) false (sr_ident r) None) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 (L2Reg (lr_tp s0) (Some (sr_ident r, m'))) with "Hrp Hrp0")
      as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HQn Hf']") as "_".
    { iNext. iExists T, ξb, m, 1, (SlotReg (sr_td r) false (sr_ident r) None),
               (L2Reg (lr_tp s0) (Some (sr_ident r, m'))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /CtxBox.box_arm.
      iFrame "Hf' HQn". iPureIntro. split_and!; done. }
    iModIntro. iFrame "Hrun HQ' Hrest Hrd0 Hcnt". iExists m'.
    iSplitR; [iPureIntro; by rewrite Hsum' Hsum|].
    rewrite /CtxBox.l2_hold. iExists (lr_tp s0). iFrame "Hrp0". iExact "Hllb'".
  Qed.

  (* (g) plain: CtxBox.box_l1_to_l2, verbatim -- Qc := Q2, Q' := Q1 1 *)
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
    Q2 -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗ Q1 1 ∗
    P_rest x0 ξ ∗
    slotd_half γ (SlotReg (sr_td r) false (sr_ident r) None) ∗
    cnt_half γ 1 ∗
    ∃ m', ⌜qsum m' = nat_Qc 1⌝ ∗ l2_hold γ (sr_ident r) m'.
  Proof.
    intros HE Hw Hx HTK Hs0.
    apply (box_l1_to_l2_hook N γ ξ r x0 T0 K s0 Q2 (Q1 1) E HE Hw Hx HTK Hs0).
    iIntros "[HQ2 HQ1]". iModIntro. iFrame.
  Qed.

  (* ================================================================== *)
  (*  THE OUT_L1 RESIDUE ACCESSOR (§6²⁴ Q8, accepted §6²⁵/§6²⁶/§6²⁷)        *)
  (* ================================================================== *)
  (* box_q_update's L1 twin.  The window's holder presents the L1 register
     half at win = true and the count half -- both returned, so the arm and
     the count are fixed by agreement -- and rewrites Q1 c in place through
     a fupd at the box's mask, handing an output residue R out.  The icache
     recycle trades Q1 0's dead arm for its live arm here (the pool opened
     inside), between its (a) and its (b).  Non-transition: no arm, stamp,
     register or row moves. *)
  Lemma box_q1_update (N : namespace) γ (r : slot_reg id X) (c : nat) (R : iProp Σ) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    is_box N γ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    (Q1 c ={E ∖ ↑N}=∗ Q1 c ∗ R) ={E}=∗
    slotd_half γ r ∗ cnt_half γ c ∗ R.
  Proof.
    iIntros (HE Hw) "#Hbox Hrd0 Hcnt Hupd".
    rewrite /CtxBox.is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    destruct (lr_hold sb) as [[i0 m0]|] eqn:Hh.
    { (* OUT_L2 records win = false; the caller's half says true *)
      iDestruct "Harm" as "(>%Hwf & _)". congruence. }
    iEval (rewrite Hw) in "Harm".
    iDestruct "Harm" as "(>Hho & >Hrest & >HQ)".
    iMod ("Hupd" with "HQ") as "[HQ HR]".
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hho Hrest HQ]") as "_".
    { iNext. iExists T, ξb, m, c, r, sb.
      iFrame "Hpk Hllb Hst Hc Hrd Hrp".
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /CtxBox.box_arm Hh Hw. iFrame "Hho Hrest HQ". }
    iModIntro. iFrame "Hrd0 Hcnt HR".
  Qed.

End hooked.
