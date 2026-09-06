(* TsoCtxTwin4.v -- THE FOURTH TWIN: the two-log ghost layer over the
   context surface as it stands on main (claude-notes/projects/relaxed-ww.md
   §2, order of work item 2).

   [TsoCtxTwin3.v] proved that the context machinery survives the split of
   a store's IDENTITY (its issue index) from its COHERENCE POSITION (its
   drain position), but did so over the pre-contexts surface: an
   author-indexed parked record, a per-author release receipt and an
   author index on domination.  The context abstractions that landed
   since (claude-notes/design/contexts.md: one domination relation,
   [ctx_parked ξ ξ'], the per-lock context, the release hook) make all
   three unnecessary, and this file is the design record of WHY -- the
   landed [TsoCtx.v] shapes restated over the two-log machine, with
   exactly the changes relaxed-ww.md §2 prescribes:

     - ONE PROPOSITION.  [key_at ξ' k] -- "key [k] is justified at ξ'" --
       is the clean/dirty bit of a fact and the body of domination.  Its
       clean arm becomes "drained at a position under ξ''s bound"
       ([dpos_ev k.1 p ∗ ctx_floor ξ' p]); its dirty arm is unchanged.
     - THE THREE TOKENS keep their statements.  [own_context]'s dirty
       WATERMARK row is dropped (nothing consumes it once the interp-free
       stamps are gone); [ctx_stamped ξ T] hangs on a DRAIN position with
       every key drained under it; [ctx_parked ξ ξ'] is the relation at
       full authority, unchanged.
     - THE MINTS.  Mint 1 (same hart: [ctx_park], [ctx_dom_run], hence
       [ctx_move]), mint 3 (out of a stamped root at a view receipt:
       [ctx_dom_of_stamped_lb]) and mint 4 ([ctx_parked_borrow]) are
       unchanged and interp-free.  Exactly two ghost steps become
       FENCE-BOUND: [ctx_stamp] (running → stamped) and mint 2
       ([ctx_dom_to_stamped], a deposit into a stamped root).  Both take
       the interp and the fence's enabling fact [own_drained]: every key
       of the running context is this hart's own message, drained by the
       fence, with its [dpos_at] witness in the interp.
     - THE FENCE RECORD.  [fence_rec N M] -- "every message with issue
       index ≥ N drains at a position > M" -- is the one author-free
       receipt the racy tiers need, mintable at ANY leaf (a message that
       does not exist yet drains later) and maintained by the interp for
       free.  It is the twin's [drain_lb] with the author dropped.
     - NO AUTHOR INDEX ANYWHERE: [ctx_dom ξ ξ'] is the landed shape, and
       [CtxMorph] its bare update.

   The acid tests at the end are the two halves of the lock path (§2.4):
   a pending store moves into the lock's context, is published at the
   releaser's fence, and is read on the winner's hart at every view above
   its own -- plus the tripwire that the fence really waits (a hart with
   a pending store is NOT [own_drained]).

   Everything the pure layer needs ([latest], [chain_ok], [fifo_ok],
   [tso_read_of_latest], [dpos_ok], the view RA) is [TsoCtxTwin3]'s and is
   imported, as are its gname-free ghost helpers ([nlb], [dset_*],
   [ctx_at], [view_lb], [view_auth], [author], [dpos_at]).  The ghost
   layer below supersedes [TsoCtxTwin3] §3–§17. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.algebra Require Import auth dfrac numbers functions gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map mono_nat.
From xv6iris Require Import TsoMem TsoCtxTwin3.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * 0.  The pure layer: the fence record's mirror                    *)
(* ================================================================== *)

(** [FR] mirrors the fence records: an entry at [(N, M)] says every
    message with issue index [≥ N] drains at a position [> M].  Sound at
    the mint because [N] is the issue length (no such message exists) and
    [M] the drain length; kept by every later step because [M] only falls
    behind the drain top.  The entry's value is irrelevant. *)
Definition fr_ok (dl : list nat) (FR : gmap (agent * nat) nat) : Prop :=
  ∀ N M v, FR !! (N, M) = Some v →
    (M ≤ length dl)%nat ∧
    ∀ i q, dl !! q = Some i → (N ≤ i)%nat → (M < S q)%nat.

Lemma fr_ok_drain dl FR k : fr_ok dl FR → fr_ok (dl ++ [k]) FR.
Proof.
  move => Hfr N M v HNM. destruct (Hfr _ _ _ HNM) as [HM Hall]. split.
  - rewrite length_app /=. lia.
  - move => i q Hq HNi. apply lookup_app_last' in Hq as [[_ Hq]|[-> _]].
    + by eapply Hall.
    + lia.
Qed.

Lemma fr_ok_mint log dl FR v :
  dl_ok log dl → fr_ok dl FR →
  fr_ok dl (<[(length log, length dl) := v]> FR).
Proof.
  move => [_ Hlt] Hfr N M v'.
  destruct (decide ((N, M) = (length log, length dl))) as [[= -> ->]|Hne].
  - rewrite lookup_insert => _. split; [done|].
    move => i q Hq HNi. exfalso.
    have := Hlt _ (elem_of_list_lookup_2 _ _ _ Hq). lia.
  - rewrite lookup_insert_ne; last done. by apply Hfr.
Qed.

(** THE TRIPWIRE: a hart with a pending store is not drained.  This is
    what makes the release fence wait, and what makes [ctx_stamp]'s
    premise a real one. *)
Lemma own_drained_store_false log dl h a data :
  dl_ok log dl → ¬ own_drained h (store_log log h a data) dl.
Proof.
  move => [_ Hlt] Hod.
  have Hi : store_log log h a data !! length log = Some (WMsg a data h)
    by apply list_lookup_middle.
  have := own_drained_lookup _ _ _ _ _ Hod Hi eq_refl.
  move => /Hlt. lia.
Qed.

(* ================================================================== *)
(** * 1.  The ghost layer                                              *)
(* ================================================================== *)

Section twin4.
  Context {Σ : gFunctors} `{!tsoCtx3G Σ}.
  (* [γfr] takes the class's receipt-map slot: its keys are [(N, M)]
     pairs, at [agent * nat = nat * nat]. *)
  Context (γheap γlogm γdpos γfr γloglen γdlen γview : gname).

  Notation llb := (nlb γloglen).
  Notation dlb := (nlb γdlen).
  Notation view_lb := (TsoCtxTwin3.view_lb γdlen γview).
  Notation view_auth := (TsoCtxTwin3.view_auth γview).
  Notation author := (TsoCtxTwin3.author γlogm).
  Notation dpos_at := (TsoCtxTwin3.dpos_at γdpos).

  (* [nlb_valid] at a fraction of the authority -- what a half-borrow
     reads a floor against. *)
  Local Lemma nlb_valid_q (γ : gname) (q : Qp) (n K : nat) :
    mono_nat_auth_own γ q n -∗ nlb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  Local Lemma view_lb_join h K1 K2 :
    view_lb h K1 -∗ view_lb h K2 -∗ view_lb h (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2".
    destruct (Nat.le_ge_cases K1 K2) as [Hle|Hle].
    - rewrite (Nat.max_r _ _ Hle). iExact "H2".
    - rewrite (Nat.max_l _ _ Hle). iExact "H1".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.1 The two receipts: a drain position, a fence record        *)
  (* ---------------------------------------------------------------- *)

  (** THE TIE BETWEEN THE NUMBER LINES, author-free: issue timestamp [t]'s
      message is the image or is drained at a position under [B]. *)
  Definition dpos_ev (t B : nat) : iProp Σ :=
    (⌜t = 0%nat⌝ ∨ ∃ i p, ⌜t = S i⌝ ∗ dpos_at i p ∗ ⌜(p ≤ B)%nat⌝)%I.
  Global Instance dpos_ev_persistent t B : Persistent (dpos_ev t B).
  Proof. apply _. Qed.
  Global Instance dpos_ev_timeless t B : Timeless (dpos_ev t B).
  Proof. apply _. Qed.

  Lemma dpos_ev_mono t B B' : (B ≤ B')%nat → dpos_ev t B -∗ dpos_ev t B'.
  Proof.
    iIntros (Hle) "[%|(%i & %p & % & #H & %)]".
    - by iLeft.
    - iRight. iExists i, p. iFrame "H". iPureIntro. split; [done|lia].
  Qed.

  Lemma dpos_ev_0 B : ⊢ dpos_ev 0 B.
  Proof. by iLeft. Qed.

  (** THE FENCE RECORD: every message with issue index [≥ N] drains at a
      position [> M].  Persistent; [N] and [M] are the lengths of the two
      logs at the mint. *)
  Definition fence_rec (N M : nat) : iProp Σ := (∃ v, (N, M) ↪[γfr]□ v)%I.
  Global Instance fence_rec_persistent N M : Persistent (fence_rec N M).
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.2 The tokens (contexts.md §1) and the one proposition (§2)  *)
  (* ---------------------------------------------------------------- *)

  (** THE CONTEXT FLOOR: "ξ's bound has passed [lo]" -- a drain position. *)
  Definition ctx_floor (ξ : CtxId) (lo : nat) : iProp Σ := nlb (tc_bnd ξ) lo.
  Global Instance ctx_floor_persistent ξ lo : Persistent (ctx_floor ξ lo).
  Proof. apply _. Qed.
  Global Instance ctx_floor_timeless ξ lo : Timeless (ctx_floor ξ lo).
  Proof. apply _. Qed.
  Lemma ctx_floor_0 ξ : ⊢ ctx_floor ξ 0.
  Proof. apply nlb_0. Qed.
  Lemma ctx_floor_le ξ lo lo' : (lo' ≤ lo)%nat → ctx_floor ξ lo -∗ ctx_floor ξ lo'.
  Proof. apply nlb_le. Qed.

  (** A DIRTY ENTRY'S JUSTIFICATION on hart [h] under bound [B]: drained
      under the bound, or [h]'s own message (forwarding, pending or not). *)
  Definition dirty_ok (h B : nat) (k : nat * Z) : iProp Σ :=
    (dpos_ev k.1 B ∨ ∃ i, ⌜k.1 = S i⌝ ∗ author i h)%I.
  Global Instance dirty_ok_persistent h B k : Persistent (dirty_ok h B k).
  Proof. apply _. Qed.

  Lemma dirty_ok_mono h B B' k : (B ≤ B')%nat → dirty_ok h B k -∗ dirty_ok h B' k.
  Proof.
    iIntros (Hle) "[H|H]"; [iLeft; by iApply dpos_ev_mono | by iRight].
  Qed.

  (** THE RUNNING TOKEN: "hart [h] runs as ξ".  Both authorities; the bound
      (a drain position) under the hart's view receipt; every dirty entry
      justified at [h].  NO WATERMARK ROW: a clean key carries a drain
      position, which bounds nothing about its issue index, and nothing
      below consumes one. *)
  Definition own_context (ξ : CtxId) (h : agent) : iProp Σ :=
    (∃ (B K : nat) (D : gset (nat * Z)),
      ctx_at ξ 1 B D ∗
      view_lb h K ∗ ⌜(B ≤ K)%nat⌝ ∗
      [∗ set] k ∈ D, dirty_ok h B k)%I.

  (** THE STAMPED TOKEN: hung on a DRAIN position [T] -- every key drained
      under it, and [T] a legal drain position. *)
  Definition ctx_stamped (ξ : CtxId) (T : nat) : iProp Σ :=
    (∃ D : gset (nat * Z),
      ctx_at ξ 1 T D ∗ dlb T ∗ □ [∗ set] k ∈ D, dpos_ev k.1 T)%I.

  (** THE ONE PROPOSITION: key [k] is justified at ξ' -- drained at a
      position under ξ''s bound, or registered in ξ''s dirty set. *)
  Definition key_at (ξ' : CtxId) (k : nat * Z) : iProp Σ :=
    ((∃ p, dpos_ev k.1 p ∗ ctx_floor ξ' p) ∨ dset_in (tc_dirty ξ') k)%I.
  Global Instance key_at_persistent ξ' k : Persistent (key_at ξ' k).
  Proof. apply _. Qed.
  Global Instance key_at_timeless ξ' k : Timeless (key_at ξ' k).
  Proof. apply _. Qed.

  (** DOMINATION at fraction [q] (contexts.md §2), the landed body. *)
  Definition ctx_dom_at (ξ ξ' : CtxId) (q : Qp) : iProp Σ :=
    (∃ (B : nat) (D : gset (nat * Z)),
      ctx_at ξ q B D ∗ ctx_floor ξ' B ∗ □ [∗ set] k ∈ D, key_at ξ' k)%I.
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ := ctx_dom_at ξ ξ' (1/2).
  Definition ctx_parked (ξ ξ' : CtxId) : iProp Σ := ctx_dom_at ξ ξ' 1.

  (** THE FACT: the heap element (issue timestamp and value) plus its bit. *)
  Definition ctx_pointsto (ξ : CtxId) (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, a ↪[γheap]{dq} (t, v) ∗ key_at ξ (t, a))%I.

  (** A store's own key at its context ([TsoCtx.ctx_wrote]). *)
  Definition ctx_wrote (ξ : CtxId) (t : nat) (a : Z) : iProp Σ :=
    dset_in (tc_dirty ξ) (t, a).
  Global Instance ctx_wrote_persistent ξ t a : Persistent (ctx_wrote ξ t a).
  Proof. apply _. Qed.

  Global Instance own_context_timeless ξ h : Timeless (own_context ξ h).
  Proof. apply _. Qed.
  Global Instance ctx_stamped_timeless ξ T : Timeless (ctx_stamped ξ T).
  Proof. apply _. Qed.
  Global Instance ctx_dom_at_timeless ξ ξ' q : Timeless (ctx_dom_at ξ ξ' q).
  Proof. apply _. Qed.
  Global Instance ctx_pointsto_timeless ξ a dq v : Timeless (ctx_pointsto ξ a dq v).
  Proof. apply _. Qed.
  Global Instance ctx_pointsto_discarded_persistent ξ a v :
    Persistent (ctx_pointsto ξ a DfracDiscarded v).
  Proof. apply _. Qed.

  (** Exclusivity (contexts.md §2): the whole bound authority is inside. *)
  Lemma own_context_excl ξ h1 h2 : own_context ξ h1 -∗ own_context ξ h2 -∗ False.
  Proof.
    iIntros "(%B1 & %K1 & %D1 & [Hb1 _] & _) (%B2 & %K2 & %D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.
  Lemma ctx_parked_excl ξ ξ1 ξ2 : ctx_parked ξ ξ1 -∗ ctx_parked ξ ξ2 -∗ False.
  Proof.
    iIntros "(%B1 & %D1 & [Hb1 _] & _) (%B2 & %D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.
  Lemma ctx_parked_running_excl ξ ξ' h : ctx_parked ξ ξ' -∗ own_context ξ h -∗ False.
  Proof.
    iIntros "(%B1 & %D1 & [Hb1 _] & _) (%B & %K & %D & [Hb _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb").
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.3 The state interpretation -- MACHINE ONLY                  *)
  (* ---------------------------------------------------------------- *)

  Definition interp_pure (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (tvs : agent → nat) (HM : gmap Z (nat * bv 8)) (LM : gmap nat wmsg)
      (DP : gmap nat nat) (FR : gmap (agent * nat) nat) : Prop :=
    tie_ok img log dl HM ∧ (∀ i, LM !! i = log !! i) ∧ dpos_ok dl DP ∧
    fr_ok dl FR ∧ (∀ h, (tvs h ≤ length dl)%nat) ∧ dl_ok log dl ∧ fifo_ok log dl.

  (** The drain map's and the fence-record map's persistent fragments live
      IN the interp: a drain is nobody's step, and a record is re-minted on
      demand. *)
  Definition tso_interp (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (tvs : agent → nat) : iProp Σ :=
    (∃ (HM : gmap Z (nat * bv 8)) (LM : gmap nat wmsg) (DP : gmap nat nat)
       (FR : gmap (agent * nat) nat),
      ghost_map_auth γheap 1 HM ∗ ghost_map_auth γlogm 1 LM ∗
      ghost_map_auth γdpos 1 DP ∗ ([∗ map] i ↦ p ∈ DP, dpos_at i p) ∗
      ghost_map_auth γfr 1 FR ∗ ([∗ map] k ↦ v ∈ FR, k ↪[γfr]□ v) ∗
      mono_nat_auth_own γloglen 1 (length log) ∗
      mono_nat_auth_own γdlen 1 (length dl) ∗
      view_auth tvs ∗
      ⌜interp_pure img log dl tvs HM LM DP FR⌝)%I.

  (** The interp's pure content and its two length receipts, threaded. *)
  Lemma interp_pure_get img log dl tvs :
    tso_interp img log dl tvs -∗
    ⌜(∀ h, (tvs h ≤ length dl)%nat) ∧ dl_ok log dl ∧ fifo_ok log dl⌝.
  Proof.
    iIntros "(% & % & % & % & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hp)".
    iPureIntro. destruct Hp as (_ & _ & _ & _ & ? & ? & ?). done.
  Qed.

  Lemma interp_dlb img log dl tvs :
    tso_interp img log dl tvs -∗ tso_interp img log dl tvs ∗ dlb (length dl).
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    iDestruct (nlb_get with "Hdlen") as "#Hlb". iFrame "Hlb".
    iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv". by iPureIntro.
  Qed.

  Lemma interp_llb img log dl tvs :
    tso_interp img log dl tvs -∗ tso_interp img log dl tvs ∗ llb (length log).
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    iDestruct (nlb_get with "Hlen") as "#Hlb". iFrame "Hlb".
    iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv". by iPureIntro.
  Qed.

  (** What the evidence says at the machine. *)
  Lemma dpos_ev_vis img log dl tvs t B :
    tso_interp img log dl tvs -∗ dpos_ev t B -∗
    ⌜t = 0%nat ∨ ∃ i q, t = S i ∧ dl !! q = Some i ∧ (S q ≤ B)%nat⌝.
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iIntros "[%|(%i & %p & -> & Hat & %Hp)]".
    - by iLeft.
    - iDestruct (ghost_map_lookup with "Hdp Hat") as %HDP.
      apply Hdpo in HDP as (q & Hq & ->). iPureIntro. right. exists i, q. done.
  Qed.

  Lemma dpos_ev_drained img log dl tvs i B :
    tso_interp img log dl tvs -∗ dpos_ev (S i) B -∗ ⌜i ∈ dl⌝.
  Proof.
    iIntros "Hint Hev".
    iDestruct (dpos_ev_vis with "Hint Hev") as %[?|(i' & q & [= <-] & Hq & _)]; [done|].
    iPureIntro. by eapply elem_of_list_lookup_2.
  Qed.

  (** A drain position's witness, read off the interp. *)
  Lemma interp_dpos_at img log dl tvs i q :
    dl !! q = Some i →
    tso_interp img log dl tvs -∗ tso_interp img log dl tvs ∗ dpos_at i (S q).
  Proof.
    iIntros (Hq) "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    have HDP : DP !! i = Some (S q) by apply Hdpo; eauto.
    iDestruct (big_sepM_lookup _ _ _ _ HDP with "Hdps") as "#Hat".
    iFrame "Hat". iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
    iPureIntro. by split_and!.
  Qed.

  (** The view receipt, minted at the hart's current view. *)
  Lemma twin_view_lb_get img log dl tvs h :
    tso_interp img log dl tvs -∗ tso_interp img log dl tvs ∗ view_lb h (tvs h).
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (view_auth_frag γview tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hdlen") as "#Hlb".
    iSplitL; last first.
    { iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs. }
    iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
    iPureIntro. by split_and!.
  Qed.

  Lemma twin_view_valid img log dl tvs h K :
    tso_interp img log dl tvs -∗ view_lb h K -∗
    tso_interp img log dl tvs ∗ ⌜(K ≤ tvs h)%nat⌝.
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp) #HK".
    iDestruct (view_auth_valid with "Hv HK") as %?.
    iSplitL "Hh Hm Hdp Hfr Hlen Hdlen Hv"; [|by iPureIntro].
    iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv". by iPureIntro.
  Qed.

  (** The machine's view advance (a load's choice of view). *)
  Lemma twin_view_advance img log dl tvs h tv' :
    (tvs h ≤ tv')%nat → (tv' ≤ length dl)%nat →
    tso_interp img log dl tvs ==∗
    tso_interp img log dl (λ h0, if decide (h0 = h) then tv' else tvs h0).
  Proof.
    iIntros (Hle Htop) "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iMod (view_auth_update γview tvs (λ h0, if decide (h0 = h) then tv' else tvs h0)
            with "Hv") as "Hv".
    { intros h0. destruct (decide (h0 = h)); [subst; lia | lia]. }
    iModIntro. iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
    iPureIntro. split_and!; try done.
    intros h0. destruct (decide (h0 = h)); [lia | apply Htvs].
  Qed.

  (** The acquire leaf's gift ([TsoCtxLedger.hart_view_lb_get]): a hart at
      the drain top places any stamp under its own view. *)
  Lemma twin_passed_get img log dl tvs h T :
    (length dl ≤ tvs h)%nat →
    tso_interp img log dl tvs -∗ dlb T -∗
    tso_interp img log dl tvs ∗ view_lb h (tvs h) ∗ ⌜(T ≤ tvs h)%nat⌝.
  Proof.
    iIntros (Htop) "Hint #HT".
    iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (nlb_valid with "Hdlen HT") as %HTlen.
    iDestruct (view_auth_frag γview tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hdlen") as "#Hlb".
    iSplitL.
    { iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
      iPureIntro. by split_and!. }
    iSplitR; last (iPureIntro; lia).
    iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.4 A threading helper for big-ops over a spatial resource    *)
  (* ---------------------------------------------------------------- *)

  (** Rewrite every element of a set big-op through a resource that is
      threaded, not consumed -- the interp, or an authority. *)
  Lemma thread_big_sepS `{Countable A} (P : iProp Σ) (Φ Ψ : A → iProp Σ)
      (D : gset A) :
    (∀ k, k ∈ D → P -∗ Φ k -∗ P ∗ Ψ k) →
    P -∗ ([∗ set] k ∈ D, Φ k) -∗ P ∗ [∗ set] k ∈ D, Ψ k.
  Proof.
    induction D as [|k D Hk IH] using set_ind_L.
    - iIntros (_) "HP _". iFrame "HP". by iApply big_sepS_empty.
    - iIntros (Hstep) "HP Hs". rewrite !big_sepS_insert; [|exact Hk|exact Hk].
      iDestruct "Hs" as "[Hk Hs]".
      iDestruct (Hstep k with "HP Hk") as "[HP Hk']"; first set_solver.
      iDestruct (IH with "HP Hs") as "[HP Hs]".
      { intros k' Hk'. apply Hstep. set_solver. }
      iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.5 Token birth and the interp-free lifecycle laws            *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_stamped_alloc : ⊢ |==> ∃ ξc : CtxId, ctx_stamped ξc 0.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), ∅. iFrame "Hb Hd".
    iSplitR; first by iApply nlb_0. iModIntro. by iApply big_sepS_empty.
  Qed.

  Lemma own_context_boot h : ⊢ |==> ∃ ξ : CtxId, own_context ξ h.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), 0%nat, 0%nat, ∅. iFrame "Hb Hd".
    iSplitR; first by iApply view_lb_0.
    iSplitR; first done. by iApply big_sepS_empty.
  Qed.

  (** FORK'S MINT: a running twin of a running context. *)
  Lemma own_context_twin ξ h :
    own_context ξ h ==∗ own_context ξ h ∗ ∃ ξc : CtxId, own_context ξc h.
  Proof.
    iIntros "(%B & %K & %D & Hat & #HK & %HBK & #Hoks)".
    iMod (mono_nat_own_alloc B) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iSplitL "Hat".
    { iExists B, K, D. iFrame "Hat HK Hoks". by iPureIntro. }
    iExists (MkCtxId γb γd), B, K, ∅. iFrame "Hb Hd HK".
    iSplitR; first done. by iApply big_sepS_empty.
  Qed.

  (** THE ABSORB OF THE BOUND at a view receipt, yielding a floor. *)
  Lemma ctx_bound_raise ξ h K' :
    own_context ξ h -∗ view_lb h K' ==∗ own_context ξ h ∗ ctx_floor ξ K'.
  Proof.
    iIntros "(%B & %K & %D & [Hb Hd] & #HK & %HBK & #Hoks) #HK'".
    iMod (mono_nat_own_update (Nat.max B K') with "Hb") as "[Hb #Hlb]"; first lia.
    iDestruct (view_lb_join h K K' with "HK HK'") as "#HKm".
    iModIntro. iSplitL.
    { iExists (Nat.max B K'), (Nat.max K K'), D. iFrame "Hb Hd HKm".
      iSplitR; first (iPureIntro; lia).
      iApply (big_sepS_impl with "Hoks"). iIntros "!>" (k _).
      iApply dirty_ok_mono. lia. }
    iLeft. iApply (mono_nat_lb_own_le with "Hlb"). lia.
  Qed.

  (** UNSTAMP: re-host a stamped context at a receipt [T ≤ K].  Every key
      is re-founded on the clean arm. *)
  Lemma ctx_unstamp ξ h T K :
    (T ≤ K)%nat →
    view_lb h K -∗ ctx_stamped ξ T ==∗ own_context ξ h.
  Proof.
    iIntros (HTK) "#HK (%D & Hat & #HT & #Hks)".
    iModIntro. iExists T, K, D. iFrame "Hat HK".
    iSplitR; first done.
    iApply big_sepS_intro. iIntros "!>" (k Hk). iLeft.
    iApply (big_sepS_elem_of with "Hks"). exact Hk.
  Qed.

  Lemma ctx_stamped_dlb ξ T : ctx_stamped ξ T -∗ ctx_stamped ξ T ∗ dlb T.
  Proof.
    (* [iSplitL] first: a persistent [iFrame] would descend into the
       transparent [ctx_stamped] and frame its inner [dlb T] instead. *)
    iIntros "(%D & Hat & #HT & #Hks)". iSplitL "Hat"; last iExact "HT".
    iExists D. iFrame "Hat HT". iModIntro. iExact "Hks".
  Qed.

  (** A STAMPED CONTEXT'S STAMP RISES AT A DRAIN-LENGTH RECEIPT (the
      release hook's fold, [WpLock.lock_hook_llb], with [dlb] for [llb]). *)
  Lemma ctx_stamped_raise ξ T T' :
    dlb T' -∗ ctx_stamped ξ T ==∗ ctx_stamped ξ (Nat.max T T') ∗ ctx_floor ξ T'.
  Proof.
    iIntros "#HT' (%D & [Hb Hd] & #HT & #Hks)".
    iMod (mono_nat_own_update (Nat.max T T') with "Hb") as "[Hb #Hlb]"; first lia.
    iModIntro. iSplitL.
    - iExists D. iFrame "Hb Hd".
      iSplitR; first by iApply (nlb_max with "HT HT'").
      iModIntro. iApply (big_sepS_impl with "Hks"). iIntros "!>" (k _).
      iApply dpos_ev_mono. lia.
    - iLeft. iApply (mono_nat_lb_own_le with "Hlb"). lia.
  Qed.

  (** THE FOLD'S EVIDENCE (relaxed-ww.md §2.4): a stamped record's own key
      is drained under its stamp -- what a payload row's floor is stated
      through under two logs, in place of an [llb] at an issue index. *)
  Lemma ctx_stamped_wrote ξ T t a :
    ctx_stamped ξ T -∗ ctx_wrote ξ t a -∗ ctx_stamped ξ T ∗ dpos_ev t T.
  Proof.
    iIntros "(%D & [Hb Hd] & #HT & #Hks) #Hw".
    iDestruct (dset_lookup with "Hd Hw") as %HkD.
    iDestruct (big_sepS_elem_of _ _ (t, a) HkD with "Hks") as "#Hev".
    iFrame "Hev". iExists D. iFrame "Hb Hd HT". iModIntro. iExact "Hks".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.6 The key transports and [CtxMorph]                         *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_floor_dom_at ξ ξ' q lo :
    ctx_dom_at ξ ξ' q -∗ ctx_floor ξ lo -∗ ctx_dom_at ξ ξ' q ∗ ctx_floor ξ' lo.
  Proof.
    iIntros "(%B & %D & [Hb Hd] & #Hfl & #Hks) #Hlo".
    iDestruct (nlb_valid_q with "Hb Hlo") as %HloB.
    iSplitL.
    { iExists B, D. iFrame "Hb Hd Hfl". iModIntro. iExact "Hks". }
    iApply (ctx_floor_le _ _ _ HloB with "Hfl").
  Qed.
  Lemma ctx_floor_dom ξ ξ' lo :
    ctx_dom ξ ξ' -∗ ctx_floor ξ lo -∗ ctx_dom ξ ξ' ∗ ctx_floor ξ' lo.
  Proof. apply ctx_floor_dom_at. Qed.

  (** THE KEY TRANSPORTS ([TsoCtx.ctx_dom_at_key]): the clean arm by the
      evidence's position under [B] and the floor, the dirty arm by
      membership and the registered [key_at]. *)
  Lemma ctx_dom_at_key ξ ξ' q k :
    ctx_dom_at ξ ξ' q -∗ key_at ξ k -∗ ctx_dom_at ξ ξ' q ∗ key_at ξ' k.
  Proof.
    iIntros "(%B & %D & [Hb Hd] & #Hfl & #Hks) #Hk".
    iAssert (key_at ξ' k) as "#Hk'".
    { iDestruct "Hk" as "[(%p & Hev & Hp) | Hdt]".
      - iDestruct (nlb_valid_q with "Hb Hp") as %HpB.
        iLeft. iExists B. iFrame "Hfl". iApply (dpos_ev_mono with "Hev"). lia.
      - iDestruct (dset_lookup with "Hd Hdt") as %HkD.
        iApply (big_sepS_elem_of with "Hks"). exact HkD. }
    iFrame "Hk'". iExists B, D. iFrame "Hb Hd Hfl". iModIntro. iExact "Hks".
  Qed.
  Lemma ctx_dom_key ξ ξ' k :
    ctx_dom ξ ξ' -∗ key_at ξ k -∗ ctx_dom ξ ξ' ∗ key_at ξ' k.
  Proof. apply ctx_dom_at_key. Qed.

  (** §2.8's rule, as a law: a store-derived floor IS [key_at] at the
      store's issue index, and it transports as one. *)
  Lemma ctx_dom_wrote ξ ξ' t a :
    ctx_dom ξ ξ' -∗ ctx_wrote ξ t a -∗ ctx_dom ξ ξ' ∗ key_at ξ' (t, a).
  Proof.
    iIntros "Hd #Hw". iApply (ctx_dom_key with "Hd"). by iRight.
  Qed.

  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.

  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P) | 100.
  Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

  Global Instance ctx_morph_pointsto a dq v :
    CtxMorph (λ ξ, ctx_pointsto ξ a dq v).
  Proof.
    iIntros (ξ ξ') "Hd (%t & Hpt & #Hbit)".
    iDestruct (ctx_dom_key ξ ξ' (t, a) with "Hd Hbit") as "[Hd #Hbit']".
    iModIntro. iFrame "Hd". iExists t. by iFrame "Hpt Hbit'".
  Qed.

  Global Instance ctx_morph_floor lo : CtxMorph (λ ξ, ctx_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd #Hfl".
    iDestruct (ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    iModIntro. iFrame "Hd Hfl'".
  Qed.

  Global Instance ctx_morph_key k : CtxMorph (λ ξ, key_at ξ k).
  Proof.
    iIntros (ξ ξ') "Hd #Hk".
    iDestruct (ctx_dom_key ξ ξ' k with "Hd Hk") as "[Hd #Hk']".
    iModIntro. iFrame "Hd Hk'".
  Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR1 HR2]".
    iMod (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iMod (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ ξ') "Hd [%x HR]".
    iMod (ctx_morph with "Hd HR") as "[Hd HR]".
    iModIntro. iFrame "Hd". iExists x. iExact "HR".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.7 Mint 1: a context dominated by a context on the same hart *)
  (* ---------------------------------------------------------------- *)

  Local Lemma dset_insert_set (γ : gname) (S D : gset (nat * Z)) :
    dset_auth γ 1 S ==∗ dset_auth γ 1 (S ∪ D) ∗ [∗ set] k ∈ D, dset_in γ k.
  Proof.
    induction D as [|k D Hk IH] using set_ind_L.
    - iIntros "H". rewrite union_empty_r_L big_sepS_empty. by iFrame.
    - iIntros "H". iMod (IH with "H") as "[H #Hs]".
      iMod (dset_insert _ _ k with "H") as "[H #Hk]".
      iModIntro. rewrite big_sepS_insert; [|exact Hk]. iFrame "Hk Hs".
      replace (S ∪ ({[k]} ∪ D)) with (S ∪ D ∪ {[k]}) by set_solver. iFrame.
  Qed.

  (** Every key justified at ξ' is drained under ξ''s bound or in ξ''s
      dirty set -- read off ξ''s authority (at any fraction), threaded. *)
  Local Lemma keys_just (ξ' : CtxId) (q : Qp) (B' : nat) (D' D : gset (nat * Z)) :
    ctx_at ξ' q B' D' -∗ ([∗ set] k ∈ D, key_at ξ' k) -∗
    ctx_at ξ' q B' D' ∗ [∗ set] k ∈ D, (dpos_ev k.1 B' ∨ ⌜k ∈ D'⌝).
  Proof.
    apply thread_big_sepS.
    iIntros (k _) "[Hb Hd] #Hk".
    iDestruct "Hk" as "[(%p & Hev & Hp) | Hdt]".
    - iDestruct (nlb_valid_q with "Hb Hp") as %HpB'.
      iFrame "Hb Hd". iLeft. iApply (dpos_ev_mono with "Hev"). lia.
    - iDestruct (dset_lookup with "Hd Hdt") as %HkD'.
      iFrame "Hb Hd". by iRight.
  Qed.

  (** THE CORE OF MINT 1: ξ' takes on the keys of a context running beside
      it on THIS hart.  Unchanged from the landed law: ξ's dirty keys are
      this hart's own messages or drained under ξ's bound, both of which
      justify them at ξ' once its bound has risen to the join. *)
  Local Lemma ctx_dom_run_core (ξ' : CtxId) (h : agent) (B K : nat) (D : gset (nat * Z)) :
    (B ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ([∗ set] k ∈ D, dirty_ok h B k) ==∗
    own_context ξ' h ∗ ctx_floor ξ' B ∗ [∗ set] k ∈ D, key_at ξ' k.
  Proof.
    iIntros (HBK) "(%B' & %K' & %D' & [Hb' Hd'] & #HK' & %HBK' & #Hoks') #HK #Hoks".
    iDestruct (view_lb_join h K' K with "HK' HK") as "#HKK".
    iMod (mono_nat_own_update (Nat.max B' B) with "Hb'") as "[Hb' #Hlb']"; first lia.
    iMod (dset_insert_set (tc_dirty ξ') D' D with "Hd'") as "[Hd' #Hins]".
    iAssert ([∗ set] k ∈ D' ∪ D, dirty_ok h (Nat.max B' B) k)%I as "#Hoks''".
    { iApply big_sepS_intro. iIntros "!>" (k Hk).
      apply elem_of_union in Hk as [Hk|Hk].
      - iApply (dirty_ok_mono _ B' with "[]"); [lia|].
        iApply (big_sepS_elem_of with "Hoks'"). exact Hk.
      - iApply (dirty_ok_mono _ B with "[]"); [lia|].
        iApply (big_sepS_elem_of with "Hoks"). exact Hk. }
    iModIntro.
    iSplitL "Hb' Hd'".
    { iExists (Nat.max B' B), (Nat.max K' K), (D' ∪ D). iFrame "Hb' Hd' HKK Hoks''".
      iPureIntro. lia. }
    iSplitR.
    { iApply (nlb_le _ (Nat.max B' B)); [lia|]. iLeft. iExact "Hlb'". }
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iRight. iApply (big_sepS_elem_of with "Hins"). exact Hk.
  Qed.

  (** PARK -- mint 1 at full authority.  No fence, no receipt, no stamp. *)
  Lemma ctx_park ξ ξ' h :
    own_context ξ' h -∗ own_context ξ h ==∗ own_context ξ' h ∗ ctx_parked ξ ξ'.
  Proof.
    iIntros "Hrun' (%B & %K & %D & Hat & #HK & %HBK & #Hoks)".
    iMod (ctx_dom_run_core ξ' h B K D HBK with "Hrun' HK Hoks") as "(Hrun' & #Hfl & #Hks)".
    iModIntro. iFrame "Hrun'". iExists B, D. iFrame "Hat Hfl". iModIntro. iExact "Hks".
  Qed.

  (** RESUME: the dominator runs here, so the dominated may.  A child key
      is drained under the parent's bound (clean at the parent) or
      registered at the parent, so the parent's own justification on this
      hart applies. *)
  Lemma ctx_resume ξ ξ' h :
    own_context ξ' h -∗ ctx_parked ξ ξ' ==∗ own_context ξ' h ∗ own_context ξ h.
  Proof.
    iIntros "(%B' & %K' & %D' & [Hb' Hd'] & #HK' & %HBK' & #Hoks') (%B & %D & [Hb Hd] & #Hfl & #Hks)".
    iDestruct (nlb_valid with "Hb' Hfl") as %HBB'.
    iDestruct (keys_just ξ' 1 B' D' D with "[$Hb' $Hd'] Hks") as "[[Hb' Hd'] #Hjs]".
    iMod (mono_nat_own_update B' with "Hb") as "[Hb _]"; first exact HBB'.
    iModIntro.
    iSplitL "Hb' Hd'".
    { iExists B', K', D'. iFrame "Hb' Hd' HK' Hoks'". by iPureIntro. }
    iExists B', K', D. iFrame "Hb Hd HK'".
    iSplitR; first done.
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iDestruct (big_sepS_elem_of _ _ k Hk with "Hjs") as "[Hev | %HkD']".
    - by iLeft.
    - iApply (big_sepS_elem_of with "Hoks'"). exact HkD'.
  Qed.

  (** MINT 1 AT A HALF -- the same-hart borrow. *)
  Lemma ctx_dom_run ξ ξ' h :
    own_context ξ h -∗ own_context ξ' h ==∗
    own_context ξ' h ∗ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ own_context ξ h).
  Proof.
    iIntros "(%B & %K & %D & Hat & #HK & %HBK & #Hoks) Hrun'".
    iMod (ctx_dom_run_core ξ' h B K D HBK with "Hrun' HK Hoks") as "(Hrun' & #Hfl & #Hks)".
    iModIntro. iFrame "Hrun'".
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitL "Hat1".
    { iExists B, D. iFrame "Hat1 Hfl". iModIntro. iExact "Hks". }
    iIntros "(%B0 & %D0 & Hat0 & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists B, K, D. iFrame "Hat HK Hoks". by iPureIntro.
  Qed.

  (** THE SAME-HART HAND-OFF: mint, morph, give back. *)
  Lemma ctx_move {R : CtxId → iProp Σ} `{!CtxMorph R} ξ0 ξ1 h :
    own_context ξ0 h -∗ own_context ξ1 h -∗ R ξ0 ==∗
    own_context ξ0 h ∗ own_context ξ1 h ∗ R ξ1.
  Proof.
    iIntros "H0 H1 HR".
    iMod (ctx_dom_run ξ0 ξ1 with "H0 H1") as "(H1 & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "H1 HR". by iApply "Hback".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.8 Mint 4 and the algebra of the parked-under record         *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_parked_borrow ξ ξ' :
    ctx_parked ξ ξ' ⊢ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ ξ').
  Proof.
    iIntros "(%B & %D & Hat & #Hfl & #Hks)".
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitL "Hat1".
    { iExists B, D. iFrame "Hat1 Hfl". iModIntro. iExact "Hks". }
    iIntros "(%B0 & %D0 & Hat0 & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists B, D. iFrame "Hat Hfl". iModIntro. iExact "Hks".
  Qed.

  (** The relation composes through a dominated middle. *)
  Lemma ctx_dom_at_dom ξ ξ' ξ'' q :
    ctx_dom ξ' ξ'' -∗ ctx_dom_at ξ ξ' q -∗ ctx_dom ξ' ξ'' ∗ ctx_dom_at ξ ξ'' q.
  Proof.
    iIntros "(%B' & %D' & [Hb' Hd'] & #Hfl' & #Hks') (%B & %D & Hat & #Hfl & #Hks)".
    iDestruct (nlb_valid_q with "Hb' Hfl") as %HBB'.
    iDestruct (keys_just ξ' (1/2) B' D' D with "[$Hb' $Hd'] Hks") as "[[Hb' Hd'] #Hjs]".
    iAssert (ctx_floor ξ'' B) as "#Hfl''".
    { iApply (ctx_floor_le _ _ _ HBB' with "Hfl'"). }
    iAssert ([∗ set] k ∈ D, key_at ξ'' k)%I as "#Hks''".
    { iApply big_sepS_intro. iIntros "!>" (k Hk).
      iDestruct (big_sepS_elem_of _ _ k Hk with "Hjs") as "[Hev | %HkD']".
      - iLeft. iExists B'. iFrame "Hev Hfl'".
      - iApply (big_sepS_elem_of with "Hks'"). exact HkD'. }
    iSplitL "Hb' Hd'".
    { iExists B', D'. iFrame "Hb' Hd' Hfl'". iModIntro. iExact "Hks'". }
    iExists B, D. iFrame "Hat Hfl''". iModIntro. iExact "Hks''".
  Qed.

  Global Instance ctx_parked_morph ξ : CtxMorph (λ ξ', ctx_parked ξ ξ').
  Proof.
    iIntros (ξ' ξ'') "Hd HP".
    iDestruct (ctx_dom_at_dom ξ ξ' ξ'' 1 with "Hd HP") as "[Hd HP]".
    iModIntro. iFrame "Hd HP".
  Qed.

  Lemma ctx_parked_flatten ξ P S :
    ctx_parked ξ P -∗ ctx_parked P S -∗ ctx_parked ξ S ∗ ctx_parked P S.
  Proof.
    iIntros "Hξ HP".
    iDestruct (ctx_parked_borrow with "HP") as "[Hd Hback]".
    iDestruct (ctx_dom_at_dom ξ P S 1 with "Hd Hξ") as "[Hd Hξ]".
    iSplitL "Hξ"; [iExact "Hξ" | by iApply "Hback"].
  Qed.

  (** THE BRIDGE FROM THE ROOT, pure: a stamped record beside a floor of ξ'
      over its stamp IS a record parked under ξ'. *)
  Lemma ctx_parked_of_stamped ξ ξ' T :
    ctx_stamped ξ T -∗ ctx_floor ξ' T -∗ ctx_parked ξ ξ'.
  Proof.
    iIntros "(%D & Hat & #HT & #Hks) #Hfl".
    iExists T, D. iFrame "Hat Hfl".
    iModIntro. iApply big_sepS_intro. iIntros "!>" (k Hk).
    iLeft. iExists T. iFrame "Hfl". iApply (big_sepS_elem_of with "Hks"). exact Hk.
  Qed.

  (** A RECORD PARKED UNDER A STAMPED ROOT IS ITSELF STAMPED at the root's
      stamp: a child key is drained under the root's bound, or registered
      at the root and so drained under [T] by the root's own row. *)
  Lemma ctx_stamped_of_parked ξ ξ' T :
    ctx_stamped ξ' T -∗ ctx_parked ξ ξ' ==∗ ctx_stamped ξ' T ∗ ctx_stamped ξ T.
  Proof.
    iIntros "(%D' & Hat' & #HT & #Hks') (%B & %D & [Hb Hd] & #Hfl & #Hks)".
    iDestruct (keys_just ξ' 1 T D' D with "Hat' Hks") as "[[Hb' Hd'] #Hjs]".
    iDestruct (nlb_valid with "Hb' Hfl") as %HBT.
    iMod (mono_nat_own_update T with "Hb") as "[Hb _]"; first exact HBT.
    iModIntro. iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd' HT". iModIntro. iExact "Hks'". }
    iExists D. iFrame "Hb Hd HT". iModIntro.
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iDestruct (big_sepS_elem_of _ _ k Hk with "Hjs") as "[Hev | %HkD']".
    - iExact "Hev".
    - iApply (big_sepS_elem_of with "Hks'"). exact HkD'.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.9 Mint 3: out of a stamped root, at a view receipt          *)
  (* ---------------------------------------------------------------- *)

  (** [TsoCtxAbsorbLb.ctx_dom_of_stamped_lb], unchanged: the claimer's
      bound rises to the receipt; every key of the root is drained under
      [T ≤ K], clean at the claimer. *)
  Lemma ctx_dom_of_stamped_lb ξ ξ' h T K :
    (T ≤ K)%nat →
    view_lb h K -∗ own_context ξ' h -∗ ctx_stamped ξ T ==∗
    own_context ξ' h ∗ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_stamped ξ T).
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iMod (ctx_bound_raise ξ' h K with "Hrun HK") as "[Hrun #HflK]".
    iDestruct "Hpk" as "(%D & Hat & #HT & #Hks)".
    iAssert (ctx_floor ξ' T) as "#HflT".
    { iApply (ctx_floor_le _ _ _ HTK with "HflK"). }
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro. iFrame "Hrun".
    iSplitL "Hat1".
    { iExists T, D. iFrame "Hat1 HflT". iModIntro.
      iApply big_sepS_intro. iIntros "!>" (k Hk).
      iLeft. iExists T. iFrame "HflT". iApply (big_sepS_elem_of with "Hks"). exact Hk. }
    iIntros "(%B0 & %D0 & Hat0 & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". iModIntro. iExact "Hks".
  Qed.

  Lemma ctx_absorb_lb (R : CtxId → iProp Σ) `{!CtxMorph R} ξ ξ' h T K :
    (T ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ctx_stamped ξ T -∗ R ξ ==∗
    own_context ξ' h ∗ ctx_stamped ξ T ∗ R ξ'.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk HR".
    iMod (ctx_dom_of_stamped_lb ξ ξ' h T K HTK with "HK Hrun Hpk") as "(Hrun & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hrun HR". by iApply "Hback".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.10 Gate lemmas: LOAD, STORE, DRAIN                          *)
  (* ---------------------------------------------------------------- *)

  (** The bit's visibility at the machine, from either arm of the running
      token's justification. *)
  Local Lemma key_visible img log dl tvs ξ h t a :
    tso_interp img log dl tvs -∗ own_context ξ h -∗ key_at ξ (t, a) -∗
    tso_interp img log dl tvs ∗ own_context ξ h ∗
    ⌜t = 0%nat ∨ (∃ i q, t = S i ∧ dl !! q = Some i ∧ (S q ≤ tvs h)%nat) ∨
     (∃ i m, t = S i ∧ log !! i = Some m ∧ wm_tid m = h)⌝.
  Proof.
    iIntros "Hint Hrun #Hbit".
    iDestruct "Hrun" as "(%B & %K & %D & [Hb Hd] & #HK & %HBK & #Hoks)".
    iDestruct (twin_view_valid with "Hint HK") as "[Hint %HKtvs]".
    iAssert (⌜t = 0%nat ∨ (∃ i q, t = S i ∧ dl !! q = Some i ∧ (S q ≤ B)%nat) ∨
              (∃ i m, t = S i ∧ log !! i = Some m ∧ wm_tid m = h)⌝)%I as %Hvis.
    { iDestruct "Hbit" as "[(%p & Hev & Hlb)|Hdt]".
      - iDestruct (nlb_valid with "Hb Hlb") as %HpB.
        iDestruct (dpos_ev_vis with "Hint Hev") as %[Ht0|(i & q & Hti & Hq & Hle)].
        + simpl in Ht0. subst t. iPureIntro. by left.
        + simpl in Hti. subst t. iPureIntro. right; left. exists i, q. split_and!; [done|done|lia].
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepS_elem_of _ _ (t, a) HDt with "Hoks") as "[Hev|(%i & %Hti & (%m & Ha & %Htid))]".
        + iDestruct (dpos_ev_vis with "Hint Hev") as %[Ht0|(i & q & Hti' & Hq & Hle)].
          * simpl in Ht0. subst t. iPureIntro. by left.
          * simpl in Hti'. subst t. iPureIntro. right; left. exists i, q. done.
        + iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & _ & _ & _ & _ & _ & _ & _ & %Hp)".
          iDestruct (ghost_map_lookup with "Hm Ha") as %HLMi.
          destruct Hp as (_ & HLM & _). rewrite HLM in HLMi.
          iPureIntro. right; right. simpl in Hti. exists i, m. done. }
    iFrame "Hint". iSplitL.
    { iExists B, K, D. iFrame "Hb Hd HK Hoks". by iPureIntro. }
    iPureIntro. destruct Hvis as [->|[(i & q & -> & Hq & Hle)|?]].
    - by left.
    - right; left. exists i, q. split_and!; [done|done|lia].
    - by right; right.
  Qed.

  Lemma twin_load_ok img log dl tvs ξ h a dq v :
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_pointsto ξ a dq v -∗
    ⌜∀ tv', (tvs h ≤ tv')%nat → tso_read (img_fun img) log dl h tv' a = Some v⌝.
  Proof.
    iIntros "Hint Hrun (%t & Hpt & #Hbit)".
    iDestruct (key_visible with "Hint Hrun Hbit") as "(Hint & _ & %Hvis)".
    iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    destruct (Htie _ _ _ HHa) as [Hlat Hc].
    iPureIntro. move => tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ _ t v Hok Hf Hlat Hc).
    destruct Hvis as [->|[(i & q & -> & Hq & Hle)|(i & m & -> & Hi & Htid)]].
    - by left.
    - right. have Hlt := dl_lookup_lt _ _ _ _ Hok Hq.
      destruct (lookup_lt_is_Some_2 log i Hlt) as [m Hm].
      exists i, m. split_and!; [done|done|]. left. exists q. split; [done|lia].
    - right. exists i, m. split_and!; [done|done|by right].
  Qed.

  (** The store gate's pure half: the previous latest write is drained or
      [h]'s own. *)
  Lemma twin_store_gate img log dl tvs ξ h a dq v :
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_pointsto ξ a dq v -∗
    tso_interp img log dl tvs ∗ own_context ξ h ∗
    ∃ t, a ↪[γheap]{dq} (t, v) ∗ ⌜drained_or_by log dl h t⌝.
  Proof.
    iIntros "Hint Hrun (%t & Hpt & #Hbit)".
    iDestruct (key_visible with "Hint Hrun Hbit") as "(Hint & Hrun & %Hvis)".
    iFrame "Hint Hrun". iExists t. iFrame "Hpt". iPureIntro.
    destruct Hvis as [->|[(i & q & -> & Hq & _)|(i & m & -> & Hi & Htid)]].
    - by move => j mj.
    - move => j mj [= <-] _. left. by eapply elem_of_list_lookup_2.
    - move => j mj [= <-] Hj. right. congruence.
  Qed.

  (** STORE: the message is born pending; the fact turns dirty at its
      context with the author arm as its justification, and the context
      records its key ([ctx_wrote]). *)
  Lemma twin_store_ok img log dl tvs ξ h a v w :
    tso_interp img log dl tvs -∗ own_context ξ h -∗
    ctx_pointsto ξ a (DfracOwn 1) v ==∗
    tso_interp img (store_log log h a [w]) dl tvs ∗ own_context ξ h ∗
    ctx_pointsto ξ a (DfracOwn 1) w ∗ ctx_wrote ξ (S (length log)) a.
  Proof.
    iIntros "Hint Hrun Hpt".
    iDestruct (twin_store_gate with "Hint Hrun Hpt") as "(Hint & Hrun & %t & Hpt & %Hgate)".
    iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct "Hrun" as "(%B & %K & %D & [Hb Hd] & #HK & %HBK & #Hoks)".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    destruct (Htie _ _ _ HHa) as [Hlat Hc].
    set (m := WMsg a [w] h). set (t' := S (length log)).
    iMod (ghost_map_update (t', w) with "Hh Hpt") as "[Hh Hpt]".
    have HLMfresh : LM !! length log = None.
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length log) m HLMfresh with "Hm") as "[Hm #Hlogm]".
    iMod (mono_nat_own_update (length (store_log log h a [w])) with "Hlen") as "[Hlen _]".
    { rewrite /store_log length_app /=. lia. }
    iMod (dset_insert _ D (t', a) with "Hd") as "[Hd #Hdt']".
    iModIntro.
    iSplitR "Hb Hd Hpt"; last first.
    { iSplitR "Hpt"; last first.
      { iSplitL; last iExact "Hdt'". iExists t'. iFrame "Hpt". iRight. iExact "Hdt'". }
      iExists B, K, (D ∪ {[(t', a)]}). iFrame "Hb Hd HK".
      iSplitR; first done.
      destruct (decide ((t', a) ∈ D)) as [Hin|Hnin].
      { replace (D ∪ {[(t', a)]}) with D by set_solver. iExact "Hoks". }
      rewrite (union_comm_L D) big_sepS_insert; last exact Hnin.
      iFrame "Hoks". iRight. iExists (length log). iSplit; first done.
      iExists m. iFrame "Hlogm". done. }
    iExists (<[a := (t', w)]> HM), (<[length log := m]> LM), DP, FR.
    iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
    iPureIntro.
    have Hdlok' : dl_ok (store_log log h a [w]) dl by apply dl_ok_app_log.
    split_and!.
    - intros a0 t0 v0. destruct (decide (a0 = a)) as [->|Hne].
      + rewrite lookup_insert. intros [= <- <-]. split.
        * apply latest_app_new.
        * exact (chain_ok_new (img_fun img) log dl a t v h w Hok Hf Hlat Hc Hgate).
      + rewrite lookup_insert_ne; last congruence. intros HH0.
        destruct (Htie _ _ _ HH0) as [Hl0 Hc0]. split.
        * apply latest_app_frame; [by apply msg_byte_singleton_ne|done].
        * apply chain_ok_app_log; [|done]. destruct Hl0 as [Hb0 _]. by eapply log_byte_some_le.
    - intros i. rewrite /store_log. destruct (decide (i = length log)) as [->|Hne].
      + rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      + rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (i < length log)%nat) as [Hlt|Hge].
        * by rewrite lookup_app_l.
        * rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia.
    - done.
    - done.
    - done.
    - done.
    - by apply fifo_ok_app_log.
  Qed.

  (** DRAIN, the environment step: nothing any client holds moves. *)
  Lemma twin_drain img log dl tvs k :
    drain_ok log dl k →
    tso_interp img log dl tvs ==∗ tso_interp img log (dl ++ [k]) tvs.
  Proof.
    iIntros (Hdr) "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    destruct (dpos_ok_drain _ _ _ _ Hok Hdr Hdpo) as [HDPk Hdpo'].
    iMod (ghost_map_insert_persist k (S (length dl)) HDPk with "Hdp") as "[Hdp #Hk]".
    iMod (mono_nat_own_update (length (dl ++ [k])) with "Hdlen") as "[Hdlen _]".
    { rewrite length_app /=. lia. }
    iModIntro. iExists HM, LM, (<[k := S (length dl)]> DP), FR.
    iFrame "Hh Hm Hdp Hfr Hfrs Hlen Hdlen Hv".
    iSplitR.
    { rewrite big_sepM_insert //. iFrame "Hk Hdps". }
    iPureIntro. split_and!.
    - intros a t v Ha. destruct (Htie _ _ _ Ha) as [Hl Hc]. split; [done|].
      by eapply (chain_ok_drain (img_fun img)).
    - done.
    - done.
    - by apply fr_ok_drain.
    - intros h. rewrite length_app /=. have := Htvs h. lia.
    - by apply drain_dl_ok.
    - by apply fifo_ok_drain.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.11 PUBLICATION AT A FENCE: [ctx_stamp] and mint 2            *)
  (* ---------------------------------------------------------------- *)

  (** At a fence with a W predecessor the machine has waited for every own
      store to drain ([own_drained]).  Then every key this hart justifies
      as its own message has a drain witness in the interp, under the drain
      top. *)
  Local Lemma twin_publish_key img log dl tvs h B k :
    own_drained h log dl → (B ≤ length dl)%nat →
    tso_interp img log dl tvs -∗ dirty_ok h B k -∗
    tso_interp img log dl tvs ∗ dpos_ev k.1 (length dl).
  Proof.
    iIntros (Hod HB) "Hint [Hev|(%i & %Hki & (%m & #Ha & %Htid))]".
    { iFrame "Hint". iApply (dpos_ev_mono with "Hev"). lia. }
    iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (ghost_map_lookup with "Hm Ha") as %HLMi. rewrite HLM in HLMi.
    have Hin := own_drained_lookup _ _ _ _ _ Hod HLMi Htid.
    apply elem_of_list_lookup_1 in Hin as [q Hq].
    have HDP : DP !! i = Some (S q) by apply Hdpo; eauto.
    iDestruct (big_sepM_lookup _ _ _ _ HDP with "Hdps") as "#Hat".
    iSplitL.
    { iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
      iPureIntro. by split_and!. }
    iRight. iExists i, (S q). iFrame "Hat". iPureIntro. split; [done|].
    by eapply lookup_lt_Some.
  Qed.

  Local Lemma twin_publish (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (tvs : agent → nat) (h B : nat) (D : gset (nat * Z)) :
    own_drained h log dl → (B ≤ length dl)%nat →
    tso_interp img log dl tvs -∗ ([∗ set] k ∈ D, dirty_ok h B k) -∗
    tso_interp img log dl tvs ∗ [∗ set] k ∈ D, dpos_ev k.1 (length dl).
  Proof.
    iIntros (Hod HB). apply thread_big_sepS. iIntros (k _).
    by iApply twin_publish_key.
  Qed.

  (** STAMP IS PUBLICATION AT THE FENCE: running → stamped at the drain
      top, with every key drained under it.  This is where the lock's
      release stamps its context ([release]'s [fence rw,w]). *)
  Lemma ctx_stamp img log dl tvs ξ h :
    own_drained h log dl →
    tso_interp img log dl tvs -∗ own_context ξ h ==∗
    tso_interp img log dl tvs ∗ ctx_stamped ξ (length dl).
  Proof.
    iIntros (Hod) "Hint (%B & %K & %D & [Hb Hd] & #HK & %HBK & #Hoks)".
    iDestruct (twin_view_valid with "Hint HK") as "[Hint %HKtvs]".
    iDestruct (interp_pure_get with "Hint") as %(Htop & _ & _).
    have Htoph := Htop h.
    iDestruct (twin_publish _ _ _ _ h B D with "Hint Hoks") as "[Hint #Hpub]";
      [done|lia|].
    iDestruct (interp_dlb with "Hint") as "[Hint #Hdlb]".
    iMod (mono_nat_own_update (length dl) with "Hb") as "[Hb _]"; first lia.
    iModIntro. iFrame "Hint". iExists D. iFrame "Hb Hd Hdlb". iModIntro. iExact "Hpub".
  Qed.

  (** MINT 2 -- A DEPOSIT INTO A STAMPED ROOT, at the fence: the root's
      stamp rises to the drain top, which covers the depositor's keys
      because they are drained there. *)
  Lemma ctx_dom_to_stamped img log dl tvs ξ ξ' h T :
    own_drained h log dl →
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_stamped ξ' T ==∗
    tso_interp img log dl tvs ∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_stamped ξ' T' ∗ ctx_dom ξ ξ' ∗
          (ctx_dom ξ ξ' -∗ own_context ξ h).
  Proof.
    iIntros (Hod) "Hint (%B & %K & %D & Hat & #HK & %HBK & #Hoks) (%D' & [Hb' Hd'] & #HT & #Hks')".
    iDestruct (twin_view_valid with "Hint HK") as "[Hint %HKtvs]".
    iDestruct (interp_pure_get with "Hint") as %(Htop & _ & _).
    have Htoph := Htop h.
    iDestruct (twin_publish _ _ _ _ h B D with "Hint Hoks") as "[Hint #Hpub]";
      [done|lia|].
    iDestruct (interp_dlb with "Hint") as "[Hint #Hdlb]".
    set (T' := Nat.max T (length dl)).
    iMod (mono_nat_own_update T' with "Hb'") as "[Hb' #Hlb']"; first lia.
    iModIntro. iFrame "Hint". iExists T'.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitR; first (iPureIntro; lia).
    iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd'".
      iSplitR; first by iApply (nlb_max with "HT Hdlb").
      iModIntro. iApply (big_sepS_impl with "Hks'"). iIntros "!>" (k _).
      iApply dpos_ev_mono. lia. }
    iSplitL "Hat1".
    { iExists B, D. iFrame "Hat1".
      iSplitR.
      { iLeft. iApply (mono_nat_lb_own_le with "Hlb'"). lia. }
      iModIntro. iApply big_sepS_intro. iIntros "!>" (k Hk).
      iLeft. iExists T'. iSplitL.
      - iApply dpos_ev_mono; last (iApply (big_sepS_elem_of with "Hpub"); exact Hk). lia.
      - iLeft. iExact "Hlb'". }
    iIntros "(%B0 & %D0 & Hat0 & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists B, K, D. iFrame "Hat HK Hoks". by iPureIntro.
  Qed.

  Lemma ctx_deposit (R : CtxId → iProp Σ) `{!CtxMorph R} img log dl tvs ξ ξc h T :
    own_drained h log dl →
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_stamped ξc T -∗ R ξ ==∗
    tso_interp img log dl tvs ∗ own_context ξ h ∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_stamped ξc T' ∗ R ξc.
  Proof.
    iIntros (Hod) "Hint Hrun Hpk HR".
    iMod (ctx_dom_to_stamped with "Hint Hrun Hpk") as "(Hint & %T' & %HTT' & Hpk & Hdom & Hback)";
      first done.
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hint". iSplitL "Hback Hdom"; first by iApply "Hback".
    iExists T'. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.12 The fence record                                         *)
  (* ---------------------------------------------------------------- *)

  (** Mintable at ANY leaf: a message with index [≥ length log] does not
      exist, so it drains later, above [length dl]. *)
  Lemma fence_rec_mint img log dl tvs :
    tso_interp img log dl tvs ==∗
    tso_interp img log dl tvs ∗ fence_rec (length log) (length dl).
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    destruct (FR !! (length log, length dl)) as [v|] eqn:HFR.
    - iDestruct (big_sepM_lookup _ _ _ _ HFR with "Hfrs") as "#Hr".
      iModIntro. iSplitL; last by iExists v.
      iExists HM, LM, DP, FR. iFrame "Hh Hm Hdp Hdps Hfr Hfrs Hlen Hdlen Hv".
      iPureIntro. by split_and!.
    - iMod (ghost_map_insert_persist (length log, length dl) 0%nat HFR with "Hfr")
        as "[Hfr #Hr]".
      iModIntro. iSplitL; last by iExists 0%nat.
      iExists HM, LM, DP, (<[(length log, length dl) := 0%nat]> FR).
      iFrame "Hh Hm Hdp Hdps Hfr Hlen Hdlen Hv".
      iSplitR. { rewrite big_sepM_insert //. iFrame "Hr Hfrs". }
      iPureIntro. split_and!; try done. by apply fr_ok_mint.
  Qed.

  (** What the record says at the machine: a drained message with index
      [≥ N] sits above [M], and [M] is a legal drain position. *)
  Lemma fence_rec_pos img log dl tvs N M :
    tso_interp img log dl tvs -∗ fence_rec N M -∗
    ⌜(M ≤ length dl)%nat ∧ ∀ i q, dl !! q = Some i → (N ≤ i)%nat → (M < S q)%nat⌝.
  Proof.
    iIntros "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp) (%v & #Hr)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (ghost_map_lookup with "Hfr Hr") as %HFR.
    iPureIntro. exact (Hfro _ _ _ HFR).
  Qed.

  (** ... and against a drain witness. *)
  Lemma fence_rec_dpos img log dl tvs N M i p :
    (N ≤ i)%nat →
    tso_interp img log dl tvs -∗ fence_rec N M -∗ dpos_at i p -∗ ⌜(M < p)%nat⌝.
  Proof.
    iIntros (HNi) "Hint #Hr #Hat".
    iDestruct (fence_rec_pos with "Hint Hr") as %[_ Hall].
    iDestruct "Hint" as "(%HM & %LM & %DP & %FR & Hh & Hm & Hdp & #Hdps & Hfr & #Hfrs & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hfro & Htvs & Hok & Hf).
    iDestruct (ghost_map_lookup with "Hdp Hat") as %HDP.
    apply Hdpo in HDP as (q & Hq & ->). iPureIntro. by eapply Hall.
  Qed.

  (** THE READER'S CASH-IN (the [started]/[first] flags, relaxed-ww.md
      §2.7): a hart that is NOT the author sees a message with index [≥ N]
      only at a view past [M] -- the shape [StartedInv] needs to turn a
      flag read into a receipt past the publisher's stamp. *)
  Lemma fence_rec_read img log dl tvs N M h' i m q :
    log !! i = Some m → wm_tid m ≠ h' → (N ≤ i)%nat → dl !! q = Some i →
    visibleb h' (tvs h') log dl (S q) = true →
    tso_interp img log dl tvs -∗ fence_rec N M -∗ ⌜(M < tvs h')%nat⌝.
  Proof.
    iIntros (Hi Htid HNi Hq Hvis) "Hint #Hr".
    iDestruct (fence_rec_pos with "Hint Hr") as %[_ Hall].
    iPureIntro. have HMq := Hall _ _ Hq HNi.
    apply visibleb_true in Hvis as [Hle|(q' & i' & m' & [= <-] & Hq' & Hi' & Htid')]; [lia|].
    rewrite Hq in Hq'. injection Hq' as <-. rewrite Hi in Hi'. injection Hi' as <-. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.13 The dq law surface                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_pointsto_agree ξ1 ξ2 a dq1 v1 dq2 v2 :
    ctx_pointsto ξ1 a dq1 v1 -∗ ctx_pointsto ξ2 a dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "(%t1 & H1 & _) (%t2 & H2 & _)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= _ ->]. done.
  Qed.

  Lemma ctx_pointsto_frac_split ξ a q1 q2 v :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) v ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) v ∗ ctx_pointsto ξ a (DfracOwn q2) v.
  Proof.
    iSplit.
    - iIntros "(%t & [Hpt1 Hpt2] & #Hbit)".
      iSplitL "Hpt1"; iExists t; by iFrame "Hbit".
    - iIntros "[(%t1 & Hpt1 & #Hbit1) (%t2 & Hpt2 & _)]".
      iDestruct (ghost_map_elem_combine with "Hpt1 Hpt2") as "[Hpt %Heq]".
      injection Heq as <-. rewrite dfrac_op_own.
      iExists t1. by iFrame "Hpt Hbit1".
  Qed.

  Lemma ctx_pointsto_persist ξ a dq v :
    ctx_pointsto ξ a dq v ==∗ ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "(%t & Hpt & #Hbit)".
    iMod (ghost_map_elem_persist with "Hpt") as "Hpt".
    iModIntro. iExists t. by iFrame "Hpt Hbit".
  Qed.

  Lemma ctx_pointsto_intro_zero ξ a dq v :
    a ↪[γheap]{dq} ((0%nat, v) : nat * bv 8) -∗ ctx_pointsto ξ a dq v.
  Proof.
    iIntros "Hpt". iExists 0%nat. iFrame "Hpt". iLeft. iExists 0%nat.
    iSplitR; [by iApply dpos_ev_0 | by iApply ctx_floor_0].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.14 The acid tests                                           *)
  (* ---------------------------------------------------------------- *)

  (** FORK: the parent hands a child a byte fact -- clean OR dirty
      (pending!), any fraction -- with nothing to prove, and parks it. *)
  Lemma twin_fork_deposit ξ h a dq v :
    own_context ξ h -∗ ctx_pointsto ξ a dq v ==∗
    own_context ξ h ∗ ∃ ξc, ctx_parked ξc ξ ∗ ctx_pointsto ξc a dq v.
  Proof.
    iIntros "Hrun Hpt".
    iMod (own_context_twin with "Hrun") as "[Hrun (%ξc & Hrunc)]".
    iMod (ctx_move (R := λ ξ0, ctx_pointsto ξ0 a dq v) ξ ξc h with "Hrun Hrunc Hpt")
      as "(Hrun & Hrunc & Hpt)".
    iMod (ctx_park ξc ξ h with "Hrun Hrunc") as "[Hrun Hpk]".
    iModIntro. iFrame "Hrun". iExists ξc. iFrame.
  Qed.

  (** THE LOCK PATH, RELEASE HALF (relaxed-ww.md §2.4): the holder resumes
      the lock's context from under its own, moves the payload in -- a
      fact it may have STORED TO, still pending -- and stamps at its
      release fence.  Interp-free until the stamp. *)
  Lemma twin_lock_release img log dl tvs ξ ξL h a dq v :
    own_drained h log dl →
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_parked ξL ξ -∗
    ctx_pointsto ξ a dq v ==∗
    tso_interp img log dl tvs ∗ own_context ξ h ∗
    ctx_stamped ξL (length dl) ∗ ctx_pointsto ξL a dq v.
  Proof.
    iIntros (Hod) "Hint Hrun HpkL Hpt".
    iMod (ctx_resume ξL ξ h with "Hrun HpkL") as "[Hrun HrunL]".
    iMod (ctx_move (R := λ ξ0, ctx_pointsto ξ0 a dq v) ξ ξL h with "Hrun HrunL Hpt")
      as "(Hrun & HrunL & Hpt)".
    iMod (ctx_stamp with "Hint HrunL") as "[Hint HstL]"; first done.
    iModIntro. iFrame.
  Qed.

  (** THE LOCK PATH, ACQUIRE HALF: a winner on any hart, at the drain top
      (the AMO's receipt), unstamps the lock's context, moves the payload
      out, parks the emptied context under itself, and reads the stored
      value at every view above its own. *)
  Lemma twin_lock_acquire img log dl tvs ξ' ξL h' T a dq v :
    (length dl ≤ tvs h')%nat →
    tso_interp img log dl tvs -∗ own_context ξ' h' -∗ ctx_stamped ξL T -∗
    ctx_pointsto ξL a dq v ==∗
    tso_interp img log dl tvs ∗ own_context ξ' h' ∗ ctx_parked ξL ξ' ∗
    ctx_pointsto ξ' a dq v ∗
    ⌜∀ tv', (tvs h' ≤ tv')%nat → tso_read (img_fun img) log dl h' tv' a = Some v⌝.
  Proof.
    iIntros (Htop) "Hint Hrun HstL Hpt".
    iDestruct (ctx_stamped_dlb with "HstL") as "[HstL #HT]".
    iDestruct (twin_passed_get _ _ _ _ h' T Htop with "Hint HT") as "(Hint & #HK & %HTK)".
    iMod (ctx_unstamp ξL h' T (tvs h') HTK with "HK HstL") as "HrunL".
    iMod (ctx_move (R := λ ξ0, ctx_pointsto ξ0 a dq v) ξL ξ' h' with "HrunL Hrun Hpt")
      as "(HrunL & Hrun & Hpt)".
    iMod (ctx_park ξL ξ' h' with "Hrun HrunL") as "[Hrun HpkL]".
    iDestruct (twin_load_ok with "Hint Hrun Hpt") as %Hread.
    iModIntro. iFrame. by iPureIntro.
  Qed.

  (** THE THREAD RECORD RIDES THE LOCK (contexts.md §3): a record parked
      under the lock's context stays parked while the lock is stamped,
      unstamped on another hart and resumed there -- with no premise about
      the record itself. *)
  Lemma twin_record_rides ξp ξL h' T K :
    (T ≤ K)%nat →
    view_lb h' K -∗ ctx_stamped ξL T -∗ ctx_parked ξp ξL ==∗
    own_context ξL h' ∗ own_context ξp h'.
  Proof.
    iIntros (HTK) "#HK HstL Hpkp".
    iMod (ctx_unstamp ξL h' T K HTK with "HK HstL") as "HrunL".
    iApply (ctx_resume with "HrunL Hpkp").
  Qed.

End twin4.

(* ================================================================== *)
(** * 2.  Satisfiability: the interp at the boot image                 *)
(* ================================================================== *)

Lemma twin4_init `{!tsoCtx3G Σ} (img : gmap Z (bv 8)) :
  ⊢ |==> ∃ γheap γlogm γdpos γfr γloglen γdlen γview,
      tso_interp γheap γlogm γdpos γfr γloglen γdlen γview img [] [] (λ _, 0%nat) ∗
      [∗ map] a ↦ v ∈ img, a ↪[γheap] ((0%nat, v) : nat * bv 8).
Proof.
  iMod (ghost_map_alloc ((λ v, (0%nat, v)) <$> img)) as (γheap) "[Hh Hfr]".
  iMod (ghost_map_alloc_empty (K := nat) (V := wmsg)) as (γlogm) "Hm".
  iMod (ghost_map_alloc_empty (K := nat) (V := nat)) as (γdpos) "Hdp".
  iMod (ghost_map_alloc_empty (K := agent * nat) (V := nat)) as (γfr) "Hfrm".
  iMod (mono_nat_own_alloc 0) as (γloglen) "[Hlen _]".
  iMod (mono_nat_own_alloc 0) as (γdlen) "[Hdlen _]".
  iMod (own_alloc (● vf (λ _, 0%nat) ⋅ ◯ vf (λ _, 0%nat))) as (γview) "Hv".
  { apply auth_both_valid_discrete. split; [done | by intros h]. }
  iModIntro. iExists γheap, γlogm, γdpos, γfr, γloglen, γdlen, γview.
  iSplitR "Hfr"; last first.
  { iApply (big_sepM_impl with "[Hfr]").
    { by rewrite big_sepM_fmap. }
    iIntros "!>" (a v Hlk) "H". iExact "H". }
  iExists ((λ v, (0%nat, v)) <$> img), ∅, ∅, ∅.
  iFrame "Hh Hm Hdp Hfrm Hlen Hdlen Hv".
  iSplitR; first by rewrite big_sepM_empty.
  iSplitR; first by rewrite big_sepM_empty.
  iPureIntro. split_and!.
  - intros a t v. rewrite lookup_fmap.
    destruct (img !! a) as [v0|] eqn:Ha; last done.
    simpl. intros [= <- <-]. split; [|apply chain_ok_0]. split.
    + rewrite /log_byte /img_fun Ha //.
    + intros t' Ht'. destruct t' as [|i]; first lia. rewrite /log_byte /=. done.
  - intros i. rewrite lookup_empty lookup_nil //.
  - intros i p. rewrite lookup_empty. split; [done|]. intros (q & Hq & _). rewrite lookup_nil in Hq. done.
  - intros N M v. rewrite lookup_empty. done.
  - intros h. simpl. lia.
  - split; [apply NoDup_nil_2|]. intros i Hi. by apply elem_of_nil in Hi.
  - intros i j mi mj qj _ _ _ _ _ Hq. rewrite lookup_nil in Hq. done.
Qed.
