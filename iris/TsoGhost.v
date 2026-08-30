(* TsoGhost.v — THE TSO GHOST ALGEBRA, at the machine's types.

   The ghost layer of the real Σ instantiation
   ([claude-notes/projects/tso-machine-flip.md] §4): the per-agent view
   authority and its persistent lower bounds, the log-length mono-nat
   and its receipts, and the dirty-entry justification — everything
   [TsoCtxTwin2.v] proved over the [Z]-typed spike machine, restated
   over [TsoMemPa] (Arch.pa keys, map-payload messages) and
   PARAMETERIZED BY GNAMES, so the same definitions serve the state
   interpretation (at [riscvEraGS]'s era names, RiscvPtsto.v) and the
   context surface (TsoCtx.v).  Nothing here mentions [gstate],
   [riscvGS] or contexts: this file is pure ghost algebra.

   The one deliberate deviation from the twin: every definition takes
   its gname(s) explicitly instead of a Section-wide [Context] — the
   era names live in a record the interp threads, and the context
   names live in [CtxId]. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.algebra Require Import auth dfrac numbers functions gset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map mono_nat.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import TsoMemPa.

(* ================================================================== *)
(** * 1.  The view algebra: one auth over all agents' single-nat views *)
(* ================================================================== *)

(* [TsoCtxTwin2.viewUR], verbatim: the per-agent view collapses the
   weak-memory branch's per-byte floor function to a per-AGENT one — the
   whole per-agent state is one nat ([TsoMemPa]), so the monotone
   summary of "what agent h has observed" is [MaxNat (tvs h)]. *)
Definition viewUR : ucmra := discrete_funUR (λ _ : agent, max_natUR).

Definition vf (tvs : agent → nat) : viewUR := λ h, MaxNat (tvs h).

Definition vone (h : agent) (K : nat) : viewUR :=
  λ h', MaxNat (if decide (h' = h) then K else 0%nat).

Global Instance vf_core_id tvs : CoreId (vf tvs).
Proof. constructor => h. reflexivity. Qed.

Global Instance vone_core_id h K : CoreId (vone h K).
Proof. constructor => h'. reflexivity. Qed.

Lemma vone_incl_vf h K tvs : (K ≤ tvs h)%nat → vone h K ≼ vf tvs.
Proof.
  intros HK. exists (vf tvs). intros h'.
  rewrite discrete_fun_lookup_op /vone /vf max_nat_op.
  rewrite Nat.max_r; [done|].
  destruct (decide (h' = h)) as [->|Hne]; lia.
Qed.

Lemma vf_local_update tvs tvs' :
  (∀ h, tvs h ≤ tvs' h)%nat → (vf tvs, vf tvs) ~l~> (vf tvs', vf tvs').
Proof.
  intros Hle. rewrite local_update_unital_discrete => z _ Heq.
  split; [by intros h|]. intros h. specialize (Heq h). specialize (Hle h).
  rewrite discrete_fun_lookup_op in Heq. rewrite discrete_fun_lookup_op.
  rewrite /vf in Heq |- *.
  destruct (z h) as [zh].
  rewrite max_nat_op in Heq. rewrite max_nat_op.
  revert Heq. intros [= Heq]. rewrite Nat.max_l; [done|lia].
Qed.

(* ================================================================== *)
(** * 2.  The ghost classes                                            *)
(* ================================================================== *)

(* One bundle for everything the TSO machine side needs.  The
   per-context authorities (a mono_nat bound, a dirty ghost_map) reuse
   [tsomem_natG]/[tsomem_dirtyG]; their NAMES ride in [TsoCtx.CtxId]. *)
Class tsoMemG Σ := TsoMemG {
  (* the per-byte timestamp of the latest write; fragments ride inside
     [ctx_pointsto] at the fact's own dq, beside gen_heap's byte.
     THE ELEMENT CARRIES THE PIN (tso-pin-memo.md §5.2, ruling 2): the
     value is [(t, None)] for an ordinary byte and [(t, Some (Sv, B))]
     for a CANON-PINNED one -- the confinement payload of
     [TsoMemPa.pin_ok].  Carrying it in the ELEMENT rather than in a
     gate's premises is what keeps every existing store gate sound with
     no new premise (the sealed definitions pin the option to [None], so
     the interp's frame arm applies definitionally) and what avoids the
     142-site / 36-file [kpt_inv] arity sweep: the bound rides here, not
     in the invariant. *)
  tsomem_tsG :: ghost_mapG Σ Arch.pa TsoMemPa.ts_elem;
  (* the log entries, persisted at append — "log[i] = m" is stable
     because the log is append-only; the dirty author-tie rides here *)
  tsomem_logmG :: ghost_mapG Σ nat pwmsg;
  (* NOTE what is deliberately ABSENT: a [mono_natG Σ] field.  The log
     length and the per-context bounds are mono-nats, but a second
     [mono_natG] instance beside [riscvF_genGS] would make resolution
     ambiguous and split the ghost functor in two (the riscvEraGS
     comments' standing rule); consumers take the class from the ambient
     context -- [riscvF_genGS] in every riscvFixedGS scope. *)
  (* the per-agent views ([view_lb] fragments) *)
  tsomem_viewG :: inG Σ (authR viewUR);
  (* the per-context dirty sets: keys are (timestamp, byte).  A6.128: a
     MONOTONE SET authority ([gsetUR] under [auth]) rather than a ghost map
     with owned element fragments -- membership fragments are persistent
     and RE-MINTABLE from the authority, which is what makes the same-hart
     hand-off of a dirty cell between two running contexts a total rule
     ([TsoCtx.ctx_move_h]): the receiver registers the key whether or not
     it already has it. *)
  tsomem_dirtyG :: inG Σ (authR (gsetUR (nat * Arch.pa)));
}.

(* ---------------------------------------------------------------------- *)
(* A6.63' THE FUNCTOR AND ITS [subG], which the flip needed and did not     *)
(* have.  Without these, [RiscvAdequacy]'s [riscvGpreS] cannot carry the    *)
(* TSO ghosts, and the era record's positional [_] for [riscvF_tsomemGS]    *)
(* has no instance to resolve against -- which is exactly the error the     *)
(* adequacy file has been carrying ("Could not find an instance for         *)
(* ?riscvF_tsomemGS : tsoMemG Σ").                                          *)
(*                                                                          *)
(* NOTE what is deliberately ABSENT, matching the class above: NO           *)
(* [mono_natΣ].  The log length and the per-context bounds are mono-nats,   *)
(* but a second [mono_natG] beside [riscvF_genGS] would make resolution     *)
(* ambiguous; [riscvΣ] already carries the one [mono_natΣ] the whole tree   *)
(* shares.                                                                  *)
(* ---------------------------------------------------------------------- *)
Definition tsoMemΣ : gFunctors :=
  #[ ghost_mapΣ Arch.pa TsoMemPa.ts_elem;
     ghost_mapΣ nat TsoMemPa.pwmsg;
     GFunctor (authR viewUR);
     GFunctor (authR (gsetUR (nat * Arch.pa))) ].

Global Instance subG_tsoMemG {Σ} : subG tsoMemΣ Σ -> tsoMemG Σ.
Proof. solve_inG. Qed.

(* ---------------------------------------------------------------------- *)
(* A6.128 THE DIRTY SET: a monotone set authority with persistent,          *)
(* re-mintable membership.  [dset_auth γ q S] is the (fractional) authority *)
(* at the set [S]; [dset_in γ k] is a persistent witness that [k ∈ S].      *)
(* Nothing is ever removed: a dirty key is a write's (timestamp, byte) and  *)
(* stays registered for the life of the context (the cell's OWNERSHIP moves,*)
(* the registration does not).                                              *)
(* ---------------------------------------------------------------------- *)
Section dset.
  Context {Σ : gFunctors} `{!tsoMemG Σ}.

  Definition dset_auth (γ : gname) (q : Qp) (S : gset (nat * Arch.pa)) : iProp Σ :=
    own γ (●{#q} S).
  Definition dset_in (γ : gname) (k : nat * Arch.pa) : iProp Σ :=
    own γ (◯ ({[k]} : gset (nat * Arch.pa))).

  Global Instance dset_in_persistent γ k : Persistent (dset_in γ k).
  Proof. rewrite /dset_in. apply _. Qed.
  Global Instance dset_in_timeless γ k : Timeless (dset_in γ k).
  Proof. rewrite /dset_in. apply _. Qed.
  Global Instance dset_auth_timeless γ q S : Timeless (dset_auth γ q S).
  Proof. rewrite /dset_auth. apply _. Qed.

  Lemma dset_alloc : ⊢ |==> ∃ γ : gname, dset_auth γ 1 ∅.
  Proof.
    iMod (own_alloc (● (∅ : gset (nat * Arch.pa)))) as (γ) "H".
    { apply auth_auth_valid. done. }
    iModIntro. iExists γ. iExact "H".
  Qed.

  Lemma dset_halves γ S :
    dset_auth γ 1 S ⊣⊢ dset_auth γ (1/2) S ∗ dset_auth γ (1/2) S.
  Proof.
    rewrite /dset_auth -own_op -auth_auth_dfrac_op dfrac_op_own Qp.half_half.
    done.
  Qed.

  Lemma dset_agree γ q1 q2 S1 S2 :
    dset_auth γ q1 S1 -∗ dset_auth γ q2 S2 -∗ ⌜S1 = S2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    exact (auth_auth_dfrac_op_inv_L _ _ _ _ Hv).
  Qed.

  Lemma dset_lookup γ q S k :
    dset_auth γ q S -∗ dset_in γ k -∗ ⌜k ∈ S⌝.
  Proof.
    iIntros "Ha Hk". iCombine "Ha Hk" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    apply auth_both_dfrac_valid_discrete in Hv as (_ & Hincl & _).
    apply gset_included in Hincl. set_solver.
  Qed.

  Lemma dset_get γ q S k :
    k ∈ S -> dset_auth γ q S ==∗ dset_auth γ q S ∗ dset_in γ k.
  Proof.
    iIntros (Hk) "H". rewrite /dset_auth /dset_in -own_op.
    iApply (own_update with "H").
    apply auth_update_dfrac_alloc; [apply _ |]. apply gset_included. set_solver.
  Qed.

  Lemma dset_insert γ S k :
    dset_auth γ 1 S ==∗ dset_auth γ 1 (S ∪ {[k]}) ∗ dset_in γ k.
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● (S ∪ {[k]}) ⋅ ◯ (S ∪ {[k]})) with "H") as "[H _]".
    { apply auth_update_alloc. apply gset_local_update. set_solver. }
    iApply (dset_get with "H"). set_solver.
  Qed.

End dset.

Section ghosts.
  Context {Σ : gFunctors} `{!tsoMemG Σ} `{!mono_natG Σ}.

  (* ---------------------------------------------------------------- *)
  (** ** 3. The log-length lower bound                                 *)
  (* ---------------------------------------------------------------- *)

  (** "The log was at least this long."  The [K = 0] arm keeps the
      empty receipt pure (minting the unit fragment would cost a bupd). *)
  Definition llb (γll : gname) (K : nat) : iProp Σ :=
    (mono_nat_lb_own γll K ∨ ⌜K = 0%nat⌝)%I.

  Global Instance llb_persistent γll K : Persistent (llb γll K).
  Proof. apply _. Qed.
  Global Instance llb_timeless γll K : Timeless (llb γll K).
  Proof. apply _. Qed.

  Lemma llb_0 γll : ⊢ llb γll 0.
  Proof. by iRight. Qed.

  Lemma llb_le γll K K' : (K' ≤ K)%nat → llb γll K -∗ llb γll K'.
  Proof.
    iIntros (Hle) "[Hlb|%Hz]".
    - iLeft. by iApply mono_nat_lb_own_le.
    - iRight. iPureIntro. lia.
  Qed.

  Lemma llb_max γll K1 K2 : llb γll K1 -∗ llb γll K2 -∗ llb γll (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2". destruct (decide (K1 ≤ K2)%nat) as [Hle|Hgt].
    - iClear "H1". iApply (llb_le with "H2"). lia.
    - iClear "H2". iApply (llb_le with "H1"). lia.
  Qed.

  (* >>> A6.105: THE RECEIPT A WRITER CAN ACTUALLY BUY.  A hart's own
     buffered store never advances its own view, so a lock's CREATOR can
     never certify [ctx_floor ξ lo] for the floor its own store just made
     (A6.101's bootstrap, one level up).  What it CAN take off the
     interpretation is this: "[lo] is a real log position".  Paired with an
     AMO's log-top view at the first acquire ([TsoCtx.hart_view_lb_get] +
     [ctx_bound_raise]) that is exactly ruling §0.35'(iii)'s ABSORB, so the
     floor is bought by the READER instead of the writer. <<< *)
  Lemma llb_get γll n :
    mono_nat_auth_own γll 1 n -∗ mono_nat_auth_own γll 1 n ∗ llb γll n.
  Proof.
    iIntros "Ha".
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    iFrame "Ha". by iLeft.
  Qed.

  Lemma llb_valid γll n K :
    mono_nat_auth_own γll 1 n -∗ llb γll K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 4. The stable agent-view lower bound                          *)
  (* ---------------------------------------------------------------- *)

  (** "Agent [h]'s view has passed [K]" — persistent and monotone;
      "h is at the log top" is false one step later, but this is never
      falsified.  It carries an [llb K] because a view never exceeds
      the log length, so every consumer that needs "K is a legal log
      position" has it without the interp.  ([TsoCtxTwin2.view_lb].) *)
  Definition view_lb (γv γll : gname) (h : agent) (K : nat) : iProp Σ :=
    ((own γv (◯ vone h K) ∗ mono_nat_lb_own γll K) ∨ ⌜K = 0%nat⌝)%I.

  Global Instance view_lb_persistent γv γll h K :
    Persistent (view_lb γv γll h K).
  Proof. apply _. Qed.
  Global Instance view_lb_timeless γv γll h K :
    Timeless (view_lb γv γll h K).
  Proof. apply _. Qed.

  Lemma view_lb_0 γv γll h : ⊢ view_lb γv γll h 0.
  Proof. by iRight. Qed.

  Lemma view_lb_llb γv γll h K : view_lb γv γll h K -∗ llb γll K.
  Proof.
    iIntros "[[_ Hlb]|%Hz]"; [by iLeft | by iRight].
  Qed.

  Lemma vone_le_incl h K K' :
    (K' ≤ K)%nat → vone h K' ≼ vone h K.
  Proof.
    intros Hle. exists (vone h K). intros h'.
    rewrite discrete_fun_lookup_op /vone max_nat_op.
    destruct (decide (h' = h)); f_equal; lia.
  Qed.

  Lemma view_lb_le γv γll h K K' :
    (K' ≤ K)%nat → view_lb γv γll h K -∗ view_lb γv γll h K'.
  Proof.
    iIntros (Hle) "[[Hv Hll]|%Hz]".
    - iLeft. iSplitL "Hv".
      + iApply (own_mono with "Hv").
        apply auth_frag_mono, vone_le_incl, Hle.
      + by iApply mono_nat_lb_own_le.
    - iRight. iPureIntro. lia.
  Qed.

  (** The machine-side view authority ([WeakCtx.ctx_auth]'s shape: auth
      and fragment at the same value, so a receipt is INCLUSION rather
      than an update). *)
  Definition view_auth (γv : gname) (tvs : agent → nat) : iProp Σ :=
    own γv (● vf tvs ⋅ ◯ vf tvs).

  (** THE ERA'S MINT (tso-machine-flip.md §6 amendment A6.58, the
      [RiscvAdequacy] inventory's fourth allocation).  Auth AND fragment at
      the same value, so the whole authority is one [own_alloc] with no
      update: [vf tvs] is valid pointwise ([max_natUR] has no invalid
      element) and includes itself, which is exactly [auth_both_valid].
      Stated at an ARBITRARY view function so a later era can be born at
      the view its predecessor left. *)
  Lemma view_auth_alloc (tvs : agent → nat) :
    ⊢ |==> ∃ γv : gname, view_auth γv tvs.
  Proof.
    iApply own_alloc. apply auth_both_valid_discrete.
    split; [reflexivity | intros h; done].
  Qed.

  Lemma view_auth_frag γv tvs h K :
    (K ≤ tvs h)%nat → view_auth γv tvs -∗ own γv (◯ vone h K).
  Proof.
    iIntros (HK) "Hv". iApply (own_mono with "Hv").
    etrans; [apply auth_frag_mono, vone_incl_vf, HK | apply cmra_included_r].
  Qed.

  Lemma view_auth_valid γv γll tvs h K :
    view_auth γv tvs -∗ view_lb γv γll h K -∗ ⌜(K ≤ tvs h)%nat⌝.
  Proof.
    iIntros "Ha [[Hf _]|%Hz]"; last (iPureIntro; lia).
    iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro.
    move: Hv. rewrite -assoc -auth_frag_op.
    rewrite auth_both_valid_discrete => -[Hincl _].
    apply (discrete_fun_included_spec_1 _ _ h) in Hincl.
    move: Hincl. rewrite discrete_fun_lookup_op /vf /vone max_nat_op.
    rewrite decide_True; last done.
    move => /max_nat_included /=. lia.
  Qed.

  Lemma view_auth_update γv tvs tvs' :
    (∀ h, tvs h ≤ tvs' h)%nat → view_auth γv tvs ==∗ view_auth γv tvs'.
  Proof.
    iIntros (Hle). iApply own_update.
    by apply auth_update, vf_local_update.
  Qed.

  (** The view receipt, minted where the authority is open (the
      load/AMO leaves): the current view, paired with the log-length
      receipt that keeps it a legal position. *)
  Lemma view_lb_get γv γll tvs (n : nat) h :
    (tvs h ≤ n)%nat →
    view_auth γv tvs -∗ mono_nat_auth_own γll 1 n -∗
    view_auth γv tvs ∗ mono_nat_auth_own γll 1 n ∗
    view_lb γv γll h (tvs h).
  Proof.
    iIntros (Htop) "Hv Hll".
    iDestruct (view_auth_frag γv tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hll") as "#Hlb".
    iFrame "Hv Hll". iLeft. iFrame "Hf".
    iApply (mono_nat_lb_own_le with "Hlb"). exact Htop.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 5. The dirty entry's justification                            *)
  (* ---------------------------------------------------------------- *)

  (** Kept in the RUNNING BUNDLE (never in the fact): the entry's
      timestamp is already under the bound (morally clean, flipped
      lazily), or it is the agent's own message — the forwarding arm of
      [visibleb].  The author-tie names the BUNDLE's agent, which is
      exactly why park must raise the bound before the context can
      leave [h]: the weak-memory branch's migration invariant, at a
      single nat.  ([TsoCtxTwin2.dirty_ok] at the era's log name.) *)
  Definition dirty_ok (γlogm : gname) (h : agent) (B : nat)
      (k : nat * Arch.pa) : iProp Σ :=
    (⌜(k.1 ≤ B)%nat⌝ ∨
     ∃ i m, ⌜k.1 = S i⌝ ∗ i ↪[γlogm]□ m ∗ ⌜pm_tid m = h⌝)%I.

  Global Instance dirty_ok_persistent γlogm h B k :
    Persistent (dirty_ok γlogm h B k).
  Proof. apply _. Qed.

  Lemma dirty_ok_mono γlogm h B B' k :
    (B ≤ B')%nat → dirty_ok γlogm h B k -∗ dirty_ok γlogm h B' k.
  Proof.
    iIntros (Hle) "[%Hb|H]"; [iLeft; iPureIntro; lia | by iRight].
  Qed.
End ghosts.
