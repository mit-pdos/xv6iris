(** * WeakViewMono.v — PROTOTYPE: the hart's weak state as MONOTONE ghost
      state, so it can be threaded as an OPAQUE token with persistent
      lower bounds.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §2 — this file is
    obligation 1 of §5.  NOT wired into anything yet; [WeakGhost.hart_ws] is
    still the exact-valued [ghost_var] the tree uses.

    THE POINT.  [WeakGhost.hart_ws c ws := ghost_var (weak_ws_name c) (1/2) ws]
    is EXACT-valued, and a [ghost_var] can only be updated by naming both the
    old and the new value.  That is the sole reason every leaf reads [ws] in,
    [ws'] out, and carries [⌜ws_le ws ws'⌝] — even for an instruction that
    touches no data, since every instruction fetches its own text and the
    fetch is a view-raising weak read.  [ws_le] is pointwise [≤] on every
    field with no non-monotone component, so the state is a product of
    monotone pieces and the exactness is simply not needed above a leaf. *)
From stdpp Require Import gmap.
From iris.algebra Require Import auth numbers gmap.
From iris.base_logic.lib Require Import iprop own mono_nat.
From iris.proofmode Require Import proofmode.
Require Import WeakMem.

(* ====================================================================== *)
(** ** 1. The five scalar floors.

    [w_vrOld] / [w_vwOld] / [w_vrNew] / [w_vwNew] / [w_vRel] are plain [nat]s
    ordered by [≤], i.e. five [mono_nat]s.  This half is entirely standard
    and uses the same library the tree already uses in [VirtioProto] and
    [RiscvAdequacy]. *)

Class weakViewScalarG (Σ : gFunctors) := {
  wvs_vrOld : mono_natG Σ;
  wvs_vwOld : mono_natG Σ;
  wvs_vrNew : mono_natG Σ;
  wvs_vwNew : mono_natG Σ;
  wvs_vRel  : mono_natG Σ;
}.
Global Existing Instances wvs_vrOld wvs_vwOld wvs_vrNew wvs_vwNew wvs_vRel.

Record ws_names := WsNames {
  wsn_vrOld : gname; wsn_vwOld : gname;
  wsn_vrNew : gname; wsn_vwNew : gname; wsn_vRel : gname;
}.

Section scalars.
  Context `{!weakViewScalarG Σ}.

  (** The AUTHORITY on the five scalars, at an exact state — internal. *)
  Definition ws_scal_auth (γ : ws_names) (w : wstate) : iProp Σ :=
    (mono_nat_auth_own (wsn_vrOld γ) 1 (w_vrOld w) ∗
     mono_nat_auth_own (wsn_vwOld γ) 1 (w_vwOld w) ∗
     mono_nat_auth_own (wsn_vrNew γ) 1 (w_vrNew w) ∗
     mono_nat_auth_own (wsn_vwNew γ) 1 (w_vwNew w) ∗
     mono_nat_auth_own (wsn_vRel  γ) 1 (w_vRel  w))%I.

  (** The persistent LOWER BOUND — duplicable, and (the whole point) it
      survives every intervening step for free, with no [vwp_hold_mono]. *)
  Definition ws_scal_lb (γ : ws_names) (w : wstate) : iProp Σ :=
    (mono_nat_lb_own (wsn_vrOld γ) (w_vrOld w) ∗
     mono_nat_lb_own (wsn_vwOld γ) (w_vwOld w) ∗
     mono_nat_lb_own (wsn_vrNew γ) (w_vrNew w) ∗
     mono_nat_lb_own (wsn_vwNew γ) (w_vwNew w) ∗
     mono_nat_lb_own (wsn_vRel  γ) (w_vRel  w))%I.

  Global Instance ws_scal_lb_persistent γ w : Persistent (ws_scal_lb γ w).
  Proof. apply _. Qed.

  Lemma ws_scal_lb_get γ w : ws_scal_auth γ w -∗ ws_scal_lb γ w.
  Proof.
    iIntros "(H1 & H2 & H3 & H4 & H5)".
    iDestruct (mono_nat_lb_own_get with "H1") as "#L1".
    iDestruct (mono_nat_lb_own_get with "H2") as "#L2".
    iDestruct (mono_nat_lb_own_get with "H3") as "#L3".
    iDestruct (mono_nat_lb_own_get with "H4") as "#L4".
    iDestruct (mono_nat_lb_own_get with "H5") as "#L5".
    by iFrame "L1 L2 L3 L4 L5".
  Qed.

  (** THE UPDATE.  Note what it does NOT need: the caller does not name the
      old state.  Any [ws_le]-larger state is reachable, which is exactly the
      obligation a leaf can discharge internally. *)
  Lemma ws_scal_update γ w w' :
    ws_le w w' -> ws_scal_auth γ w ==∗ ws_scal_auth γ w'.
  Proof.
    intros (_ & H1 & H2 & H3 & H4 & H5).
    iIntros "(A1 & A2 & A3 & A4 & A5)".
    iMod (mono_nat_own_update _ H1 with "A1") as "[$ _]".
    iMod (mono_nat_own_update _ H2 with "A2") as "[$ _]".
    iMod (mono_nat_own_update _ H3 with "A3") as "[$ _]".
    iMod (mono_nat_own_update _ H4 with "A4") as "[$ _]".
    iMod (mono_nat_own_update _ H5 with "A5") as "[$ _]".
    done.
  Qed.

  (** The lower bound is SOUND: what it tells you is a floor, which is the
      direction owned memory needs (knowing your view is AT LEAST [w] is what
      rules out reading stale; a larger real view only makes reads fresher). *)
  Lemma ws_scal_lb_valid γ w w0 :
    ws_scal_auth γ w -∗ ws_scal_lb γ w0 -∗
    ⌜(w_vrOld w0 ≤ w_vrOld w)%nat /\ (w_vwOld w0 ≤ w_vwOld w)%nat /\
     (w_vrNew w0 ≤ w_vrNew w)%nat /\ (w_vwNew w0 ≤ w_vwNew w)%nat /\
     (w_vRel  w0 ≤ w_vRel  w)%nat⌝.
  Proof.
    iIntros "(A1 & A2 & A3 & A4 & A5) (L1 & L2 & L3 & L4 & L5)".
    iDestruct (mono_nat_lb_own_valid with "A1 L1") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A2 L2") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A3 L3") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A4 L4") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A5 L5") as %[_ ?].
    iPureIntro. auto.
  Qed.

End scalars.

(* ====================================================================== *)
(** ** 2. THE PER-BYTE COHERENCE FLOOR — and the trap in encoding it.

    [w_coh : gmap Z nat] with [coh w a := default 0 (w_coh w !! a)], ordered
    by [∀ a, coh w1 a ≤ coh w2 a].  The obvious camera is
    [auth (gmapUR Z max_natUR)] — but the obvious ENCODING
    [MaxNat <$> w_coh w] is WRONG, and quietly so:

      [gmap] inclusion is pointwise inclusion in [option], and
      [Some x ≼ None] is FALSE.  So a state whose map carries an EXPLICIT
      zero entry ([w_coh w1 = {[a := 0]}]) is not included in one that omits
      the key ([w_coh w2 = ∅]) -- even though [ws_le w1 w2] HOLDS, since both
      have [coh _ a = 0].

    So [ws_le] and [≼] disagree exactly on explicit-zero entries, and any
    [ws_le -> ≼] lemma proved against the naive encoding is unprovable.  Two
    ways out, neither yet taken:

      (a) NORMALISE: encode by [MaxNat <$> filter (fun kv => kv.2 ≠ 0%nat)
          (w_coh w)], and carry a normalisation lemma [coh w a] is preserved.
          Keeps one camera; costs a filter-lookup lemma.
      (b) TOTALISE: do not use [gmap] inclusion at all -- use a camera of
          FUNCTIONS [Z -> max_nat] (or [discrete_fun]), for which pointwise
          [≤] IS inclusion on the nose.  Costs a non-finite camera, which is
          fine for a ghost floor that is only ever read at finitely many keys.

    (b) is probably right: [ws_le]'s coherence conjunct is already stated
    over the TOTAL [coh], not over the map, so the function camera matches
    the intended semantics and (a)'s normalisation is an artifact of the
    representation.  Recorded rather than guessed at; this is the next thing
    to build. *)
