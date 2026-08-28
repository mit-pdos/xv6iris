(* TxPin.v -- THE TRANSACTION PIN, one vocabulary for the eight parks.

   Design: claude-notes/design/fs-ghost-state.md, "the pin inventory".

   Eight places in the file system park the SAME atom -- a positive share of
   an open transaction's [LogDefs.ln_tx] element -- so that a commit, which
   holds that map's authority EMPTY, can refute the state outright:

     * [IcacheEscrow]'s [ic_dep_side] (the write arm's descriptor),
       [ic_out_frz]'s last conjunct (iput's +0x5e..+0x70 freeze window),
       [ic_pin_tx] (the slot pin at [ic_held] and at the frozen payload),
       [ipool_transit] (the pool's in-transit ledger) and [crp_row]'s
       [CrpPre] (the corpse ledger);
     * [InodeRegion]'s [ireg_fpin] (the f column's freeze window),
       [ireg_cpin] (the c column's claim box) and [ireg_parked] (the armed
       registry).

   WHAT DOES *NOT* UNIFY, and the reason this file holds three combinators
   rather than one indexed predicate: the eight parks do not share a KEY and
   cannot share an AUTHORITY.  Three of them are keyed by an icache SLOT, one
   by a fresh ARM ID and four by an INUM -- and even at the inum, two pins
   stand at one key at one moment (create's [ProofCreateFreshTy] holds the
   child's [DepTx] share and the claim box's [ireg_cpin] together;
   [EscrowDeposit.ireg_free_deposit_au] returns [ireg_fpin] and the transit
   ledger's share in one postcondition; iput's +0x70..+0x8a window has the
   slot pin and the f column up at once).  A single-valued per-inum ghost map
   cannot hold two pins at one key, and a multi-valued one would re-create
   the RE-IDENTIFICATION problem the seven existing devices already solve
   ([IcacheRef.hpn_h], [ic_deposit], [iclaim], [ifreeze_pre]/[ifreeze_post],
   [ipool_tkey], [EscrowDefs.crp_elem], [ireg_armed]).  So the pin unifies
   and the devices stay: what every park has in common is the ATOM, and what
   every refutation has in common is [tx_pin_no_ops].

   GAMMA-PARAMETRIC, NEVER [icfg_log]-AMBIENT (durable-notes, "NAMING AN
   AMBIENT CLASS FIELD OUTSIDE ITS CLASS'S SCOPE IS A MEMORY BOMB").  This
   file is a pure leaf with no [icfg] in scope; naming [icfg_log] here would
   send typeclass search after [fileG Σ] with [Σ] unknown.  The ambient
   readings are spelled [tx_pin icfg_log ...] inside the files that already
   bind [ICFG].

   AND NOT [Typeclasses Opaque] (durable-notes, the seal trap).  Seven
   [Timeless] instances downstream ([ireg_fsh], [ireg_cpin], [ic_dep_side],
   [crp_row], [ipool_transit], [ireg_parked], [ic_pin_tx]) are one-line
   [apply _] / [tl_struct]; a seal makes [ghost_map_elem]'s own instance
   unreachable and every one of them breaks.  [SpecIunlockput.ic_dep_side_of_tx]
   also states a LEIBNIZ equality between propositions discharged by
   [reflexivity], which a seal would not survive either.  The three instances
   below are stated explicitly so no consumer has to unfold.

   [LogInv.log_tx_full] / [log_tx_open] are NOT restated here: their
   conclusion names [LogInv.log_tx], which lives above this leaf.  Because
   [tx_pin] is transparent they apply to a [tx_pin γ t 1] by conversion. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import Xv6Cameras.   (* [logG]: [ln_tx]'s [ghost_mapG Σ nat unit] *)
Require Import LogDefs.      (* [log_names], [ln_tx] *)

Section TxPin.
  Context {Σ : gFunctors} `{!logG Σ}.

  (* ONE PARKED SHARE: transaction [t] is open, and [q] of the evidence for
     that is parked here.  [(t, q)] are always FIELDS of whatever records the
     park -- never existentials inside it -- because two halves of one element
     are not the whole: a walk that lent a share must get THAT element back,
     and an existentially keyed share cannot be re-identified. *)
  Definition tx_pin (γ : log_names) (t : nat) (q : Qp) : iProp Σ :=
    (t ↪[ln_tx γ]{#q} tt)%I.

  (* ...AT AN OPTIONAL PARK.  The shape of every park keyed by a column or a
     descriptor that may be empty: [ic_dep_side] (a [DepRd] parks nothing),
     [ireg_cpin] (an unclaimed c column parks nothing). *)
  Definition tx_pin_o (γ : log_names) (o : option (nat * Qp)) : iProp Σ :=
    match o with
    | Some p => tx_pin γ p.1 p.2
    | None   => emp
    end%I.

  (* ...AND AT A LEDGER.  The shape of every park that keeps a MAP of them:
     [ipool_transit] over the in-transit inums, the armed registry's
     [ireg_parked] rows over the arm ids. *)
  Definition tx_pins (γ : log_names) `{Countable K}
      (M : gmap K (nat * Qp)) : iProp Σ :=
    ([∗ map] _ ↦ p ∈ M, tx_pin γ p.1 p.2)%I.

  Global Instance tx_pin_timeless γ t q : Timeless (tx_pin γ t q).
  Proof. rewrite /tx_pin. apply _. Qed.

  Global Instance tx_pin_o_timeless γ o : Timeless (tx_pin_o γ o).
  Proof. rewrite /tx_pin_o. destruct o; apply _. Qed.

  Global Instance tx_pins_timeless γ `{Countable K} M :
    Timeless (tx_pins (K:=K) γ M).
  Proof. rewrite /tx_pins. apply _. Qed.

  (* ==================================================================== *)
  (*  THE REFUTATION EVERY PARK'S OWN [_no_ops] IS AN INSTANCE OF          *)
  (* ==================================================================== *)

  (* THE CORE FACT, and the whole reason the pins exist: a park holds a
     POSITIVE share of some transaction's element, and at a commit the WAL's
     authority for that map is EMPTY ([LogInv.log_tx_empty_of_ops] reads it
     off the ledger), so the state the park witnesses cannot be standing. *)
  Lemma tx_pin_no_ops (γ : log_names) (t : nat) (q : Qp) :
    ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) -∗ tx_pin γ t q -∗ False.
  Proof.
    iIntros "Ha Hp". rewrite /tx_pin.
    iDestruct (ghost_map_lookup with "Ha Hp") as %Hbad.
    rewrite lookup_empty in Hbad. discriminate.
  Qed.

  (* ...at an optional park: it is empty. *)
  Lemma tx_pin_o_no_ops (γ : log_names) (o : option (nat * Qp)) :
    ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) -∗
    tx_pin_o γ o -∗ ⌜o = None⌝.
  Proof.
    iIntros "Ha Hp". destruct o as [p |]; [| done].
    rewrite /tx_pin_o. iDestruct (tx_pin_no_ops with "Ha Hp") as %[].
  Qed.

  (* ...and at a ledger: it is empty.  ONE arbitrary row is enough -- no
     induction, because the conclusion is [M = ∅] and [map_choose] hands the
     witness. *)
  Lemma tx_pins_no_ops (γ : log_names) `{Countable K}
      (M : gmap K (nat * Qp)) :
    ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) -∗
    tx_pins γ M -∗ ⌜M = ∅⌝.
  Proof.
    iIntros "Ha HM". rewrite /tx_pins.
    destruct (decide (M = ∅)) as [-> | Hne]; [done |].
    destruct (map_choose M Hne) as (z & p & Hz).
    iDestruct (big_sepM_lookup _ _ z p Hz with "HM") as "Hp".
    iDestruct (tx_pin_no_ops with "Ha Hp") as %[].
  Qed.

  (* ==================================================================== *)
  (*  THE SPLIT AND ITS INVERSE (restated from [LogInv.log_tx_split] /     *)
  (*  [log_tx_join_q], which are the same equations on the raw element)    *)
  (* ==================================================================== *)

  (* A walk that write-locks TWO inodes at one transaction parks a share in
     each escrow and keeps the rest.  Stated with the total as an EQUATION
     premise rather than as [q1 + q2] in the conclusion: a caller then never
     has to [rewrite] a [Qp] sum inside the proofmode, where the split's evar
     is out of scope (durable-notes, [rewrite -(Qp.div_2 q)]). *)
  Lemma tx_pin_split (γ : log_names) (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    tx_pin γ t q -∗ tx_pin γ t q1 ∗ tx_pin γ t q2.
  Proof. intros ->. rewrite /tx_pin. iIntros "H". iDestruct "H" as "[$ $]". Qed.

  Lemma tx_pin_join_q (γ : log_names) (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    tx_pin γ t q1 -∗ tx_pin γ t q2 -∗ tx_pin γ t q.
  Proof.
    intros ->. rewrite /tx_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  (* the bridge a consumer wants when it must hand the RAW element to a
     [LogInv] lemma (or take one from it) without unfolding this file's
     definition by hand *)
  Lemma tx_pin_elem (γ : log_names) (t : nat) (q : Qp) :
    tx_pin γ t q ⊣⊢ (t ↪[ln_tx γ]{#q} tt).
  Proof. rewrite /tx_pin. done. Qed.
End TxPin.
