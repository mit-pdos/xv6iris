(* ===================================================================== *)
(*  DirViewLend.v -- M1, THE CANCELLABLE LEND [dv_ride / dv_pin]          *)
(*  (the three OPERATIONS, which open the region: InodeRegion.v §L;       *)
(*   the pinned namei corollary that consumes them: DirViewPin.v)         *)
(*  (claude-notes/projects/namei-pinned-lookup.md §11.2, ruled D-N4a;     *)
(*   stage N-4, PHASE B: E1-region, the Timeless re-spelling)             *)
(* ===================================================================== *)

(*  WHAT IT IS.  N-1's [DirViewG.dv_hold] rides the custody chain WHOLE,
    because [dv_set] -- the free own-update every byte-write mover uses --
    needs [DfracOwn 1].  A client that wants to know a directory's contents
    ACROSS TIME must therefore subtract something from what the writer can
    gather, and §11.1's triangle says one of the three properties has to go.
    M1 gives up (U), unconditional redemption: the lend is an ESCROW whose
    CANCELLATION IS UNGATED, so no writer is ever stuck and no landed
    contract grows a premise.  What the client gets back is a DISJUNCTION --
    "the contents are still what you pinned" OR "a receipt naming the
    directory that was modified under you".  A concurrent unlink can race
    namei; M1's receipt is that race, named.

    ---------------------------------------------------------------------
    PHASE B, E1-region (RULED): WHERE THE LEND BODY LIVES.

    Phase A hosted the escrowed ¼ in an [inv] of its own and reported the
    obstruction that follows from that choice: the ride arm has to carry the
    handle, [inv] is never Timeless, and [ic_loaded_timeless] -- hence every
    [iInv "Hesc" as ">"] in the tree -- dies.  The ruling was E1: put the
    body in a per-inum column of the INODE REGION, which is ambient in every
    fs contract, openable at every instant the lend is touched, and whose
    ledgers are all-[own].  So:

      * the COLUMN [dv_lcol z] (below) is one per inum and all [own]:
        NONE ∨ INTACT(¼ + the pending one-shot) ∨ CANCELLED(the shot one).
        It is parked in [InodeRegion.ireg_registry] -- the region's per-inum
        SIDE ledger, the conjunct of [ireg_body] that every accessor already
        threads opaquely -- so not one [ireg_slot] lemma moves.
      * the operations ([dv_set_rt], [dv_pin_redeem]) live in
        [InodeRegion.v] §L, take an [ireg_inv] argument (a
        PERSISTENT handle every calling context already holds) and open
        [↑iregN].  No spec text changes anywhere.
      * everything a client or a writer carries -- the ride's marker, the
        pin, the receipt -- is an [own] plus a pure bound, so [dv_ride] is
        Timeless and the [">"]-discipline is untouched.

    ---------------------------------------------------------------------
    THE γ-AGREEMENT SCHEME: the ESCROW-NAME REGISTRY, at negative keys.

    The client and the region must agree on WHICH cells carry this inum's
    lend.  That is exactly the problem [icfg_reg] -- the per-inum
    escrow-name registry, a [ghost_map Z (gname * gname)] whose authority
    already lives inside [ireg_body] -- was built to solve, and its
    authority is also what makes a lend slot ALLOCATABLE at all (a bare
    [own] map cannot grow a key; a ghost_map under its own auth can, which
    is why NO boot map and no [icfg] field had to change).  The lend rides
    the SAME registry at a DISJOINT key space:

      dvl_k z = -4z-1   the dview LEND SLOT     (negatives = 3 mod 4)
      dvl_l z = -4z-2   the dview MINT LICENCE  (negatives = 2 mod 4)
      fvl_k z = -4z-3   the fview LEND SLOT     (negatives = 1 mod 4)
      fvl_l z = -4z-4   the fview MINT LICENCE  (negatives = 0 mod 4)

    N-5.2A RE-SPELLED THE TWO dview KEYS (from -2z-1 / -2z-2, D-52c).  Phase
    B's pair already covered EVERY negative integer between them -- odd and
    even -- so the fview column had no free key at all: the residues had to
    widen from 2 to 4 before a second ghost could ride the same registry.
    The change is value-only (the four families are still affine in z, still
    negative, still pairwise disjoint by residue and injective), it is
    internal to this file and [IcacheBoot], and nothing anywhere depends on
    the numeric value of a key.

    Region inums are non-negative, so no landed registry key can collide,
    and the coverage clause [ireg_registry] carries ("every inum in range is
    bound") is preserved by insertions outside its range.  [EscrowDeposit]'s
    rebind touches key [inum] only.

    THE FRACTION LEDGER OF ONE LEND SLOT, which is the whole discipline:

      state       region     ¾-arm marker    client pin     licence
      NONE          1             --             --         out (whole)
      INTACT        ¼             ½              ¼          in the arm
      CANCELLED     ¾             --             ¼          in the arm

    Every refutation the three operations need is one fraction overflow:

      * a writer at the ¾ arm holds ½, so it refutes NONE (1+½) and
        CANCELLED (¾+½).  It therefore ALWAYS finds INTACT -- which is
        what makes [dv_set_rt] TOTAL with no premise beyond the ride.
      * a client holds ¼, so it refutes NONE (1+¼); INTACT and CANCELLED
        are its two honest answers.
      * a minter holds the LICENCE, which the mint DEPOSITS into the
        column, so it refutes INTACT and CANCELLED: one lend per inum,
        enforced by a token rather than by a side condition.

    THE TWO CELLS a slot's value names.  Both are [dviewUR] maps at gnames
    allocated ONCE, at region boot, and KEYED BY INUM -- so the pair bound
    at every lend slot is the same, and nothing has to be re-bound at a
    mint (the registry auth therefore never appears in a lend operation):

      γc  the CANCELLATION one-shot.  WHOLE ([DfracOwn 1]) in the column at
          every unlent and intact instant, and DISCARDED by the writer that
          cancels.  Nobody outside the column ever holds a share of it, so
          the persistent receipt [dv_cshot] CANNOT be forged by a client --
          which is what makes the pinned spec's right arm mean something.
      γv  the VALUE WITNESS.  Cut in half at the mint: one half in the
          column, one in the pin.  Agreement on it is what says "the lend
          the column is holding is MY lend, at MY contents", with the client
          owning no fraction of the directory itself.

    NO new [inG] ([icache_regG] and [icache_dviewG] are both landed), NO new
    [icfg] field, NO functor row, NO boot map widened.

    RETIREMENT IS LAZY (charter).  An INTACT redeem is a pure read: the pin
    comes back unspent and the ¼ stays lent.  A CANCELLED redeem spends the
    pin into the persistent receipt.  There is deliberately no retire
    operation.                                                             *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap list namespaces bitvector.definitions.
From iris.algebra Require Import gmap dfrac excl updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map.
Require Import SailStdpp.Values.
Require Import DinodeEnc.   (* [dinode], [di_size]                          *)
Require Import FsTree.      (* [fname], [dir_view]                          *)
Require Import IcacheRef.   (* [icfg], [icfg_dview], [icfg_reg], [dviewUR]  *)
Require Import DirViewG.    (* [dv_half], [dv_hold], [dv_set], [dv_agree]   *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE KEY SPACE                                                     *)
(* ===================================================================== *)

(* The lend's two registry keys for inum [z].  Both are NEGATIVE (region
   inums are not) and they never collide with each other ([dvl_k] is odd,
   [dvl_l] is even), so the three key spaces partition their union. *)
Definition dvl_k (z : Z) : Z := -(4 * z) - 1.
Definition dvl_l (z : Z) : Z := -(4 * z) - 2.
(* N-5.2A: the fview column's two families, at the two residues the widening
   above freed. *)
Definition fvl_k (z : Z) : Z := -(4 * z) - 3.
Definition fvl_l (z : Z) : Z := -(4 * z) - 4.

Lemma dvl_k_neg (z : Z) : 0 <= z -> dvl_k z < 0.
Proof. rewrite /dvl_k. lia. Qed.
Lemma dvl_l_neg (z : Z) : 0 <= z -> dvl_l z < 0.
Proof. rewrite /dvl_l. lia. Qed.
Lemma fvl_k_neg (z : Z) : 0 <= z -> fvl_k z < 0.
Proof. rewrite /fvl_k. lia. Qed.
Lemma fvl_l_neg (z : Z) : 0 <= z -> fvl_l z < 0.
Proof. rewrite /fvl_l. lia. Qed.

(* THE SIX PAIRWISE DISJOINTNESSES.  Each one is a residue argument [lia]
   discharges outright, and together they are what says the four key spaces
   partition their union. *)
Lemma dvl_k_l_ne (z1 z2 : Z) : dvl_k z1 <> dvl_l z2.
Proof. rewrite /dvl_k /dvl_l. lia. Qed.
Lemma dvl_k_fvl_k_ne (z1 z2 : Z) : dvl_k z1 <> fvl_k z2.
Proof. rewrite /dvl_k /fvl_k. lia. Qed.
Lemma dvl_k_fvl_l_ne (z1 z2 : Z) : dvl_k z1 <> fvl_l z2.
Proof. rewrite /dvl_k /fvl_l. lia. Qed.
Lemma dvl_l_fvl_k_ne (z1 z2 : Z) : dvl_l z1 <> fvl_k z2.
Proof. rewrite /dvl_l /fvl_k. lia. Qed.
Lemma dvl_l_fvl_l_ne (z1 z2 : Z) : dvl_l z1 <> fvl_l z2.
Proof. rewrite /dvl_l /fvl_l. lia. Qed.
Lemma fvl_k_l_ne (z1 z2 : Z) : fvl_k z1 <> fvl_l z2.
Proof. rewrite /fvl_k /fvl_l. lia. Qed.

Global Instance dvl_k_inj : Inj eq eq dvl_k.
Proof. intros z1 z2. rewrite /dvl_k. lia. Qed.
Global Instance dvl_l_inj : Inj eq eq dvl_l.
Proof. intros z1 z2. rewrite /dvl_l. lia. Qed.
Global Instance fvl_k_inj : Inj eq eq fvl_k.
Proof. intros z1 z2. rewrite /fvl_k. lia. Qed.
Global Instance fvl_l_inj : Inj eq eq fvl_l.
Proof. intros z1 z2. rewrite /fvl_l. lia. Qed.

(* the Qp cuts the ledger above is spelled at *)
Lemma dfrac_1_hh : DfracOwn 1 = DfracOwn (1/2) ⋅ DfracOwn (1/2).
Proof. rewrite dfrac_op_own. by rewrite Qp.half_half. Qed.
Lemma dvl_q_over_1_12 : (1 < 1 + 1/2)%Qp.
Proof. apply Qp.lt_add_l. Qed.
Lemma dvl_q_over_34_12 : (1 < 3/4 + 1/2)%Qp.
Proof.
  assert (H : (3/4 + 1/2)%Qp = (1 + 1/4)%Qp) by compute_done.
  rewrite H. apply Qp.lt_add_l.
Qed.
Lemma dvl_q_over_1_14 : (1 < 1 + 1/4)%Qp.
Proof. apply Qp.lt_add_l. Qed.

Section DirViewLendDefs.
  Context `{!icacheG Σ}.
  Context `{ICFG : icfg}.

  (* ===================================================================== *)
  (*  1.  THE CELLS                                                         *)
  (* ===================================================================== *)

  (*  ALTITUDE.  This file sits DIRECTLY ABOVE [DirViewG] -- [icacheG] for
      the cells, nothing else -- and that is load-bearing rather than tidy:
      [InodeRegion] must be able to NAME [dv_lcol] in order to park it, and
      every consumer of [dv_ride] (IcacheEscrow, EscrowInode, IcacheBoot,
      FsCfgBoot, and the byte-write movers above them) sits above the
      region.  So the three OPERATIONS, which open [↑iregN], are in
      [InodeRegion.v] §L rather than here, and the pinned corollary, which
      is above the namei cone, is in [DirViewPin.v].                       *)

  (* THE REGION'S ADDRESS SPACE, as a pure clause the lend's own tokens
     carry: an operation on a ride or a pin then needs no bound premise. *)
  Definition dvl_dom (z : Z) : Prop := 0 <= z < 16 * Z.of_nat icfg_nib.

  (* ---- the registry element, at the lend's key space ---------------- *)

  Definition dvl_slot (z : Z) (dq : dfrac) (g : gname * gname) : iProp Σ :=
    (dvl_k z ↪[icfg_reg]{dq} g)%I.

  (* THE MINT LICENCE: the whole element at the licence key.  Exclusive, so
     depositing it into the column is what forbids a second mint. *)
  Definition dv_lic (z : Z) : iProp Σ :=
    (∃ g : gname * gname, dvl_l z ↪[icfg_reg] g)%I.

  (* ---- the two boot-allocated cells, both at [dviewUR] --------------- *)

  (* A [dviewUR] cell at a given gname, keyed by inum.  Same RA as
     [DirViewG.dv_half], different name -- see the header. *)
  Definition dvl_cell (γ : gname) (z : Z) (dq : dfrac) (e : gmap fname Z)
    : iProp Σ :=
    own γ ({[ z := to_dfrac_agree dq (e : leibnizO (gmap fname Z)) ]} : dviewUR).

  (* PENDING: the lend has not been cancelled.  WHOLE, and only ever in the
     column: no client can produce it, hence none can forge the shot. *)
  Definition dv_ctick (γc : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    dvl_cell γc z (DfracOwn 1) e.

  (* SHOT: the lend was cancelled by a writer.  Persistent, Timeless, and
     it NAMES the directory and the contents that were pinned. *)
  Definition dv_cshot (γc : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    dvl_cell γc z DfracDiscarded e.

  (* THE VALUE WITNESS' HALF: one in the column, one in the pin. *)
  Definition dv_vwit (γv : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    dvl_cell γv z (DfracOwn (1/2)) e.

  (* ===================================================================== *)
  (*  2.  THE COLUMN, THE RIDE, THE PIN, THE RECEIPT                        *)
  (* ===================================================================== *)

  (* ONE INUM'S LEND COLUMN -- what [InodeRegion.ireg_registry] parks.  Every
     arm is [own], so the column, the region body and everything the region
     is a conjunct of stay Timeless. *)
  Definition dv_lcol (z : Z) : iProp Σ :=
    ( (* NONE: nothing was ever lent at this inum.  The region holds the
         whole slot element and both cells un-armed; the licence is out. *)
      (∃ γc γv : gname,
         dvl_slot z (DfracOwn 1) (γc, γv)
         ∗ dvl_cell γc z (DfracOwn 1) ∅ ∗ dvl_cell γv z (DfracOwn 1) ∅)
    ∨ (* INTACT: the escrowed ¼ of the contents, the pending one-shot, the
         column's half of the value witness, the deposited licence. *)
      (∃ (γc γv : gname) (e : gmap fname Z),
         dvl_slot z (DfracOwn (1/4)) (γc, γv) ∗ dv_lic z
         ∗ dv_half z (DfracOwn (1/4)) e ∗ dv_ctick γc z e ∗ dv_vwit γv z e)
    ∨ (* CANCELLED: the ¼ was gathered by a writer, the one-shot is shot,
         and the ¾-arm's ½ of the slot came back with it. *)
      (∃ (γc γv : gname) (e : gmap fname Z),
         dvl_slot z (DfracOwn (3/4)) (γc, γv) ∗ dv_lic z
         ∗ dv_cshot γc z e ∗ dv_vwit γv z e) )%I.

  (* THE ¾ ARM'S MARKER: half the slot element (which refutes both unlent
     arms by fraction overflow) plus the region bound (which is why no
     operation on the ride needs an inum-range premise).  The contents
     index is carried for the ride's shape only. *)
  Definition dv_lentm (z : Z) (e : gmap fname Z) : iProp Σ :=
    (⌜dvl_dom z⌝ ∗ ∃ g : gname * gname, dvl_slot z (DfracOwn (1/2)) g)%I.

  (* THE CUSTODY-CHAIN SHAPE: what replaces [dv_hold] on every arm of the
     chain.  Timeless, exclusive at an inum, and free from a hold. *)
  Definition dv_ride (z : Z) (e : gmap fname Z) : iProp Σ :=
    (dv_hold z e ∨ (dv_half z (DfracOwn (3/4)) e ∗ dv_lentm z e))%I.

  (* THE CLIENT PACKAGE: a quarter of the slot (which names the lend's two
     cells) and half the value witness (which names its contents). *)
  Definition dv_pin (z : Z) (e : gmap fname Z) : iProp Σ :=
    (⌜dvl_dom z⌝ ∗ ∃ γc γv : gname,
       dvl_slot z (DfracOwn (1/4)) (γc, γv) ∗ dv_vwit γv z e)%I.

  (* WHAT AN INTACT REDEEM RETURNS.  In the E1 spelling redemption is a
     READ, so the pin comes back whole.  (Phase A's version burned a ticket
     because its redeem had to close a private invariant; the column's does
     not.) *)
  Definition dv_pin_spent (z : Z) (e : gmap fname Z) : iProp Σ :=
    dv_pin z e.

  (* THE RECEIPT: "the lend taken on directory [z] at contents [e] was
     cancelled", i.e. some writer moved [z]'s contents since the pin.  The
     persisted slot element ties [z] to the lend's cells; the shot one-shot
     is the cancellation itself, and only a writer can produce it. *)
  Definition dv_cancelled (z : Z) (e : gmap fname Z) : iProp Σ :=
    (∃ γc γv : gname,
       dvl_slot z DfracDiscarded (γc, γv) ∗ dv_cshot γc z e)%I.

  (* ------------------------------------------------------------------- *)
  (*  instances -- EVERYTHING here is Timeless, which is E1's whole point  *)
  (* ------------------------------------------------------------------- *)

  Global Instance dvl_slot_timeless z dq g : Timeless (dvl_slot z dq g).
  Proof. rewrite /dvl_slot. apply _. Qed.
  Global Instance dv_lic_timeless z : Timeless (dv_lic z).
  Proof. rewrite /dv_lic. apply _. Qed.
  Global Instance dvl_cell_timeless γ z dq e : Timeless (dvl_cell γ z dq e).
  Proof. apply _. Qed.
  Global Instance dv_ctick_timeless γc z e : Timeless (dv_ctick γc z e).
  Proof. apply _. Qed.
  Global Instance dv_cshot_timeless γc z e : Timeless (dv_cshot γc z e).
  Proof. apply _. Qed.
  Global Instance dv_vwit_timeless γv z e : Timeless (dv_vwit γv z e).
  Proof. apply _. Qed.

  Global Instance dv_cshot_persistent γc z e : Persistent (dv_cshot γc z e).
  Proof.
    rewrite /dv_cshot /dvl_cell /to_dfrac_agree.
    apply own_core_persistent, _.
  Qed.

  Global Instance dv_lcol_timeless z : Timeless (dv_lcol z).
  Proof. rewrite /dv_lcol. apply _. Qed.
  Global Instance dv_lentm_timeless z e : Timeless (dv_lentm z e).
  Proof. rewrite /dv_lentm. apply _. Qed.
  Global Instance dv_ride_timeless z e : Timeless (dv_ride z e).
  Proof. rewrite /dv_ride. apply _. Qed.
  Global Instance dv_pin_timeless z e : Timeless (dv_pin z e).
  Proof. rewrite /dv_pin. apply _. Qed.
  Global Instance dv_cancelled_timeless z e : Timeless (dv_cancelled z e).
  Proof. rewrite /dv_cancelled. apply _. Qed.

  Global Instance dv_cancelled_persistent z e : Persistent (dv_cancelled z e).
  Proof. rewrite /dv_cancelled. apply _. Qed.

  (* ===================================================================== *)
  (*  3.  THE SLOT'S FRACTION ARITHMETIC                                    *)
  (* ===================================================================== *)

  Lemma dvl_slot_split (z : Z) (p q : Qp) (g : gname * gname) :
    dvl_slot z (DfracOwn (p + q)) g ⊣⊢
      dvl_slot z (DfracOwn p) g ∗ dvl_slot z (DfracOwn q) g.
  Proof.
    rewrite /dvl_slot.
    apply (fractional (Φ := fun q => (dvl_k z ↪[icfg_reg]{#q} g)%I)).
  Qed.

  Lemma dvl_slot_join (z : Z) (p q : Qp) (g1 g2 : gname * gname) :
    dvl_slot z (DfracOwn p) g1 -∗ dvl_slot z (DfracOwn q) g2 -∗
    ⌜g1 = g2⌝ ∗ dvl_slot z (DfracOwn (p + q)) g1.
  Proof.
    rewrite /dvl_slot. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iSplitR; [done |]. subst g2.
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  (* THE THREE-WAY CUT the mint performs, and the two-way one the writer
     re-assembles: ¼ (region) + ½ (arm) + ¼ (pin) = 1. *)
  Lemma dvl_slot_cut (z : Z) (g : gname * gname) :
    dvl_slot z (DfracOwn 1) g ⊣⊢
      dvl_slot z (DfracOwn (1/4)) g ∗ dvl_slot z (DfracOwn (1/2)) g
      ∗ dvl_slot z (DfracOwn (1/4)) g.
  Proof.
    rewrite -(dvl_slot_split z (1/2) (1/4) g).
    rewrite -(dvl_slot_split z (1/4) (1/2 + 1/4) g).
    by assert ((1/4 + (1/2 + 1/4))%Qp = 1%Qp) as -> by compute_done.
  Qed.

  Lemma dvl_slot_join34 (z : Z) (g1 g2 : gname * gname) :
    dvl_slot z (DfracOwn (1/4)) g1 -∗ dvl_slot z (DfracOwn (1/2)) g2 -∗
    ⌜g1 = g2⌝ ∗ dvl_slot z (DfracOwn (3/4)) g1.
  Proof.
    iIntros "H1 H2".
    iDestruct (dvl_slot_join with "H1 H2") as "[%Hg H]".
    iSplitR; [done |].
    by assert ((3/4)%Qp = (1/4 + 1/2)%Qp) as -> by compute_done.
  Qed.

  Lemma dvl_slot_agree (z : Z) (dq1 dq2 : dfrac) (g1 g2 : gname * gname) :
    dvl_slot z dq1 g1 -∗ dvl_slot z dq2 g2 -∗ ⌜g1 = g2⌝.
  Proof.
    rewrite /dvl_slot. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* THE OVERFLOW: "these two shares add to more than one", which is every
     refutation the three operations need. *)
  Lemma dvl_slot_over (z : Z) (p q : Qp) (g1 g2 : gname * gname) :
    (1 < p + q)%Qp ->
    dvl_slot z (DfracOwn p) g1 -∗ dvl_slot z (DfracOwn q) g2 -∗ False.
  Proof.
    intros Hlt. rewrite /dvl_slot. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
    exact (proj1 (Qp.lt_nge _ _) Hlt Hv).
  Qed.

  Lemma dv_lic_excl (z : Z) : dv_lic z -∗ dv_lic z -∗ False.
  Proof.
    rewrite /dv_lic. iIntros "[%g1 H1] [%g2 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
    exact (Qp.not_add_le_l 1 1 Hv).
  Qed.

  (* ===================================================================== *)
  (*  4.  THE CONTENTS' FRACTION ARITHMETIC (the ¾ / ¼ cut)                 *)
  (* ===================================================================== *)

  Lemma dfrac_1_34 : DfracOwn 1 = DfracOwn (3/4) ⋅ DfracOwn (1/4).
  Proof. rewrite dfrac_op_own. by rewrite Qp.three_quarter_quarter. Qed.

  Lemma dv_hold_split34 (z : Z) (e : gmap fname Z) :
    dv_hold z e ⊣⊢ dv_half z (DfracOwn (3/4)) e ∗ dv_half z (DfracOwn (1/4)) e.
  Proof. rewrite /dv_hold {1}dfrac_1_34. apply dv_split. Qed.

  Lemma dv_join34 (z : Z) (e : gmap fname Z) :
    dv_half z (DfracOwn (3/4)) e -∗ dv_half z (DfracOwn (1/4)) e -∗
    dv_hold z e.
  Proof. iIntros "H1 H2". rewrite dv_hold_split34. iFrame. Qed.

  (* A WHOLE HOLD REFUTES ANY OTHER FRACTION -- [DirViewG.dv_hold_excl] at a
     general [dq], which is the form the ride's cross-arm cases need. *)
  Lemma dv_hold_half_excl (z : Z) (dq : dfrac) (e1 e2 : gmap fname Z) :
    dv_hold z e1 -∗ dv_half z dq e2 -∗ False.
  Proof.
    rewrite /dv_hold /dv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv; [| apply to_dfrac_agree_exclusive].
  Qed.

  (* AND TWO ¾ ARMS REFUTE EACH OTHER: 3/4 + 3/4 = 1 + 1/2 is not valid.
     This is the whole reason the split is ¾/¼ and not ½/½ -- at halves a
     second lend would be sound, and the "one lend per directory"
     discipline would have to be carried by a token instead. *)
  Lemma dv_half34_excl (z : Z) (e1 e2 : gmap fname Z) :
    dv_half z (DfracOwn (3/4)) e1 -∗ dv_half z (DfracOwn (3/4)) e2 -∗ False.
  Proof.
    rewrite /dv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply dfrac_agree_op_valid_L in Hv as [Hd _].
    rewrite dfrac_op_own dfrac_valid_own in Hd.
    assert (Hq : (3/4 + 3/4)%Qp = (1 + 1/2)%Qp) by compute_done.
    rewrite Hq in Hd. by apply (Qp.not_add_le_l 1 (1/2)) in Hd.
  Qed.

  (* THE RIDE IS A CUSTODY TOKEN: two of them at one inum is a refutation,
     on all four cross-arm cases. *)
  Lemma dv_ride_excl (z : Z) (e1 e2 : gmap fname Z) :
    dv_ride z e1 -∗ dv_ride z e2 -∗ False.
  Proof.
    rewrite /dv_ride. iIntros "[H1|[H1 _]] [H2|[H2 _]]".
    - iApply (dv_hold_excl with "H1 H2").
    - iApply (dv_hold_half_excl with "H1 H2").
    - iApply (dv_hold_half_excl with "H2 H1").
    - iApply (dv_half34_excl with "H1 H2").
  Qed.

  Lemma dv_ride_of_hold (z : Z) (e : gmap fname Z) :
    dv_hold z e -∗ dv_ride z e.
  Proof. iIntros "H". rewrite /dv_ride. by iLeft. Qed.

  (* [DirViewG.dv_hold_size]'s analogue, for the re-pack sites whose record
     move leaves [di_size] alone: the ride carries the same rewriting. *)
  Lemma dv_ride_size (z : Z) (dn1 dn2 : dinode) (data : nat -> list (bv 8)) :
    di_size dn1 = di_size dn2 ->
    dv_ride z (dv_of dn1 data) -∗ dv_ride z (dv_of dn2 data).
  Proof.
    intros Hs. rewrite (dv_of_size dn1 dn2 data Hs). iIntros "H". iExact "H".
  Qed.

  (* NO SECOND MINT ON ONE DIRECTORY, and this is the whole discipline: a
     mint demands [dv_hold], and a directory that already rides a lend has
     only ¾ on the chain, so no [dv_hold] for it can exist anywhere. *)
  Lemma dv_lend_no_second_mint (z : Z) (e1 e2 : gmap fname Z) :
    dv_half z (DfracOwn (3/4)) e1 -∗ dv_lentm z e1 -∗ dv_hold z e2 -∗ False.
  Proof.
    iIntros "H34 _ Hw". iApply (dv_hold_half_excl with "Hw H34").
  Qed.

  (* ===================================================================== *)
  (*  5.  THE CELLS' MOVES                                                  *)
  (* ===================================================================== *)

  Lemma dvl_cell_agree (γ : gname) (z : Z) (dq1 dq2 : dfrac)
      (e1 e2 : gmap fname Z) :
    dvl_cell γ z dq1 e1 -∗ dvl_cell γ z dq2 e2 -∗ ⌜e1 = e2⌝.
  Proof.
    rewrite /dvl_cell. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. by apply dfrac_agree_op_valid_L in Hv as [_ ->].
  Qed.

  Lemma dv_vwit_agree (γv : gname) (z : Z) (e1 e2 : gmap fname Z) :
    dv_vwit γv z e1 -∗ dv_vwit γv z e2 -∗ ⌜e1 = e2⌝.
  Proof. rewrite /dv_vwit. apply dvl_cell_agree. Qed.

  Lemma dvl_cell_split (γ : gname) (z : Z) (dq1 dq2 : dfrac)
      (e : gmap fname Z) :
    dvl_cell γ z (dq1 ⋅ dq2) e ⊣⊢ dvl_cell γ z dq1 e ∗ dvl_cell γ z dq2 e.
  Proof.
    rewrite /dvl_cell -own_op singleton_op.
    by rewrite -dfrac_agree_op.
  Qed.

  Lemma dvl_cell_cut (γ : gname) (z : Z) (e : gmap fname Z) :
    dvl_cell γ z (DfracOwn 1) e ⊣⊢
      dvl_cell γ z (DfracOwn (1/2)) e ∗ dvl_cell γ z (DfracOwn (1/2)) e.
  Proof. rewrite -dvl_cell_split -dfrac_1_hh. done. Qed.

  (* the whole cell moves freely -- [DirViewG.dv_set]'s line *)
  Lemma dvl_cell_set (γ : gname) (z : Z) (e e' : gmap fname Z) :
    dvl_cell γ z (DfracOwn 1) e ==∗ dvl_cell γ z (DfracOwn 1) e'.
  Proof.
    rewrite /dvl_cell. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, cmra_update_exclusive.
    split; done.
  Qed.

  Lemma dv_cshoot (γc : gname) (z : Z) (e : gmap fname Z) :
    dv_ctick γc z e ==∗ dv_cshot γc z e.
  Proof.
    rewrite /dv_ctick /dv_cshot /dvl_cell. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, dfrac_agree_persist.
  Qed.

  (* ===================================================================== *)
  (*  6.  THE THREE COLUMN MOVES                                            *)
  (* ===================================================================== *)

  (*  These are the operations' whole content, stated OFF the region: a
      caller that already holds [dv_lcol z] moves it with a plain [==∗].
      [InodeRegion] §L wraps each one in an [↑iregN] open and nothing else.
      Keeping them here keeps every fraction argument beside the ledger it
      is about -- and it is what makes the operations' proofs three lines
      of invariant plumbing each.                                          *)

  (* THE MINT.  Whoever holds the whole element and this inum's licence
     splits ¼ off into the column and keeps ¾ on the chain.  Total: the two
     lent arms are refuted by the licence the mint is itself holding. *)
  Lemma dv_col_mint (z : Z) (e : gmap fname Z) :
    dvl_dom z ->
    dv_lic z -∗ dv_hold z e -∗ dv_lcol z ==∗
      dv_lcol z ∗ (dv_half z (DfracOwn (3/4)) e ∗ dv_lentm z e) ∗ dv_pin z e.
  Proof.
    iIntros (Hdom) "Hlic Hw Hcol".
    rewrite {1}/dv_lcol.
    iDestruct "Hcol"
      as "[(%γc & %γv & Hsl & Hct & Hvw)
          |[(%γc & %γv & %e0 & _ & Hlic' & _)|(%γc & %γv & %e0 & _ & Hlic' & _)]]";
      [| iDestruct (dv_lic_excl with "Hlic Hlic'") as %[]
       | iDestruct (dv_lic_excl with "Hlic Hlic'") as %[]].
    (* the one live arm: NONE.  Arm both cells at [e], cut the slot three
       ways and the contents two, and deposit the licence. *)
    iMod (dvl_cell_set γc z ∅ e with "Hct") as "Hct".
    iMod (dvl_cell_set γv z ∅ e with "Hvw") as "Hvw".
    iEval (rewrite dvl_cell_cut) in "Hvw".
    iDestruct "Hvw" as "[Hvw1 Hvw2]".
    iEval (rewrite dvl_slot_cut) in "Hsl".
    iDestruct "Hsl" as "(Hsl14 & Hsl12 & Hslp)".
    rewrite dv_hold_split34. iDestruct "Hw" as "[Hw34 Hw14]".
    iModIntro. iSplitL "Hsl14 Hlic Hw14 Hct Hvw1".
    { rewrite /dv_lcol. iRight. iLeft. iExists γc, γv, e. iFrame. }
    iSplitL "Hw34 Hsl12".
    { iFrame "Hw34". rewrite /dv_lentm. iSplitR; [by iPureIntro |].
      iExists (γc, γv). iExact "Hsl12". }
    rewrite /dv_pin. iSplitR; [by iPureIntro |]. iExists γc, γv. iFrame.
  Qed.

  (* THE WRITER'S TOTAL MOVE.  Replaces [DirViewG.dv_set] at the mover
     sites.  It takes NO premise beyond the ride: the whole arm is [dv_set]
     verbatim (and never touches the column), and the ¾ arm gathers the
     escrowed ¼ and CANCELS on the way out, its two impossible arms refuted
     by the half-slot it is itself holding. *)
  Lemma dv_col_set (z : Z) (e e' : gmap fname Z) :
    dv_half z (DfracOwn (3/4)) e -∗ dv_lentm z e -∗ dv_lcol z ==∗
      dv_lcol z ∗ dv_hold z e'.
  Proof.
    iIntros "H34 Hm Hcol".
    iDestruct "Hm" as "[_ (%g & Hsl12)]".
    rewrite {1}/dv_lcol.
    iDestruct "Hcol"
      as "[(%γc & %γv & Hsl & _ & _)
          |[(%γc & %γv & %e0 & Hsl & Hlic & Hdv14 & Hct & Hvw)
           |(%γc & %γv & %e0 & Hsl & _ & _ & _)]]".
    - iDestruct (dvl_slot_over z 1 (1/2) _ _ dvl_q_over_1_12 with "Hsl Hsl12")
        as %[].
    - (* INTACT: gather, set, shoot, re-park CANCELLED *)
      iDestruct (dvl_slot_join34 with "Hsl Hsl12") as "[%Hg Hsl34]".
      iDestruct (dv_agree with "H34 Hdv14") as %<-.
      iDestruct (dv_join34 with "H34 Hdv14") as "Hw".
      iMod (dv_set z e e' with "Hw") as "Hw".
      iMod (dv_cshoot with "Hct") as "#Hcs".
      iModIntro. iFrame "Hw".
      rewrite /dv_lcol. iRight. iRight. iExists γc, γv, e.
      iFrame "Hsl34 Hlic Hvw". iExact "Hcs".
    - iDestruct (dvl_slot_over z (3/4) (1/2) _ _ dvl_q_over_34_12
                   with "Hsl Hsl12") as %[].
  Qed.

  (* THE CLIENT'S MOVE, fired INSIDE an [SpecNameiTr.nx_hop] fupd: the hop
     lends [dv_half z dqv ents] at whatever fraction its custody carries,
     and agreement against the ESCROWED ¼ is what forces [ents = e].  On the
     cancelled arm there is nothing to agree with and the client takes the
     receipt instead, spending the pin into it. *)
  Lemma dv_col_redeem (z : Z) (e ents : gmap fname Z) (dqv : dfrac) :
    dv_pin z e -∗ dv_half z dqv ents -∗ dv_lcol z ==∗
      dv_lcol z ∗ dv_half z dqv ents ∗
      ((⌜ents = e⌝ ∗ dv_pin z e) ∨ dv_cancelled z e).
  Proof.
    iIntros "Hpin Hdv Hcol".
    iDestruct "Hpin" as "[%Hdom (%γc & %γv & Hslp & Hvwp)]".
    rewrite {1}/dv_lcol.
    iDestruct "Hcol"
      as "[(%γc0 & %γv0 & Hsl & Hct & Hvw)
          |[(%γc0 & %γv0 & %e0 & Hsl & Hlic & Hdv14 & Hct & Hvw)
           |(%γc0 & %γv0 & %e0 & Hsl & Hlic & #Hcs & Hvw)]]".
    - iDestruct (dvl_slot_over z 1 (1/4) _ _ dvl_q_over_1_14 with "Hsl Hslp")
        as %[].
    - (* INTACT: the names agree, the witness forces [e0 = e], and the
         escrowed ¼ forces the lent value *)
      iDestruct (dvl_slot_agree with "Hsl Hslp") as %Heq.
      injection Heq as -> ->.
      iDestruct (dv_vwit_agree with "Hvw Hvwp") as %->.
      iDestruct (dv_agree with "Hdv14 Hdv") as %<-.
      iModIntro. iSplitL "Hsl Hlic Hdv14 Hct Hvw".
      { rewrite /dv_lcol. iRight. iLeft. iExists γc, γv, e. iFrame. }
      iFrame "Hdv". iLeft. iSplitR; [done |].
      rewrite /dv_pin. iSplitR; [done |]. iExists γc, γv. iFrame.
    - (* CANCELLED: the pin is spent into the persistent receipt *)
      iDestruct (dvl_slot_agree with "Hsl Hslp") as %Heq.
      injection Heq as -> ->.
      iDestruct (dv_vwit_agree with "Hvw Hvwp") as %->.
      rewrite /dvl_slot.
      iMod (ghost_map_elem_persist with "Hslp") as "#Hslp".
      iModIntro. iSplitL "Hsl Hlic Hvw".
      { rewrite /dv_lcol. iRight. iRight. iExists γc, γv, e.
        iFrame "Hsl Hlic Hvw". iExact "Hcs". }
      iFrame "Hdv". iRight. rewrite /dv_cancelled.
      iExists γc, γv. iSplitR; [iExact "Hslp" | iExact "Hcs"].
  Qed.

  (* ===================================================================== *)
  (*  7.  THE BOOT SHAPE                                                    *)
  (* ===================================================================== *)

  (* What [IcacheBoot.ireg_alloc] assembles per inum: the two un-armed cells
     (cut out of two whole [dview_boot_map]s at fresh gnames) and the whole
     slot element (inserted into the registry auth).  The licence is the
     other key's element, and goes to the caller. *)
  (* [DirViewG.dv_boot_split] at an ARBITRARY gname: the two cell families
     are minted by [IcacheBoot.ireg_alloc]'s own [own_alloc]s, at the same
     boot map the contents ghost uses. *)
  Lemma dvl_boot_split (γ : gname) (P : gset Z) :
    own γ (dview_boot_map P) ⊢ [∗ set] z ∈ P, dvl_cell γ z (DfracOwn 1) ∅.
  Proof.
    rewrite /dview_boot_map
            (gset_to_gmap_singletons (A := dfrac_agreeR (leibnizO (gmap fname Z)))).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /dvl_cell. iExact "H".
  Qed.

  Lemma dv_lcol_boot (z : Z) (γc γv : gname) :
    dvl_slot z (DfracOwn 1) (γc, γv) -∗
    dvl_cell γc z (DfracOwn 1) ∅ -∗ dvl_cell γv z (DfracOwn 1) ∅ -∗
    dv_lcol z.
  Proof.
    iIntros "Hsl Hct Hvw". rewrite /dv_lcol. iLeft.
    iExists γc, γv. iFrame.
  Qed.

  (* ===================================================================== *)
  (*  8.  THE fview COLUMN (N-5.2A, namei-pinned-lookup.md §13 D-52c)        *)
  (* ===================================================================== *)

  (*  EVERYTHING ABOVE, AT [DirViewG.fv_half].  The ledger, the three states,
      the ¾/¼ cut, the licence discipline and the three column moves are
      Phase B's verbatim -- only the cell algebra changes ([fviewUR] instead
      of [dviewUR], a byte list instead of an entry map) and the two registry
      key families ([fvl_k]/[fvl_l] instead of [dvl_k]/[dvl_l]).  D-52c ruled
      exactly this: a second column at more negative key families, not a
      generalisation of the first.

      The two columns are INDEPENDENT.  A directory's lend and a file's lend
      of the same inum could both stand (nothing forbids it and nothing needs
      it); a writer cancels whichever of the two its own ride tells it to,
      and [InodeRegion.dvw_set_rt] is just the two moves in sequence.       *)

  Definition fvl_slot (z : Z) (dq : dfrac) (g : gname * gname) : iProp Σ :=
    (fvl_k z ↪[icfg_reg]{dq} g)%I.

  Definition fv_lic (z : Z) : iProp Σ :=
    (∃ g : gname * gname, fvl_l z ↪[icfg_reg] g)%I.

  Definition fvl_cell (γ : gname) (z : Z) (dq : dfrac) (b : list (bv 8))
    : iProp Σ :=
    own γ ({[ z := to_dfrac_agree dq (b : leibnizO (list (bv 8))) ]} : fviewUR).

  Definition fv_ctick (γc : gname) (z : Z) (b : list (bv 8)) : iProp Σ :=
    fvl_cell γc z (DfracOwn 1) b.

  Definition fv_cshot (γc : gname) (z : Z) (b : list (bv 8)) : iProp Σ :=
    fvl_cell γc z DfracDiscarded b.

  Definition fv_vwit (γv : gname) (z : Z) (b : list (bv 8)) : iProp Σ :=
    fvl_cell γv z (DfracOwn (1/2)) b.

  (* ONE INUM'S fview LEND COLUMN -- what [InodeRegion.ireg_flends] parks,
     beside [dv_lcol]'s family and with the same three arms. *)
  Definition fv_lcol (z : Z) : iProp Σ :=
    ( (∃ γc γv : gname,
         fvl_slot z (DfracOwn 1) (γc, γv)
         ∗ fvl_cell γc z (DfracOwn 1) [] ∗ fvl_cell γv z (DfracOwn 1) [])
    ∨ (∃ (γc γv : gname) (b : list (bv 8)),
         fvl_slot z (DfracOwn (1/4)) (γc, γv) ∗ fv_lic z
         ∗ fv_half z (DfracOwn (1/4)) b ∗ fv_ctick γc z b ∗ fv_vwit γv z b)
    ∨ (∃ (γc γv : gname) (b : list (bv 8)),
         fvl_slot z (DfracOwn (3/4)) (γc, γv) ∗ fv_lic z
         ∗ fv_cshot γc z b ∗ fv_vwit γv z b) )%I.

  Definition fv_lentm (z : Z) (b : list (bv 8)) : iProp Σ :=
    (⌜dvl_dom z⌝ ∗ ∃ g : gname * gname, fvl_slot z (DfracOwn (1/2)) g)%I.

  Definition fv_ride (z : Z) (b : list (bv 8)) : iProp Σ :=
    (fv_hold z b ∨ (fv_half z (DfracOwn (3/4)) b ∗ fv_lentm z b))%I.

  Definition fv_pin (z : Z) (b : list (bv 8)) : iProp Σ :=
    (⌜dvl_dom z⌝ ∗ ∃ γc γv : gname,
       fvl_slot z (DfracOwn (1/4)) (γc, γv) ∗ fv_vwit γv z b)%I.

  Definition fv_pin_spent (z : Z) (b : list (bv 8)) : iProp Σ :=
    fv_pin z b.

  Definition fv_cancelled (z : Z) (b : list (bv 8)) : iProp Σ :=
    (∃ γc γv : gname,
       fvl_slot z DfracDiscarded (γc, γv) ∗ fv_cshot γc z b)%I.

  (* ------------------------------------------------------------------- *)
  (*  instances -- all-[own], for E1's reason verbatim                     *)
  (* ------------------------------------------------------------------- *)

  Global Instance fvl_slot_timeless z dq g : Timeless (fvl_slot z dq g).
  Proof. rewrite /fvl_slot. apply _. Qed.
  Global Instance fv_lic_timeless z : Timeless (fv_lic z).
  Proof. rewrite /fv_lic. apply _. Qed.
  Global Instance fvl_cell_timeless γ z dq b : Timeless (fvl_cell γ z dq b).
  Proof. apply _. Qed.
  Global Instance fv_ctick_timeless γc z b : Timeless (fv_ctick γc z b).
  Proof. apply _. Qed.
  Global Instance fv_cshot_timeless γc z b : Timeless (fv_cshot γc z b).
  Proof. apply _. Qed.
  Global Instance fv_vwit_timeless γv z b : Timeless (fv_vwit γv z b).
  Proof. apply _. Qed.

  Global Instance fv_cshot_persistent γc z b : Persistent (fv_cshot γc z b).
  Proof.
    rewrite /fv_cshot /fvl_cell /to_dfrac_agree.
    apply own_core_persistent, _.
  Qed.

  Global Instance fv_lcol_timeless z : Timeless (fv_lcol z).
  Proof. rewrite /fv_lcol. apply _. Qed.
  Global Instance fv_lentm_timeless z b : Timeless (fv_lentm z b).
  Proof. rewrite /fv_lentm. apply _. Qed.
  Global Instance fv_ride_timeless z b : Timeless (fv_ride z b).
  Proof. rewrite /fv_ride. apply _. Qed.
  Global Instance fv_pin_timeless z b : Timeless (fv_pin z b).
  Proof. rewrite /fv_pin. apply _. Qed.
  Global Instance fv_cancelled_timeless z b : Timeless (fv_cancelled z b).
  Proof. rewrite /fv_cancelled. apply _. Qed.

  Global Instance fv_cancelled_persistent z b : Persistent (fv_cancelled z b).
  Proof. rewrite /fv_cancelled. apply _. Qed.

  (* ---- the slot's fraction arithmetic -------------------------------- *)

  Lemma fvl_slot_split (z : Z) (p q : Qp) (g : gname * gname) :
    fvl_slot z (DfracOwn (p + q)) g ⊣⊢
      fvl_slot z (DfracOwn p) g ∗ fvl_slot z (DfracOwn q) g.
  Proof.
    rewrite /fvl_slot.
    apply (fractional (Φ := fun q => (fvl_k z ↪[icfg_reg]{#q} g)%I)).
  Qed.

  Lemma fvl_slot_join (z : Z) (p q : Qp) (g1 g2 : gname * gname) :
    fvl_slot z (DfracOwn p) g1 -∗ fvl_slot z (DfracOwn q) g2 -∗
    ⌜g1 = g2⌝ ∗ fvl_slot z (DfracOwn (p + q)) g1.
  Proof.
    rewrite /fvl_slot. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iSplitR; [done |]. subst g2.
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  Lemma fvl_slot_cut (z : Z) (g : gname * gname) :
    fvl_slot z (DfracOwn 1) g ⊣⊢
      fvl_slot z (DfracOwn (1/4)) g ∗ fvl_slot z (DfracOwn (1/2)) g
      ∗ fvl_slot z (DfracOwn (1/4)) g.
  Proof.
    rewrite -(fvl_slot_split z (1/2) (1/4) g).
    rewrite -(fvl_slot_split z (1/4) (1/2 + 1/4) g).
    by assert ((1/4 + (1/2 + 1/4))%Qp = 1%Qp) as -> by compute_done.
  Qed.

  Lemma fvl_slot_join34 (z : Z) (g1 g2 : gname * gname) :
    fvl_slot z (DfracOwn (1/4)) g1 -∗ fvl_slot z (DfracOwn (1/2)) g2 -∗
    ⌜g1 = g2⌝ ∗ fvl_slot z (DfracOwn (3/4)) g1.
  Proof.
    iIntros "H1 H2".
    iDestruct (fvl_slot_join with "H1 H2") as "[%Hg H]".
    iSplitR; [done |].
    by assert ((3/4)%Qp = (1/4 + 1/2)%Qp) as -> by compute_done.
  Qed.

  Lemma fvl_slot_agree (z : Z) (dq1 dq2 : dfrac) (g1 g2 : gname * gname) :
    fvl_slot z dq1 g1 -∗ fvl_slot z dq2 g2 -∗ ⌜g1 = g2⌝.
  Proof.
    rewrite /fvl_slot. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  Lemma fvl_slot_over (z : Z) (p q : Qp) (g1 g2 : gname * gname) :
    (1 < p + q)%Qp ->
    fvl_slot z (DfracOwn p) g1 -∗ fvl_slot z (DfracOwn q) g2 -∗ False.
  Proof.
    intros Hlt. rewrite /fvl_slot. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
    exact (proj1 (Qp.lt_nge _ _) Hlt Hv).
  Qed.

  Lemma fv_lic_excl (z : Z) : fv_lic z -∗ fv_lic z -∗ False.
  Proof.
    rewrite /fv_lic. iIntros "[%g1 H1] [%g2 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
    exact (Qp.not_add_le_l 1 1 Hv).
  Qed.

  (* ---- the contents' fraction arithmetic ----------------------------- *)

  Lemma fv_hold_split34 (z : Z) (b : list (bv 8)) :
    fv_hold z b ⊣⊢ fv_half z (DfracOwn (3/4)) b ∗ fv_half z (DfracOwn (1/4)) b.
  Proof. rewrite /fv_hold {1}dfrac_1_34. apply fv_split. Qed.

  Lemma fv_join34 (z : Z) (b : list (bv 8)) :
    fv_half z (DfracOwn (3/4)) b -∗ fv_half z (DfracOwn (1/4)) b -∗
    fv_hold z b.
  Proof. iIntros "H1 H2". rewrite fv_hold_split34. iFrame. Qed.

  Lemma fv_hold_half_excl (z : Z) (dq : dfrac) (b1 b2 : list (bv 8)) :
    fv_hold z b1 -∗ fv_half z dq b2 -∗ False.
  Proof.
    rewrite /fv_hold /fv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv; [| apply to_dfrac_agree_exclusive].
  Qed.

  Lemma fv_half34_excl (z : Z) (b1 b2 : list (bv 8)) :
    fv_half z (DfracOwn (3/4)) b1 -∗ fv_half z (DfracOwn (3/4)) b2 -∗ False.
  Proof.
    rewrite /fv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply dfrac_agree_op_valid_L in Hv as [Hd _].
    rewrite dfrac_op_own dfrac_valid_own in Hd.
    assert (Hq : (3/4 + 3/4)%Qp = (1 + 1/2)%Qp) by compute_done.
    rewrite Hq in Hd. by apply (Qp.not_add_le_l 1 (1/2)) in Hd.
  Qed.

  Lemma fv_ride_excl (z : Z) (b1 b2 : list (bv 8)) :
    fv_ride z b1 -∗ fv_ride z b2 -∗ False.
  Proof.
    rewrite /fv_ride. iIntros "[H1|[H1 _]] [H2|[H2 _]]".
    - iApply (fv_hold_excl with "H1 H2").
    - iApply (fv_hold_half_excl with "H1 H2").
    - iApply (fv_hold_half_excl with "H2 H1").
    - iApply (fv_half34_excl with "H1 H2").
  Qed.

  Lemma fv_ride_of_hold (z : Z) (b : list (bv 8)) :
    fv_hold z b -∗ fv_ride z b.
  Proof. iIntros "H". rewrite /fv_ride. by iLeft. Qed.

  Lemma fv_ride_size (z : Z) (dn1 dn2 : dinode) (data : nat -> list (bv 8)) :
    di_size dn1 = di_size dn2 ->
    fv_ride z (fv_of dn1 data) -∗ fv_ride z (fv_of dn2 data).
  Proof.
    intros Hs. rewrite (fv_of_size dn1 dn2 data Hs). iIntros "H". iExact "H".
  Qed.

  Lemma fv_lend_no_second_mint (z : Z) (b1 b2 : list (bv 8)) :
    fv_half z (DfracOwn (3/4)) b1 -∗ fv_lentm z b1 -∗ fv_hold z b2 -∗ False.
  Proof.
    iIntros "H34 _ Hw". iApply (fv_hold_half_excl with "Hw H34").
  Qed.

  (* ---- the cells' moves ---------------------------------------------- *)

  Lemma fvl_cell_agree (γ : gname) (z : Z) (dq1 dq2 : dfrac)
      (b1 b2 : list (bv 8)) :
    fvl_cell γ z dq1 b1 -∗ fvl_cell γ z dq2 b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite /fvl_cell. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. by apply dfrac_agree_op_valid_L in Hv as [_ ->].
  Qed.

  Lemma fv_vwit_agree (γv : gname) (z : Z) (b1 b2 : list (bv 8)) :
    fv_vwit γv z b1 -∗ fv_vwit γv z b2 -∗ ⌜b1 = b2⌝.
  Proof. rewrite /fv_vwit. apply fvl_cell_agree. Qed.

  Lemma fvl_cell_split (γ : gname) (z : Z) (dq1 dq2 : dfrac)
      (b : list (bv 8)) :
    fvl_cell γ z (dq1 ⋅ dq2) b ⊣⊢ fvl_cell γ z dq1 b ∗ fvl_cell γ z dq2 b.
  Proof.
    rewrite /fvl_cell -own_op singleton_op.
    by rewrite -dfrac_agree_op.
  Qed.

  Lemma fvl_cell_cut (γ : gname) (z : Z) (b : list (bv 8)) :
    fvl_cell γ z (DfracOwn 1) b ⊣⊢
      fvl_cell γ z (DfracOwn (1/2)) b ∗ fvl_cell γ z (DfracOwn (1/2)) b.
  Proof. rewrite -fvl_cell_split -dfrac_1_hh. done. Qed.

  Lemma fvl_cell_set (γ : gname) (z : Z) (b b' : list (bv 8)) :
    fvl_cell γ z (DfracOwn 1) b ==∗ fvl_cell γ z (DfracOwn 1) b'.
  Proof.
    rewrite /fvl_cell. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, cmra_update_exclusive.
    split; done.
  Qed.

  Lemma fv_cshoot (γc : gname) (z : Z) (b : list (bv 8)) :
    fv_ctick γc z b ==∗ fv_cshot γc z b.
  Proof.
    rewrite /fv_ctick /fv_cshot /fvl_cell. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, dfrac_agree_persist.
  Qed.

  (* ---- the three column moves ---------------------------------------- *)

  Lemma fv_col_mint (z : Z) (b : list (bv 8)) :
    dvl_dom z ->
    fv_lic z -∗ fv_hold z b -∗ fv_lcol z ==∗
      fv_lcol z ∗ (fv_half z (DfracOwn (3/4)) b ∗ fv_lentm z b) ∗ fv_pin z b.
  Proof.
    iIntros (Hdom) "Hlic Hw Hcol".
    rewrite {1}/fv_lcol.
    iDestruct "Hcol"
      as "[(%γc & %γv & Hsl & Hct & Hvw)
          |[(%γc & %γv & %b0 & _ & Hlic' & _)|(%γc & %γv & %b0 & _ & Hlic' & _)]]";
      [| iDestruct (fv_lic_excl with "Hlic Hlic'") as %[]
       | iDestruct (fv_lic_excl with "Hlic Hlic'") as %[]].
    iMod (fvl_cell_set γc z [] b with "Hct") as "Hct".
    iMod (fvl_cell_set γv z [] b with "Hvw") as "Hvw".
    iEval (rewrite fvl_cell_cut) in "Hvw".
    iDestruct "Hvw" as "[Hvw1 Hvw2]".
    iEval (rewrite fvl_slot_cut) in "Hsl".
    iDestruct "Hsl" as "(Hsl14 & Hsl12 & Hslp)".
    rewrite fv_hold_split34. iDestruct "Hw" as "[Hw34 Hw14]".
    iModIntro. iSplitL "Hsl14 Hlic Hw14 Hct Hvw1".
    { rewrite /fv_lcol. iRight. iLeft. iExists γc, γv, b. iFrame. }
    iSplitL "Hw34 Hsl12".
    { iFrame "Hw34". rewrite /fv_lentm. iSplitR; [by iPureIntro |].
      iExists (γc, γv). iExact "Hsl12". }
    rewrite /fv_pin. iSplitR; [by iPureIntro |]. iExists γc, γv. iFrame.
  Qed.

  Lemma fv_col_set (z : Z) (b b' : list (bv 8)) :
    fv_half z (DfracOwn (3/4)) b -∗ fv_lentm z b -∗ fv_lcol z ==∗
      fv_lcol z ∗ fv_hold z b'.
  Proof.
    iIntros "H34 Hm Hcol".
    iDestruct "Hm" as "[_ (%g & Hsl12)]".
    rewrite {1}/fv_lcol.
    iDestruct "Hcol"
      as "[(%γc & %γv & Hsl & _ & _)
          |[(%γc & %γv & %b0 & Hsl & Hlic & Hfv14 & Hct & Hvw)
           |(%γc & %γv & %b0 & Hsl & _ & _ & _)]]".
    - iDestruct (fvl_slot_over z 1 (1/2) _ _ dvl_q_over_1_12 with "Hsl Hsl12")
        as %[].
    - iDestruct (fvl_slot_join34 with "Hsl Hsl12") as "[%Hg Hsl34]".
      iDestruct (fv_agree with "H34 Hfv14") as %<-.
      iDestruct (fv_join34 with "H34 Hfv14") as "Hw".
      iMod (fv_set z b b' with "Hw") as "Hw".
      iMod (fv_cshoot with "Hct") as "#Hcs".
      iModIntro. iFrame "Hw".
      rewrite /fv_lcol. iRight. iRight. iExists γc, γv, b.
      iFrame "Hsl34 Hlic Hvw". iExact "Hcs".
    - iDestruct (fvl_slot_over z (3/4) (1/2) _ _ dvl_q_over_34_12
                   with "Hsl Hsl12") as %[].
  Qed.

  Lemma fv_col_redeem (z : Z) (b bs : list (bv 8)) (dqv : dfrac) :
    fv_pin z b -∗ fv_half z dqv bs -∗ fv_lcol z ==∗
      fv_lcol z ∗ fv_half z dqv bs ∗
      ((⌜bs = b⌝ ∗ fv_pin z b) ∨ fv_cancelled z b).
  Proof.
    iIntros "Hpin Hfv Hcol".
    iDestruct "Hpin" as "[%Hdom (%γc & %γv & Hslp & Hvwp)]".
    rewrite {1}/fv_lcol.
    iDestruct "Hcol"
      as "[(%γc0 & %γv0 & Hsl & Hct & Hvw)
          |[(%γc0 & %γv0 & %b0 & Hsl & Hlic & Hfv14 & Hct & Hvw)
           |(%γc0 & %γv0 & %b0 & Hsl & Hlic & #Hcs & Hvw)]]".
    - iDestruct (fvl_slot_over z 1 (1/4) _ _ dvl_q_over_1_14 with "Hsl Hslp")
        as %[].
    - iDestruct (fvl_slot_agree with "Hsl Hslp") as %Heq.
      injection Heq as -> ->.
      iDestruct (fv_vwit_agree with "Hvw Hvwp") as %->.
      iDestruct (fv_agree with "Hfv14 Hfv") as %<-.
      iModIntro. iSplitL "Hsl Hlic Hfv14 Hct Hvw".
      { rewrite /fv_lcol. iRight. iLeft. iExists γc, γv, b. iFrame. }
      iFrame "Hfv". iLeft. iSplitR; [done |].
      rewrite /fv_pin. iSplitR; [done |]. iExists γc, γv. iFrame.
    - iDestruct (fvl_slot_agree with "Hsl Hslp") as %Heq.
      injection Heq as -> ->.
      iDestruct (fv_vwit_agree with "Hvw Hvwp") as %->.
      rewrite /fvl_slot.
      iMod (ghost_map_elem_persist with "Hslp") as "#Hslp".
      iModIntro. iSplitL "Hsl Hlic Hvw".
      { rewrite /fv_lcol. iRight. iRight. iExists γc, γv, b.
        iFrame "Hsl Hlic Hvw". iExact "Hcs". }
      iFrame "Hfv". iRight. rewrite /fv_cancelled.
      iExists γc, γv. iSplitR; [iExact "Hslp" | iExact "Hcs"].
  Qed.

  (* ---- the boot shape ------------------------------------------------- *)

  Lemma fvl_boot_split (γ : gname) (P : gset Z) :
    own γ (fview_boot_map P) ⊢ [∗ set] z ∈ P, fvl_cell γ z (DfracOwn 1) [].
  Proof.
    rewrite /fview_boot_map
            (gset_to_gmap_singletons (A := dfrac_agreeR (leibnizO (list (bv 8))))).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /fvl_cell. iExact "H".
  Qed.

  Lemma fv_lcol_boot (z : Z) (γc γv : gname) :
    fvl_slot z (DfracOwn 1) (γc, γv) -∗
    fvl_cell γc z (DfracOwn 1) [] -∗ fvl_cell γv z (DfracOwn 1) [] -∗
    fv_lcol z.
  Proof.
    iIntros "Hsl Hct Hvw". rewrite /fv_lcol. iLeft.
    iExists γc, γv. iFrame.
  Qed.

End DirViewLendDefs.
