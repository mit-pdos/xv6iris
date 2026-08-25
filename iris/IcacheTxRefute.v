(* IcacheTxRefute.v -- THE WALL LANE B' HIT AT THE ESCROW'S "OUT FOR
   WRITING" ARM, machine-checked.  Documentation, like [FsDurRefute.v],
   [FsDurDefer.v] and [FsDurTrunc.v]; nothing consumes it.

   ---- WHAT THE DESIGN ASKS FOR ---------------------------------------

   durable-fs-plan.md section 3 ([ilock]) wants a transactional [ilock] to
   PARK a share of the transaction's token in the checked-out entry's
   escrow, so that [end_op] -- which consumes the WHOLE token -- cannot run
   while any inode of the transaction is write-locked, and [iunlock] to hand
   that share back.  A transaction that write-locks k inodes (create holds
   its parent AND its fresh child) parks k shares and recovers them one at a
   time.

   ---- WHY IT DOES NOT CLOSE AS STATED --------------------------------

   The token is [LogInv.log_tx γ = ∃ t : nat, t ↪[ln_tx γ] ()] (LogInv.v:502)
   -- lane A closed the id EXISTENTIALLY on purpose, so that a retiring
   transaction never has to name what it retires (the ledger tie is
   CARDINALITY, [LogInv.log_res]'s [size T = size om]).  A share of it is
   therefore [∃ t, t ↪[ln_tx γ]{#q} ()], and an escrow arm holding one binds
   its own [t].  At [iunlock] the holder has its residue at ITS id and the
   arm hands back a share at the ARM's id, and NOTHING relates the two: two
   ghost-map elements at DIFFERENT keys are perfectly consistent, so
   [ghost_map_elem_combine] does not apply and the holder can never rebuild
   the whole element [end_op] needs.

   [tx_two_halves_no_whole] below is that fact positively: from an empty
   authority one can reach a state holding TWO transactions, each with a
   half out -- which satisfies [(∃ t, t ↪{#(1/2)} ()) ∗ (∃ t, t ↪{#(1/2)} ())]
   -- and in that state NO whole element exists at any id at all.  So the
   pair of existentially-keyed halves is strictly weaker than one whole
   token, and no lemma can turn one into the other.

   This is the SAME trap lane A recorded at the locked registry ("an arm
   keyed by inum must prove its key free ... and one transaction holding two
   inodes needs two halves of one token that then cannot come back whole"),
   which is why that registry is keyed by TRANSACTION and parks the WHOLE
   token.  The escrow cannot copy that fix: it is keyed by cache SLOT, and
   create holds two slots inside one transaction, so one whole token cannot
   sit in both arms.

   ---- THE CHEAPEST MECHANISM THAT DOES CLOSE IT ----------------------

   Pin the parked pair to the holder with a ghost the two already share.
   The escrow ALREADY has one: [IcacheEscrow.ic_deposit cn k d] is a
   [ghost_var] over [Xv6Cameras.ic_dep] whose other half [SpecIlock] hands
   the holder and [SpecIunlock] consumes -- it is what already pins the
   checkout's fraction, device and inum with no cell agreement at all.
   Widening [ic_dep] with a write-checkout constructor carrying the id and
   the share, say

     DepTx (s : Qp) (dev inum : mword 32) (g : gname) (t : nat) (q : Qp)

   makes the arm's [t] and [q] the holder's own, and [iunlock] recovers
   EXACTLY the share it parked.  The cost is the ten [match d with]
   sites ([ic_dep_own], [ic_dep_half], [ic_out_frz], [IcacheRef.ic_dep_gname]
   and their timeless/accessor twins) plus the writers' own checkout/park.
   The alternative -- exposing [t] in [log_op]'s ABI -- is the closure lane A
   deliberately built and should not be undone for this.  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

Section TxRefute.
  Context `{!ghost_mapG Σ nat unit}.

  (* TWO OPEN TRANSACTIONS, EACH WITH A HALF PARKED, AND NO WHOLE TOKEN.

     The two halves satisfy the "share of [log_tx]" shape
     [∃ t, t ↪{#(1/2)} ()] twice over, and the final wand says that in this
     state no [log_tx] (a WHOLE element, at any id) can be produced -- so
     [end_op] is correctly blocked, and equally no [iunlock] can ever give
     one of the two holders back a rejoinable share, because neither can
     learn WHICH id the escrow parked. *)
  Lemma tx_two_halves_no_whole (γ : gname) (t1 t2 : nat) :
    t1 <> t2 ->
    ghost_map_auth γ 1 (∅ : gmap nat unit) ==∗
      ∃ T : gmap nat unit,
        ghost_map_auth γ 1 T ∗
        t1 ↪[γ]{#(1/2)} () ∗ t2 ↪[γ]{#(1/2)} () ∗
        (∀ t : nat,
           t1 ↪[γ]{#(1/2)} () -∗ t2 ↪[γ]{#(1/2)} () -∗
           ghost_map_auth γ 1 T -∗ t ↪[γ] () -∗ False).
  Proof.
    intros Hne. iIntros "Ha".
    iMod (ghost_map_insert t1 () (lookup_empty t1) with "Ha") as "[Ha H1]".
    assert (H2 : (<[t1 := ()]> ∅ : gmap nat unit) !! t2 = None).
    { rewrite lookup_insert_ne; [apply lookup_empty | done]. }
    iMod (ghost_map_insert t2 () H2 with "Ha") as "[Ha H2]".
    iDestruct "H1" as "[H1a H1b]".
    iDestruct "H2" as "[H2a H2b]".
    iModIntro. iExists _. iFrame "Ha H1a H2a".
    iIntros (t) "H1a H2a Ha Hw".
    destruct (decide (t = t1)) as [-> | Hnt1].
    { iDestruct (ghost_map_elem_valid_2 with "Hw H1a") as %[Hv _].
      iPureIntro. exact (exclusive_l (DfracOwn 1) (DfracOwn (1/2)) Hv). }
    destruct (decide (t = t2)) as [-> | Hnt2].
    { iDestruct (ghost_map_elem_valid_2 with "Hw H2a") as %[Hv _].
      iPureIntro. exact (exclusive_l (DfracOwn 1) (DfracOwn (1/2)) Hv). }
    (* an id nobody opened: the authority has no row for it *)
    iDestruct (ghost_map_lookup with "Ha Hw") as %Ht.
    rewrite lookup_insert_ne in Ht; [| congruence].
    rewrite lookup_insert_ne in Ht; [| congruence].
    rewrite lookup_empty in Ht. discriminate Ht.
  Qed.

  (* ...and the shape the two halves DO satisfy, so the statement above is
     about the resource the design actually proposes to park. *)
  Lemma tx_halves_are_shares (γ : gname) (t1 t2 : nat) :
    t1 ↪[γ]{#(1/2)} () -∗ t2 ↪[γ]{#(1/2)} () -∗
    (∃ t : nat, t ↪[γ]{#(1/2)} ()) ∗ (∃ t : nat, t ↪[γ]{#(1/2)} ()).
  Proof. iIntros "H1 H2". iSplitL "H1"; [iExists t1 | iExists t2]; done. Qed.

End TxRefute.
