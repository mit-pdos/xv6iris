(* ===================================================================== *)
(*  DirViewLend.v -- M1, THE CANCELLABLE LEND [dv_lend / dv_pin]          *)
(*  (the pinned namei corollary that consumes it: DirViewPin.v)           *)
(*  (claude-notes/projects/namei-pinned-lookup.md §11.2, ruled D-N4a;     *)
(*   stage N-4, PHASE A: the kit, on a NEW leaf, no existing file moved)  *)
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

    THE FOUR PIECES, and the one discipline that makes them total:

      dv_ride z e  =  dv_hold z e                       the WHOLE arm
                    ∨ dv_half z (3/4) e ∗ dv_lentm z e  the LENT arm

      dv_lentm     =  the ¾-arm's marker: the lend invariant (persistent,
                      so a writer finds the lend WITHOUT a registry and
                      WITHOUT a new premise) plus ONE exclusive re-park
                      token [dv_tok γm].

      lend body    =  (dv_half z (1/4) e ∗ ctick)   INTACT
                    ∨ (cshot ∗ dv_tok γm)           CANCELLED

    THE mtok DISCIPLINE.  The re-park token is minted ONCE and lives on the
    ¾ arm while the lend is INTACT; the writer DEPOSITS it into the body at
    the same instant it shoots [cshot].  So "the ¾ arm meets a CANCELLED
    body" would exhibit two copies of one [Excl ()] -- [dv_set_rt]'s only
    impossible case is refuted by [dv_tok_excl] and nothing else.  This is
    what buys totality: the writer never has to prove that its directory is
    unlent, and never has to look one up.

    RETIREMENT IS LAZY (charter).  An INTACT redeem puts the ¼ straight
    back; the lend is retired only by the next writer's cancel.  There is
    deliberately no retire operation: a retire would need the ¾ arm in hand,
    which the redeeming client does not have.

    ---------------------------------------------------------------------
    THE RA CHOICES, AND WHY NO FUNCTOR ROW IS NEEDED (finding, Phase A).

    Every ghost cell here rides an inG the landed [Xv6Cameras.icacheG]
    already carries, at FRESH DYNAMIC gnames allocated at the mint:

      * [dv_tok] (mtok, rtick) = [own γ (Excl ())] at [icache_tickG],
        the escrow's own redemption-ticket RA.
      * [ctick]/[cshot] = a SECOND [dviewUR] cell at a fresh gname
        ([dvl_cell]).  This is the house one-shot ([IcacheRef.ity_pending]
        / [ity_shot]) at a different RA, and the swap is deliberate:
        [ityR]'s agreement payload is [bv 16], which cannot NAME the lend,
        whereas a [dviewUR] cell at key [z] and value [e] gives a
        cancellation receipt that is persistent, Timeless, AND says which
        directory at which contents was cancelled.  PENDING is the whole
        element ([DfracOwn 1], exclusive); SHOT is [DfracDiscarded]
        (persistent), and [dfrac_agree_persist] is the one-line shoot.
        [ctick] and [cshot] collide, so the two arms are exclusive without
        any extra token.

    NO new [inG], NO [icfg] field, NO functor row.  Every gname is dynamic.

    ---------------------------------------------------------------------
    [dv_ride] IS NOT Timeless, AND THAT IS FORCED (finding, Phase A -- the
    headline for Phase B's charter).

    The charter asked for a Timeless ride.  It is not achievable with the
    lend hosted in an invariant of its own, and the obstruction is not an
    accident of this file's spelling:

      (1) The writer must be able to reassemble [DfracOwn 1] at key [z]
          with no premise and no cooperation.  [dviewUR] is a landed
          [gmap Z (dfrac_agree _)]: neither [dv_set]'s exclusive update
          nor [dfrac_agree_update_2] can move the value while ANY frame
          fraction stands.  So the client's ¼ must be reachable by the
          writer, i.e. it must sit in a SHARED region.
      (2) A shared region a writer may open unpremised is an [inv], and the
          only place the ride can put its handle is the ride itself.
      (3) [inv N P] is Persistent but never Timeless (iris/base_logic/lib/
          invariants.v has no such instance, and cannot: its [ownI] carries
          an [agree (later (iProp))], which is not discrete).

    Generally: ANY ride arm that grants an unpremised fupd capability is
    non-Timeless.  This matters because the custody positions Phase B would
    swap ([IcacheEscrow.ipool_alloc], [ipool_shape_np]'s [imark] arm,
    [ic_loaded]) are all Timeless-by-instance, and [ic_loaded_timeless] is
    what [ic_escrow_body_timeless] -- hence every [iInv "Hesc" as ">"] in
    the tree -- is built out of.  IcacheEscrow.v:529-538 records the same
    trade for [escA_inv] and resolves it by RELOCATION, not by a stand-in.

    The two exits, for the coordinator to rule on (Phase A does not choose):

      (E1) HOST THE LEND IN THE ESCROW THAT IS ALREADY OPEN.  Put the ¼ and
           the two tokens in the escrow's own per-inum body, beside the
           conjunct the ride would have replaced.  Both parties already
           hold [ic_escrows] (the writer opens it to reach the payload; the
           pinned client holds it as a premise of [wp_namei_tr_body], and
           the hop fires between instructions with nothing open), so the
           lend needs NO new invariant and NO new premise -- and every
           resource it adds is an [own], so every Timeless instance
           survives.  Cost: IcacheEscrow's arms grow a disjunct, i.e. real
           surgery on a landed file.
      (E2) KEEP THIS FILE'S SHAPE and pay for it: [ic_loaded] and the pool
           shapes lose Timeless, or the dv conjunct is relocated off the
           [">"]-opened path.

    Everything below is written so that (E2) is a no-op and (E1) is a
    re-spelling of [dv_lend]/[dv_lentm] alone: the four operations'
    statements, the redeem's disjunction and the pinned functor of
    [DirViewPin.v] do not mention where the body lives.                    *)

From Stdlib Require Import ZArith.
From stdpp Require Import gmap list namespaces bitvector.definitions.
From iris.algebra Require Import gmap dfrac excl updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own invariants.
Require Import SailStdpp.Values.
Require Import DinodeEnc.   (* [dinode] -- [DirViewG]'s own cone            *)
Require Import DirView.     (* [dir_nrec]                                   *)
Require Import FsTree.      (* [fname], [dir_view]                          *)
Require Import IcacheRef.   (* [icfg], [icfg_dview], [dviewUR]              *)
Require Import DirViewG.    (* [dv_half], [dv_hold], [dv_set], [dv_agree]   *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE CELLS                                                         *)
(* ===================================================================== *)

(*  ALTITUDE.  This file sits DIRECTLY ABOVE [DirViewG] -- [icacheG] for the
    cells, [invGS] for the lend, nothing else -- and that is load-bearing
    rather than tidy: every consumer of [dv_set_rt] is a byte-write mover
    (ProofCreate, ProofFilewrite, ProofSysOpen, ProofSysLink) or an escrow
    arm (IcacheEscrow, EscrowInode, IcacheBoot, FsCfgBoot), all of which are
    BELOW the namei cone.  The pinned corollary, which is not, lives in the
    companion leaf [DirViewPin.v].                                          *)

Section DirViewLendDefs.
  Context `{!icacheG Σ, !invGS Σ}.
  Context `{ICFG : icfg}.

  (* ONE namespace for every lend.  Per-lend indexing ([lendN .@ z]) would
     buy nothing here: no operation ever opens two lends at once -- the
     writer opens the one on its own directory, the client one hop at a
     time -- and a flat namespace keeps every mask side-condition a
     [solve_ndisj] one-liner. *)
  Definition lendN : namespace := nroot .@ "dvlend".

  (* A [dviewUR] cell at a FRESH gname: the one-shot's carrier.  Same RA as
     [DirViewG.dv_half], different (dynamic) name -- see the header. *)
  Definition dvl_cell (γ : gname) (z : Z) (dq : dfrac) (e : gmap fname Z)
    : iProp Σ :=
    own γ ({[ z := to_dfrac_agree dq (e : leibnizO (gmap fname Z)) ]} : dviewUR).

  (* PENDING: the lend has not been cancelled.  Exclusive. *)
  Definition dv_ctick (γc : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    dvl_cell γc z (DfracOwn 1) e.

  (* SHOT: the lend was cancelled by a writer.  Persistent, Timeless, and
     it NAMES the directory and the contents that were pinned. *)
  Definition dv_cshot (γc : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    dvl_cell γc z DfracDiscarded e.

  (* the plain exclusive token, at [icache_tickG]: mtok and rtick both *)
  Definition dv_tok (γ : gname) : iProp Σ := own γ (Excl () : exclR unitO).

  Definition dv_lend_body (γc γm : gname) (z : Z) (e : gmap fname Z)
    : iProp Σ :=
    ( (dv_half z (DfracOwn (1/4)) e ∗ dv_ctick γc z e)
    ∨ (dv_cshot γc z e ∗ dv_tok γm) )%I.

  Definition dv_lend (γc γm : gname) (z : Z) (e : gmap fname Z) : iProp Σ :=
    inv lendN (dv_lend_body γc γm z e).

  (* THE ¾ ARM'S MARKER.  Carries the lend (persistent: the writer finds it
     without a registry) and the re-park token (exclusive: the writer's
     deposit, and the refuter of the impossible arm). *)
  Definition dv_lentm (z : Z) (e : gmap fname Z) : iProp Σ :=
    (∃ γc γm, dv_lend γc γm z e ∗ dv_tok γm)%I.

  (* THE CUSTODY-CHAIN SHAPE (Phase B swaps this in for [dv_hold]). *)
  Definition dv_ride (z : Z) (e : gmap fname Z) : iProp Σ :=
    (dv_hold z e ∨ (dv_half z (DfracOwn (3/4)) e ∗ dv_lentm z e))%I.

  (* THE CLIENT PACKAGE: knowledge of the lend + the exclusive redemption
     ticket.  One redemption per pin; the ticket is spent on BOTH arms. *)
  Definition dv_pin (z : Z) (e : gmap fname Z) : iProp Σ :=
    (∃ γc γm γr, dv_lend γc γm z e ∗ dv_tok γr)%I.

  (* what a spent-but-intact pin leaves behind: the lend, minus the ticket *)
  Definition dv_pin_spent (z : Z) (e : gmap fname Z) : iProp Σ :=
    (∃ γc γm, dv_lend γc γm z e)%I.

  (* THE RECEIPT: "the lend taken on directory [z] at contents [e] was
     cancelled", i.e. some writer moved [z]'s contents since the pin. *)
  Definition dv_cancelled (z : Z) (e : gmap fname Z) : iProp Σ :=
    (∃ γc γm, dv_lend γc γm z e ∗ dv_cshot γc z e)%I.

  (* ------------------------------------------------------------------- *)
  (*  instances                                                           *)
  (* ------------------------------------------------------------------- *)

  Global Instance dvl_cell_timeless γ z dq e : Timeless (dvl_cell γ z dq e).
  Proof. apply _. Qed.
  Global Instance dv_ctick_timeless γc z e : Timeless (dv_ctick γc z e).
  Proof. apply _. Qed.
  Global Instance dv_cshot_timeless γc z e : Timeless (dv_cshot γc z e).
  Proof. apply _. Qed.
  Global Instance dv_tok_timeless γ : Timeless (dv_tok γ).
  Proof. apply _. Qed.

  Global Instance dv_cshot_persistent γc z e : Persistent (dv_cshot γc z e).
  Proof.
    rewrite /dv_cshot /dvl_cell /to_dfrac_agree.
    apply own_core_persistent, _.
  Qed.

  Global Instance dv_lend_persistent γc γm z e : Persistent (dv_lend γc γm z e).
  Proof. rewrite /dv_lend. apply _. Qed.

  (* THE BODY IS Timeless -- which is what lets every open below strip the
     ▷ with a plain [">"] pattern.  (The HANDLE is not; see the header.) *)
  Global Instance dv_lend_body_timeless γc γm z e :
    Timeless (dv_lend_body γc γm z e).
  Proof. rewrite /dv_lend_body. apply _. Qed.

  Global Instance dv_pin_spent_persistent z e : Persistent (dv_pin_spent z e).
  Proof. rewrite /dv_pin_spent. apply _. Qed.
  Global Instance dv_cancelled_persistent z e : Persistent (dv_cancelled z e).
  Proof. rewrite /dv_cancelled. apply _. Qed.

  (* the body's two arms, as an entailment the proofmode can destruct
     without unfolding anything in the goal *)
  Lemma dv_lend_body_cases (γc γm : gname) (z : Z) (e : gmap fname Z) :
    dv_lend_body γc γm z e ⊢
      (dv_half z (DfracOwn (1/4)) e ∗ dv_ctick γc z e)
      ∨ (dv_cshot γc z e ∗ dv_tok γm).
  Proof. by rewrite /dv_lend_body. Qed.

  (* ===================================================================== *)
  (*  2.  THE FRACTION ARITHMETIC AND THE EXCLUSIVITY LAWS                  *)
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
    assert ((3/4 + 3/4)%Qp = (1 + 1/2)%Qp) as Hq by compute_done.
    rewrite Hq in Hd. by apply (Qp.not_add_le_l 1 (1/2)) in Hd.
  Qed.

  Lemma dv_tok_excl (γ : gname) : dv_tok γ -∗ dv_tok γ -∗ False.
  Proof.
    rewrite /dv_tok. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %[].
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

  (* NO SECOND MINT ON ONE DIRECTORY, and this is the whole discipline: a
     mint demands [dv_hold], and a directory that already rides a lend has
     only ¾ on the chain, so no [dv_hold] for it can exist anywhere.  The
     ¾ constraint does the work; there is no registry to consult. *)
  Lemma dv_lend_no_second_mint (z : Z) (e1 e2 : gmap fname Z) :
    dv_half z (DfracOwn (3/4)) e1 -∗ dv_lentm z e1 -∗ dv_hold z e2 -∗ False.
  Proof.
    iIntros "H34 _ Hw". iApply (dv_hold_half_excl with "Hw H34").
  Qed.

  (* ===================================================================== *)
  (*  3.  THE ONE-SHOT'S SHOOT                                              *)
  (* ===================================================================== *)

  Lemma dv_cshoot (γc : gname) (z : Z) (e : gmap fname Z) :
    dv_ctick γc z e ==∗ dv_cshot γc z e.
  Proof.
    rewrite /dv_ctick /dv_cshot /dvl_cell. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, dfrac_agree_persist.
  Qed.

  Lemma dv_ctick_cshot_excl (γc : gname) (z : Z) (e1 e2 : gmap fname Z) :
    dv_ctick γc z e1 -∗ dv_cshot γc z e2 -∗ False.
  Proof.
    rewrite /dv_ctick /dv_cshot /dvl_cell. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    by apply dfrac_agree_op_valid_L in Hv as [Hd _].
  Qed.

  (* ===================================================================== *)
  (*  4.  THE THREE OPERATIONS                                              *)
  (* ===================================================================== *)

  (* MINT.  Whoever holds the whole element splits ¼ off into a fresh lend
     and keeps ¾ on the chain.  The client walks away with the pin; the
     chain walks away with the ¾ arm.  All three gnames are dynamic. *)
  Lemma dv_lend_mint (E : coPset) (z : Z) (e : gmap fname Z) :
    ↑lendN ⊆ E ->
    dv_hold z e ={E}=∗
      (dv_half z (DfracOwn (3/4)) e ∗ dv_lentm z e) ∗ dv_pin z e.
  Proof.
    iIntros (HE) "H". rewrite dv_hold_split34.
    iDestruct "H" as "[H34 H14]".
    iMod (own_alloc ({[ z := to_dfrac_agree (DfracOwn 1)
                              (e : leibnizO (gmap fname Z)) ]} : dviewUR))
      as (γc) "Hct".
    { by rewrite singleton_valid. }
    iMod (own_alloc (Excl () : exclR unitO)) as (γm) "Hm"; [done|].
    iMod (own_alloc (Excl () : exclR unitO)) as (γr) "Hr"; [done|].
    iMod (inv_alloc lendN E (dv_lend_body γc γm z e) with "[H14 Hct]")
      as "#Hinv".
    { iNext. rewrite /dv_lend_body. iLeft. iFrame. }
    iModIntro. iFrame "H34".
    iSplitL "Hm".
    - rewrite /dv_lentm. iExists γc, γm. by iFrame "Hinv Hm".
    - rewrite /dv_pin. iExists γc, γm, γr. by iFrame "Hinv Hr".
  Qed.

  (* THE WRITER'S TOTAL MOVER.  Replaces [DirViewG.dv_set] at the W3 sites.
     It takes NO premise beyond the ride and it is total: the whole arm is
     [dv_set] verbatim, the ¾ arm gathers the escrowed ¼ and CANCELS on the
     way out, and the one arm that would be a problem -- a ¾ ride meeting an
     already-CANCELLED body -- is refuted by the mtok it is itself holding.
     The mask is the only cost, and it is [↑lendN] alone. *)
  Lemma dv_set_rt (E : coPset) (z : Z) (e e' : gmap fname Z) :
    ↑lendN ⊆ E ->
    dv_ride z e ={E}=∗ dv_ride z e'.
  Proof.
    iIntros (HE) "H". rewrite {1}/dv_ride.
    iDestruct "H" as "[Hw|[H34 Hm]]".
    - iMod (dv_set with "Hw") as "Hw". iModIntro. by iApply dv_ride_of_hold.
    - rewrite /dv_lentm. iDestruct "Hm" as (γc γm) "[#Hinv Hm]".
      iInv "Hinv" as ">Hbody" "Hclose".
      iDestruct (dv_lend_body_cases with "Hbody") as "[[H14 Hct]|[#Hcs Hm']]".
      + iDestruct (dv_join34 with "H34 H14") as "Hw".
        iMod (dv_set with "Hw") as "Hw".
        iMod (dv_cshoot with "Hct") as "#Hcs".
        iMod ("Hclose" with "[Hm]") as "_".
        { iNext. rewrite /dv_lend_body. iRight. by iFrame "Hcs Hm". }
        iModIntro. by iApply dv_ride_of_hold.
      + iDestruct (dv_tok_excl with "Hm Hm'") as %[].
  Qed.

  (* THE CLIENT'S MOVE, fired INSIDE an [SpecNameiTr.nx_hop] fupd: the hop
     lends [dv_half z dqv ents] at whatever fraction its custody carries,
     and agreement against the ESCROWED ¼ is what forces [ents = e].  On the
     cancelled arm there is nothing to agree with and the client takes the
     receipt instead.  The ticket is spent either way -- one redemption per
     pin -- and the ¼ STAYS LENT (lazy retirement, charter). *)
  Lemma dv_pin_redeem (E : coPset) (z : Z) (e : gmap fname Z)
      (dqv : dfrac) (ents : gmap fname Z) :
    ↑lendN ⊆ E ->
    dv_pin z e -∗ dv_half z dqv ents ={E}=∗
      dv_half z dqv ents ∗
      ((⌜ents = e⌝ ∗ dv_pin_spent z e) ∨ dv_cancelled z e).
  Proof.
    iIntros (HE) "Hpin Hdv". rewrite /dv_pin.
    iDestruct "Hpin" as (γc γm γr) "[#Hinv Hr]".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct (dv_lend_body_cases with "Hbody") as "[[H14 Hct]|[#Hcs Hm]]".
    - iDestruct (dv_agree with "H14 Hdv") as %Heq.
      iMod ("Hclose" with "[H14 Hct]") as "_".
      { iNext. rewrite /dv_lend_body. iLeft. iFrame. }
      iModIntro. iFrame "Hdv". iLeft. iSplit.
      { iPureIntro. by rewrite Heq. }
      rewrite /dv_pin_spent. iExists γc, γm. by iFrame "Hinv".
    - iMod ("Hclose" with "[Hm]") as "_".
      { iNext. rewrite /dv_lend_body. iRight. by iFrame "Hcs Hm". }
      iModIntro. iFrame "Hdv". iRight.
      rewrite /dv_cancelled. iExists γc, γm. by iFrame "Hinv Hcs".
  Qed.

End DirViewLendDefs.

