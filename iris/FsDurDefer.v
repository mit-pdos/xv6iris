(* FsDurDefer.v -- DEFERRED JUSTIFICATION (fs-state.md section 4.75), as
   machine-checked statements rather than as prose.

   Design of record: claude-notes/design/fs-state.md sections 4, 4.5, 4.5a
   and 4.75; worklist claude-notes/projects/durable-disk.md, item 3a-def.
   Its predecessor is iris/FsDurRefute.v, which carries the two walls of the
   home-view accessor ruling; read that file first.

   The ruling of 2026-08-24 makes the TRANSACTION the unit of durable
   justification.  Each open op's ledger entry carries its DEFERRED WRITES;
   [log_write]'s AU offers a justify-now arm and a defer arm; [log_state]
   carries ONE pure row saying that the justified durable view [Dj],
   overlaid with the open ops' deferred maps, IS the logged view; and
   [end_op] consumes ONE fupd per op that carries [Dj] over that op's
   deferred set.  At quiescence the ledger is empty, [Dj = lm_logged L], and
   the commit runs the chain.

   THIS FILE ANSWERS THE ONE QUESTION THE RULING LEAVES OPEN -- what the
   overlay is when two OPEN ops have both written one block, which xv6 does
   constantly (the bitmap block, an inode block, a directory's data block;
   [log_res] permits [out <= 3]) -- and it answers it in three parts.

   (1) NO ORDER-FREE OVERLAY OF PER-OP BYTE MAPS CAN BE THE ROW.  The
       ledger is a [gmap nat _]: it records no order.  Two write orders of
       one block by two open ops reach the SAME ledger and DIFFERENT logged
       views, so no function of [(Dj, ledger)] can equal [lm_logged L] at
       both.  [dfr_ledger_order_blind] is the ledger equality and
       [defer_overlay_order_blind] is the refutation.  It survives every
       repair that keeps the deferred content per-op and order-free -- in
       particular the byte-valued map the ruling's item 1 proposes, and the
       DOMAIN-only variant, whose end_op is refuted separately by
       [defer_domain_row_end_blind].  Deferring the FUNCTION update instead
       of the bytes does not lift it either: function composition is not
       commutative for the pair that actually occurs (one op's [bfree]
       clearing a bit and another's [balloc] setting the same bit), so it
       needs the very order the ledger does not have.

   (2) THE ROW THAT DOES WORK IS POINTWISE, AND IT FORCES EVICTION.
       [dfr_row Dj Lg om] below is the ruling's row spelled without any
       union at all:

         (a) every open op's deferred value at a block IS the logged value
             there, and
         (b) off the deferred domain, [Dj] agrees with the logged view.

       Read (a)+(b) together and they say exactly "[Dj] overlaid with the
       open ops' deferred maps is [lm_logged L]", with no overlay function,
       no order and no disjointness hypothesis.  (a) is what makes it
       order-free: it FORCES any two open ops that hold one block to hold it
       at the same value ([dfr_row_forces_agreement]), so the defer arm has
       to EVICT the block from every other open op's entry as it records it,
       and the justify-now arm has to evict it from all of them.  With that
       discipline the row is maintained by all five ledger transitions --
       [dfr_row_begin], [dfr_row_justify], [dfr_row_defer], [dfr_row_end],
       and [dfr_row_quiesce] collapses it to [Dj = Lg] at [out = 0], which
       is what the commit needs.  All five are proved below, so the
       INTERFACE is real: it is the CONTENT that is not.

   (3) EVICTION MOVES THE OBLIGATION ACROSS THE TRANSACTION BOUNDARY, AND
       THAT IS THE WALL.  [dfr_row_end_target] is (a) read as the op's
       obligation: op [i]'s end-of-op fupd must carry every block of its
       deferred map to that block's FULL logged content.  For a block two
       open ops wrote, the last writer's entry is the only one left, so the
       last writer owes the OTHER op's effect as well -- the bitmap bit the
       other op's [balloc] set, the claim marker the other op's [ialloc]
       wrote -- and it owns neither the resources nor the knowledge.  The
       bitmap instance is machine-checked here: after such a step the other
       op's block is marked USED, so the free pool contributes nothing at it
       ([free_pool_used_no_block]) and no inode names it yet, while the
       later step in which that op's own record adopts the block provably
       CONSUMES the block's ownership ([fs_state_orphan_step_False], the
       [step_forces_the_element] idiom at one block).  Nothing in
       [fs_state Gamma_D] holds it in between.

   So the ruling's consequence 4 -- "the in-transit bin and the
   explicit-pool relaxation are unnecessary and not built" -- does not hold
   once two transactions are open at once: the orphaned block has to be
   parked somewhere that outlives ONE op's fupd, i.e. in the payload's own
   existential (a batch-scope bin, a third index on [Psi]) or in
   [FsDurRefute]'s section C decoupling.  With one op open at a time the
   whole of (3) is vacuous and (2) is the whole interface. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import FsImg.
Require Import RiscvPtsto.     (* [fs_dur_names] -- Gamma_D's two gnames  *)
Require Import LogDefs.        (* [lm_logged], [fs_home_set], [fs_dbytes] *)
Require Import FsDurBytes.     (* [fs_gamma_D]                            *)
Require Import FsState.        (* [fs_state], [free_pool], [inode_owned]  *)

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE LEDGER'S DEFERRED HALF                                        *)
(* ===================================================================== *)

(* One open op's deferred writes: the blocks it has logged and not yet
   justified against the durable predicate, at their content.  This is the
   field [Xv6Cameras.op_entry] gains under the ruling; it is stated here on
   its own so that every law below is about the ledger and nothing else. *)
Definition dfr_map : Type := gmap Z (list (bv 8)).

(* the open ops' entries, keyed by op id exactly as [LogInv.log_res]'s
   ledger is -- A [gmap], hence NO ORDER; section 1 is about that *)
Definition dfr_ledger : Type := gmap nat dfr_map.

(* "no open op has deferred block [b]" *)
Definition dfr_unowned (om : dfr_ledger) (b : Z) : Prop :=
  forall i d, om !! i = Some d -> d !! b = None.

(* THE ROW.  fs-state.md section 4.75 item 2's "[D_justified] overlaid with
   the open ops' deferred maps = [lm_logged L]", spelled POINTWISE so that
   no overlay function -- hence no order, and no disjointness hypothesis --
   is needed.  [Lg] is [lm_logged L cov logstart] at the use site. *)
Definition dfr_row (Dj Lg : gmap Z (list (bv 8))) (om : dfr_ledger) : Prop :=
  (forall i d b v, om !! i = Some d -> d !! b = Some v -> Lg !! b = Some v)
  /\ (forall b, dfr_unowned om b -> Dj !! b = Lg !! b).

(* ===================================================================== *)
(*  1.  THE LEDGER RECORDS NO ORDER, AND THE LOGGED VIEW DEPENDS ON IT    *)
(* ===================================================================== *)

(* Two open ops [i] and [j] each write home block [b] once, [i] with bytes
   [x] and [j] with bytes [y].  The ledger they leave is the SAME map
   whichever order the two writes happen in -- that is all this says, and it
   is what the next lemma turns into a refutation.

   The two orders really are both reachable, and they leave the rest of the
   entry alone as well: take [b] already present in [lh.block[]] (a third
   write earlier in the same batch, e.g. the op's own first [balloc]), so
   both writes take [log_write]'s ABSORB path -- neither spends a budget
   unit, neither grows [lh.n], and each op's already-logged set gains the
   same [b] either way.  Nothing but the deferred half is in play. *)
Lemma dfr_ledger_order_blind (i j : nat) (di dj : dfr_map) (om : dfr_ledger) :
  i <> j ->
  <[i := di]> (<[j := dj]> om) = <[j := dj]> (<[i := di]> om).
Proof. intros Hij. by apply insert_commute. Qed.

(* NO ORDER-FREE OVERLAY IS THE ROW.  [ov] is ARBITRARY: any function of the
   justified view and the ledger -- the ruling's per-op byte maps under any
   union convention, a fold in key order, a per-op function map composed in
   key order, anything.  The two hypotheses are the ROW at the two states
   the two write orders reach, and they force [x = y].

   Read it as: the row is an equation whose right-hand side moves with the
   WRITE ORDER and whose left-hand side cannot see it.  The repair is not a
   better overlay; it is to stop two entries ever holding one block, which
   is section 2. *)
Lemma defer_overlay_order_blind
    (ov : gmap Z (list (bv 8)) -> dfr_ledger -> gmap Z (list (bv 8)))
    (Dj L0 : gmap Z (list (bv 8))) (cov : gset Z) (ls b : Z)
    (x y : list (bv 8)) (i j : nat) (om0 : dfr_ledger) :
  i <> j ->
  b ∈ fs_home_set cov ls ->
  (* order 1: op [i] writes [x], then op [j] writes [y] *)
  ov Dj (<[j := {[b := y]}]> (<[i := {[b := x]}]> om0))
    = lm_logged (<[b := y]> (<[b := x]> L0)) cov ls ->
  (* order 2: op [j] writes [y], then op [i] writes [x] -- the SAME ledger *)
  ov Dj (<[i := {[b := x]}]> (<[j := {[b := y]}]> om0))
    = lm_logged (<[b := x]> (<[b := y]> L0)) cov ls ->
  x = y.
Proof.
  intros Hij Hb H1 H2.
  rewrite (dfr_ledger_order_blind i j {[b := x]} {[b := y]} om0 Hij) in H2.
  rewrite H1 in H2. rewrite !insert_insert in H2.
  rewrite (lm_logged_insert_home L0 cov ls b y Hb) in H2.
  rewrite (lm_logged_insert_home L0 cov ls b x Hb) in H2.
  assert (Hlk : Some y = Some x).
  { rewrite -(lookup_insert (lm_logged L0 cov ls) b y).
    rewrite H2 lookup_insert //. }
  injection Hlk as ->. reflexivity.
Qed.

(* THE DOMAIN-ONLY VARIANT DIES AT [end_op], not at the write.  Weaken the
   row to "[Dj] agrees with the logged view off the union of the deferred
   DOMAINS" -- the values then play no part in the row, and all four
   transitions go through.  But the end-of-op fupd still has to move [Dj]
   somewhere, and the only thing the ending op knows is what IT wrote.  Op
   [j] writes [y], op [i] writes [x] (so the logged view holds [y]), then
   [j] ends and overlays its own [y], then [i] ends and overlays its own
   [x]; with both entries gone the row demands [Dj = Lg] at [b], and it is
   not.  A stale value written back is exactly what the domain-only row
   cannot see. *)
Lemma defer_domain_row_end_blind
    (Dj Lg : gmap Z (list (bv 8))) (b : Z) (x y : list (bv 8)) :
  Lg !! b = Some y ->
  (({[b := x]} : gmap Z (list (bv 8))) ∪ ({[b := y]} ∪ Dj)) !! b = Lg !! b ->
  x = y.
Proof.
  intros Hy Heq.
  assert (Hs : ({[b := x]} : gmap Z (list (bv 8))) !! b = Some x)
    by apply lookup_singleton.
  rewrite (lookup_union_Some_l _ _ _ _ Hs) Hy in Heq.
  injection Heq as ->. reflexivity.
Qed.

(* ===================================================================== *)
(*  2.  THE ROW THAT WORKS, AND THE EVICTION IT FORCES                    *)
(* ===================================================================== *)

(* THE ROW FORCES AGREEMENT.  Two open ops holding one block hold it at ONE
   value, because clause (a) pins both to the logged view.  So the ledger
   transitions have no choice: a [log_write] at [b] must remove [b] from
   every other open op's entry.  That is what makes the row order-free --
   and it is also what section 3 is about, because eviction hands the last
   writer the earlier writer's obligation. *)
Lemma dfr_row_forces_agreement Dj Lg om i j d d' b x y :
  dfr_row Dj Lg om ->
  om !! i = Some d -> om !! j = Some d' ->
  d !! b = Some x -> d' !! b = Some y -> x = y.
Proof.
  intros [H1 _] Hi Hj Hx Hy.
  pose proof (H1 i d b x Hi Hx) as Ex.
  pose proof (H1 j d' b y Hj Hy) as Ey.
  rewrite Ex in Ey. injection Ey as ->. reflexivity.
Qed.

(* THE OP'S END-OF-OP OBLIGATION, read straight off clause (a): whatever the
   op's entry holds, it holds AT THE LOGGED VALUE, so the one fupd [end_op]
   consumes has to carry the durable predicate to the FULL logged content of
   every block in the op's deferred map.  Section 3 is what that costs. *)
Lemma dfr_row_end_target Dj Lg om i d b v :
  dfr_row Dj Lg om -> om !! i = Some d -> d !! b = Some v ->
  Lg !! b = Some v.
Proof. intros [H1 _] Hi Hb. exact (H1 i d b v Hi Hb). Qed.

(* the eviction itself: block [b] leaves every open op's entry *)
Definition dfr_evict (om : dfr_ledger) (b : Z) : dfr_ledger :=
  (delete b) <$> om.

Lemma dfr_evict_lookup om b i :
  dfr_evict om b !! i = (delete b) <$> (om !! i).
Proof. rewrite /dfr_evict lookup_fmap //. Qed.

Lemma dfr_evict_unowned om b : dfr_unowned (dfr_evict om b) b.
Proof.
  intros i d Hd. rewrite dfr_evict_lookup in Hd.
  destruct (om !! i) as [d0|] eqn:Ho; [| discriminate].
  cbn in Hd. injection Hd as <-. apply lookup_delete.
Qed.

Lemma dfr_evict_lookup_Some om b i d' b' v :
  dfr_evict om b !! i = Some d' -> d' !! b' = Some v ->
  b' <> b /\ exists d, om !! i = Some d /\ d !! b' = Some v.
Proof.
  intros Hd' Hb'. rewrite dfr_evict_lookup in Hd'.
  destruct (om !! i) as [d|] eqn:Ho; [| discriminate].
  cbn in Hd'. injection Hd' as <-.
  destruct (decide (b' = b)) as [->|Hne].
  { rewrite lookup_delete in Hb'. discriminate. }
  rewrite lookup_delete_ne in Hb'; [| exact (not_eq_sym Hne)].
  split; [exact Hne |]. exists d. split; [done | exact Hb'].
Qed.

Lemma dfr_unowned_evict_ne om b b' :
  b' <> b -> dfr_unowned (dfr_evict om b) b' -> dfr_unowned om b'.
Proof.
  intros Hne Hun i d Hd.
  assert (He : dfr_evict om b !! i = Some (delete b d))
    by (rewrite dfr_evict_lookup Hd //).
  pose proof (Hun i (delete b d) He) as Hn.
  rewrite lookup_delete_ne in Hn; [exact Hn | exact (not_eq_sym Hne)].
Qed.

(* ---------------------------------------------------------------- *)
(*  The five ledger transitions                                       *)
(* ---------------------------------------------------------------- *)

(* [begin_op] mints an EMPTY deferred map. *)
Lemma dfr_row_begin Dj Lg om i :
  om !! i = None -> dfr_row Dj Lg om -> dfr_row Dj Lg (<[i := ∅]> om).
Proof.
  intros Hi [H1 H2]. split.
  - intros i' d b v Hd Hb.
    destruct (decide (i' = i)) as [->|Hne].
    + rewrite lookup_insert in Hd. injection Hd as <-.
      rewrite lookup_empty in Hb. discriminate.
    + rewrite lookup_insert_ne in Hd; [| exact (not_eq_sym Hne)].
      exact (H1 i' d b v Hd Hb).
  - intros b Hun. apply H2. intros i' d Hd.
    destruct (decide (i' = i)) as [->|Hne].
    { rewrite Hi in Hd. discriminate. }
    apply (Hun i'). rewrite lookup_insert_ne; [exact Hd | exact (not_eq_sym Hne)].
Qed.

(* [log_write], JUSTIFY-NOW arm: the client's step advances [Dj] at [b] and
   the block leaves every open op's entry.  Note there is no side condition:
   the arm is available at ANY block, including one another op had deferred
   -- which is precisely the eviction section 3 prices. *)
Lemma dfr_row_justify Dj Lg om b bs :
  dfr_row Dj Lg om ->
  dfr_row (<[b := bs]> Dj) (<[b := bs]> Lg) (dfr_evict om b).
Proof.
  intros [H1 H2]. split.
  - intros i d' b' v Hd' Hb'.
    destruct (dfr_evict_lookup_Some om b i d' b' v Hd' Hb')
      as (Hne & d & Ho & Hv).
    rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)].
    exact (H1 i d b' v Ho Hv).
  - intros b' Hun.
    destruct (decide (b' = b)) as [->|Hne].
    + rewrite lookup_insert lookup_insert //.
    + rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)].
      rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)].
      exact (H2 b' (dfr_unowned_evict_ne om b b' Hne Hun)).
Qed.

(* [log_write], DEFER arm: the block joins the writer's entry at its new
   content and leaves every other open op's. *)
Lemma dfr_row_defer Dj Lg om i d b bs :
  om !! i = Some d ->
  dfr_row Dj Lg om ->
  dfr_row Dj (<[b := bs]> Lg)
          (<[i := <[b := bs]> d]> (dfr_evict om b)).
Proof.
  intros Hi [H1 H2]. split.
  - intros i' d' b' v Hd' Hb'.
    destruct (decide (i' = i)) as [->|Hne'].
    + rewrite lookup_insert in Hd'. injection Hd' as <-.
      destruct (decide (b' = b)) as [->|Hneb].
      * rewrite lookup_insert in Hb'. injection Hb' as <-.
        rewrite lookup_insert //.
      * rewrite lookup_insert_ne in Hb'; [| exact (not_eq_sym Hneb)].
        rewrite lookup_insert_ne; [| exact (not_eq_sym Hneb)].
        exact (H1 i d b' v Hi Hb').
    + rewrite lookup_insert_ne in Hd'; [| exact (not_eq_sym Hne')].
      destruct (dfr_evict_lookup_Some om b i' d' b' v Hd' Hb')
        as (Hneb & d0 & Ho & Hv).
      rewrite lookup_insert_ne; [| exact (not_eq_sym Hneb)].
      exact (H1 i' d0 b' v Ho Hv).
  - intros b' Hun.
    assert (Hib : <[i := <[b := bs]> d]> (dfr_evict om b) !! i
                    = Some (<[b := bs]> d)) by apply lookup_insert.
    assert (Hneb : b' <> b).
    { intros ->. pose proof (Hun i (<[b := bs]> d) Hib) as Hn.
      rewrite lookup_insert in Hn. discriminate. }
    rewrite lookup_insert_ne; [| exact (not_eq_sym Hneb)].
    apply H2. intros i' d0 Ho.
    destruct (decide (i' = i)) as [->|Hne'].
    + rewrite Hi in Ho. injection Ho as <-.
      pose proof (Hun i (<[b := bs]> d) Hib) as Hn.
      rewrite lookup_insert_ne in Hn; [exact Hn | exact (not_eq_sym Hneb)].
    + assert (He : <[i := <[b := bs]> d]> (dfr_evict om b) !! i'
                     = Some (delete b d0)).
      { rewrite lookup_insert_ne; [| exact (not_eq_sym Hne')].
        rewrite dfr_evict_lookup Ho //. }
      pose proof (Hun i' (delete b d0) He) as Hn.
      rewrite lookup_delete_ne in Hn; [exact Hn | exact (not_eq_sym Hneb)].
Qed.

(* [end_op]: the ONE fupd carries [Dj] over the op's deferred map, and the
   entry is cleared.  [d ∪ Dj] is the overlay -- left-biased, so the op's
   own values win at its own blocks -- and clause (a) is what makes the row
   survive: those values ARE the logged ones. *)
Lemma dfr_row_end Dj Lg om i d :
  om !! i = Some d ->
  dfr_row Dj Lg om ->
  dfr_row (d ∪ Dj) Lg (delete i om).
Proof.
  intros Hi [H1 H2]. split.
  - intros i' d' b v Hd' Hb.
    rewrite lookup_delete_Some in Hd'. destruct Hd' as [_ Ho].
    exact (H1 i' d' b v Ho Hb).
  - intros b Hun.
    destruct (d !! b) as [v|] eqn:Hdb.
    + rewrite (H1 i d b v Hi Hdb).
      apply lookup_union_Some_l. exact Hdb.
    + rewrite lookup_union_r; [| exact Hdb].
      apply H2. intros i' d' Ho.
      destruct (decide (i' = i)) as [->|Hne].
      * rewrite Hi in Ho. injection Ho as <-. exact Hdb.
      * apply (Hun i').
        rewrite lookup_delete_ne; [exact Ho | exact (not_eq_sym Hne)].
Qed.

(* AT QUIESCENCE THE ROW IS THE COMMIT'S CONCLUSION.  [out = 0] forces the
   ledger empty ([LogInv.log_res]'s [size om = out]), and then clause (b) is
   unconditional: the justified view IS the logged view, which is what
   [log_psi_commit] hands the permit. *)
Lemma dfr_row_quiesce Dj Lg : dfr_row Dj Lg ∅ -> Dj = Lg.
Proof.
  intros [_ H2]. apply map_eq. intros b. apply H2.
  intros i d Hd. rewrite lookup_empty in Hd. discriminate.
Qed.

(* the boot's row: nothing open, nothing deferred, [Dj] the logged view *)
Lemma dfr_row_id Dj : dfr_row Dj Dj ∅.
Proof.
  split.
  - intros i d b v Hd. rewrite lookup_empty in Hd. discriminate.
  - intros b _. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  WHAT EVICTION COSTS: THE ORPHANED BLOCK                           *)
(* ===================================================================== *)

Section OrphanBlock.
  Context {Σ : gFunctors}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.

  (* THE POOL CONTRIBUTES NOTHING AT A USED BLOCK.  [pool_elt] is [emp] at a
     set bit, so the pool at a used block is exactly the pool with that slot
     held out -- there is no ownership of it to be had.  This is the source
     half of the wall: after the evicting writer's bitmap step has set the
     OTHER op's bit, the durable state's only two candidate owners of that
     block are the pool (nothing, by this lemma) and an inode whose record
     names it (none yet -- the other op has not written its record). *)
  Lemma pool_elt_used_emp Γ (u : gset Z) (b : Z) :
    b ∈ u -> pool_elt Γ u b ⊣⊢ emp.
  Proof. intros Hb. rewrite /pool_elt (bool_decide_eq_true_2 _ Hb) //. Qed.

  Lemma free_pool_used_no_block Γ (nb : Z) (u : gset Z) (i0 : nat) :
    Z.of_nat i0 < nb -> Z.of_nat i0 ∈ u ->
    free_pool Γ nb u ⊣⊢ free_pool_but Γ nb u i0.
  Proof.
    intros Hlt Hin.
    rewrite (free_pool_split Γ nb u i0 Hlt) (pool_elt_used_emp Γ u _ Hin).
    apply bi.emp_sep.
  Qed.

  (* an inode's own block, out of the whole state -- the target half *)
  Lemma fs_state_block_of_inode Γ S i n k bs :
    fss_inodes S !! i = Some n -> fn_blk n !! k = Some bs ->
    fs_state Γ S -∗ blk_owned Γ (fn_naddr n k) bs.
  Proof.
    intros Hi Hk. rewrite /fs_state /fs_inodes.
    iIntros "(_ & Hin & _)".
    iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hio".
    rewrite /inode_owned /inode_phi.
    iDestruct "Hio" as "((_ & Hb & _) & _)".
    iDestruct (big_sepM_lookup _ _ k bs Hk with "Hb") as "$".
  Qed.

  (* THE WALL, in the [step_forces_the_element] idiom.  Any update whose
     TARGET state has inode [i] naming block [c] must CONSUME block [c]'s
     ownership: an outside holder of it refutes the update.  So the step in
     which the allocating op's own record finally adopts the block cannot be
     supplied by a durable state that does not already hold the block -- and
     by [free_pool_used_no_block] the state the evicting writer's bitmap
     step leaves does not hold it.

     [S1] and [S2] are arbitrary: the lemma is about the STEP, exactly as
     [FsDurRefute.dstep_block_forces_ownership] is about an arbitrary [Q]. *)
  Lemma fs_state_orphan_step_False Γ (Hex : phi_excl Γ) S1 S2 i n k bs bs' :
    fss_inodes S2 !! i = Some n ->
    fn_blk n !! k = Some bs ->
    (fs_state Γ S1 ==∗ fs_state Γ S2) -∗
    fs_state Γ S1 -∗ blk_owned Γ (fn_naddr n k) bs' ==∗ False.
  Proof.
    intros Hi Hk. iIntros "Hstep HS1 Hblk".
    iMod ("Hstep" with "HS1") as "HS2".
    iDestruct (fs_state_block_of_inode Γ S2 i n k bs Hi Hk with "HS2") as "Hb".
    iDestruct (blk_owned_excl Γ Hex with "Hb Hblk") as "[]".
  Qed.

End OrphanBlock.

(* ===================================================================== *)
(*  4.  THE INTERFACE, VERBATIM                                           *)
(* ===================================================================== *)

(* The four shapes fs-state.md section 4.75 asks for, as TYPE-CHECKED
   definitions rather than as prose, so the next lane starts from the terms
   and not from a paraphrase.  None of them is built into the log or the
   crash predicate: section 3 is why.  What each one is:

   - [P_wf_strict] is section 4.5 (2)'s standalone strict predicate -- no
     index by the committed map, no bin, no completeness clause.  The
     durable top map's FRAGMENTS are in it because [FsState.inode_owned]
     carries none and an authority with no elements cannot be retagged.
   - [dstep_strict] is what [LogDefs.fs_dstep] becomes at that body:
     [ghost_map_auth] and [P_wf] are LENT to the step, exactly as today, and
     [LogDefs.fs_dstep_rebase] stops holding -- which is the point.
   - [lw_arm_justify] is [log_write]'s JUSTIFY-NOW arm.  The tie
     [Dj !! b = Lg !! b] is what the log reads off clause (b) of [dfr_row]
     when the block is unowned, and it is the whole of what pins [Dj] for
     the writer: with it, and with its own era byte elements pinning [Lg] at
     its object, the writer knows the durable content of the object it is
     about to move.  There is no [forall Dc] obligation left
     ([FsDurRefute]'s wall (B)) because [Dj] is pinned at the block.
   - The DEFER arm carries no premise at all: the block joins the op's
     ledger entry ([dfr_row_defer]) and [eo_arm] is the obligation.
   - [eo_arm] is [end_op]'s ONE fupd.  [Dfr] is the op's own deferred map,
     known to it by value; [eo_arm_empty] is the [emp]-trivial case that
     every non-deferring op discharges.
   - [commit_conclusion] is the commit's FS-facing conclusion at HOME MAPS
     (section 4.5 (1)): at quiescence [dfr_row_quiesce] turns the row into
     [Dj = lm_logged L cov ls], so the chain the permit runs ends with the
     durable predicate standing at the batch's logged values.  No
     [fs_restrict] arithmetic appears: that stays inside the WAL. *)

Section TheInterface.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  Definition P_wf_strict (g : gname) (Γd : fs_dur_names) : iProp Σ :=
    (∃ S : fs_state_rec,
       ghost_map_auth (fdn_top Γd) 1 (fss_inodes S)
       ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (fs_gamma_D g Γd) i n)
       ∗ fs_state (fs_gamma_D g Γd) S)%I.

  Definition dstep_strict (g : gname) (Γd : fs_dur_names)
      (D D' : gmap Z (list (bv 8))) : iProp Σ :=
    (ghost_map_auth g 1 (fs_dbytes D) -∗ P_wf_strict g Γd ==∗
     ghost_map_auth g 1 (fs_dbytes D') ∗ P_wf_strict g Γd)%I.

  (* the identity survives the flip, as it does today *)
  Lemma dstep_strict_id g Γd D : ⊢ dstep_strict g Γd D D.
  Proof. rewrite /dstep_strict. iIntros "Ha Hw". iModIntro. iFrame. Qed.

  Lemma dstep_strict_trans g Γd D D' D'' :
    dstep_strict g Γd D D' -∗ dstep_strict g Γd D' D'' -∗
    dstep_strict g Γd D D''.
  Proof.
    rewrite /dstep_strict. iIntros "H1 H2 Ha Hw".
    iMod ("H1" with "Ha Hw") as "[Ha Hw]".
    iApply ("H2" with "Ha Hw").
  Qed.

  Implicit Types Psi : gmap Z (list (bv 8)) -> gmap Z (list (bv 8)) -> iProp Σ.

  Definition lw_arm_justify Psi (Lg : gmap Z (list (bv 8)))
      (b : Z) (bs : list (bv 8)) : iProp Σ :=
    (∀ D0 Dj : gmap Z (list (bv 8)),
       ⌜Dj !! b = Lg !! b⌝ -∗ Psi D0 Dj ==∗ Psi D0 (<[b := bs]> Dj))%I.

  Definition eo_arm Psi (Dfr : gmap Z (list (bv 8))) : iProp Σ :=
    (∀ D0 Dj : gmap Z (list (bv 8)), Psi D0 Dj ==∗ Psi D0 (Dfr ∪ Dj))%I.

  Lemma eo_arm_empty Psi : ⊢ eo_arm Psi ∅.
  Proof.
    rewrite /eo_arm. iIntros (D0 Dj) "H".
    assert (Hu : (∅ : gmap Z (list (bv 8))) ∪ Dj = Dj).
    { apply map_eq. intros b.
      rewrite lookup_union_r; [reflexivity | apply lookup_empty]. }
    rewrite Hu. by iModIntro.
  Qed.

  Definition commit_conclusion (g : gname) (Γd : fs_dur_names)
      (D0 L : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) : iProp Σ :=
    dstep_strict g Γd D0 (lm_logged L cov ls).

End TheInterface.

(* the strict body is a nest of block-sized big-ops; seal it the day it is
   written (durable-notes.md, the [iFrame] hang) *)
Global Typeclasses Opaque P_wf_strict dstep_strict lw_arm_justify eo_arm.
