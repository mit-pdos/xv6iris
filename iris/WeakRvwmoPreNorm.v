(** * WeakRvwmoPreNorm.v — THE WRITE-ORDER PRE-NORMALIZATION (wsupply's
      [gwrow_gmo] residual)

    THE POINT.  [WeakRvwmoWalk.wsupply]'s first clause is [gwrow_gmo]: one
    hart's writes reach the log in PROGRAM order.  RVWMO⁻ does not imply it
    (same-hart byte-disjoint stores are unordered by [gppo]) and [grule14]
    does — but the walk exists precisely to REFUTE rule 14, so it must not
    be assumed.  This file runs [WeakRvwmoNorm]'s exchange normalization at
    the WEAKER target: not "every po-earlier memory event is gmo-earlier"
    but only "every po-earlier WRITE OF THE SAME HART is gmo-earlier".

    WHAT THE WEAKER TARGET BUYS, and it is the whole point of the file:

      - THE DESCENDING EVENT IS ALWAYS A WRITE.  The measure counts only
        WRITE-witness inversions ([gviolw] = [WeakRvwmoXchg.gviol] with the
        witness a write), so the po-minimal witness of the gmo-minimal
        violating write is a write and the descent never runs
        [WeakRvwmoXchg]'s READ-down move.  **[WeakRvwmoNorm.kill_K1] — the
        one kill the tree's own non-collapse witness REFUTES
        ([lbgd_kill_K1_false]) — therefore does not arise at all.**
      - CORRESPONDINGLY, the po-minimality that discharges the interior
        side conditions is only over WRITE witnesses, so
        [WeakRvwmoNorm.po_min_no_blocker] covers the interior WRITES and
        not the interior READS.  That is where the price is paid: a read
        sitting gmo-inside the descent interval and po-BEFORE the
        descending write is a new blocker, K4 below.

    THE THREE RESIDUALS, all at an interval event [z] of the descent of a
    write [e] towards the gmo-minimal violating write [w]:

      - [kill_ww_K2] — [z] a READ of one of [e]'s bytes at an OLDER write
        index (B2c's co-maximality condition; [WeakRvwmoNorm.kill_K2]'s
        shape, with the witness premise strengthened to [gviolw]);
      - [kill_ww_K3] — [z] a CROSS-HART SAME-BYTE WRITE (the kit's excluded
        (W,W) case; [WeakRvwmoNorm.kill_K3]'s shape, likewise);
      - [kill_ww_K4] — NEW, and not anticipated by the B2d analysis: [z] a
        READ that is ppo- or dep-ordered BEFORE [e].  Under the full
        rule-14 discipline such a [z] is refuted by po-minimality over all
        MEMORY events; here the minimality is over writes only, so it
        survives.

    THE R-CYCLE ANALYSIS (§5), which is the mathematical content.  Each of
    the three configurations carries the SAME two-edge [RacyD] path

        z →(fr | co | ppo/dep) e →(po-into-a-write) w,

    machine-checked as [kill_ww_K2_Rpath] / [_K3_] / [_K4_].  So each kill
    is an [R]-CYCLE as soon as the ONE remaining edge [w →⁺ z] is there,
    and that edge is exactly what is NOT free: [w] is gmo-minimal, and
    nothing in RVWMO⁻ forces an R-edge out of a gmo-earlier write into a
    gmo-later event (a store nobody reads has no outgoing R-edge at all).
    §5 therefore names that one missing link — [ww_gap_link], stated at
    exactly the descent's own interval and nowhere else — and proves

        acyclicity of [RacyD] over the [gd_equiv] orbit
          + [ww_gap_link]  ⇒  all three kills  ⇒  [normalize_ww].

    This is an HONEST reduction, not a discharge: [ww_gap_link] is the
    residue.  What it replaces is three unanalysed configurations; what is
    left is one reachability statement about a gmo interval, and the
    counterexample that stops it from being free is recorded in the file's
    closing note.

    §6 collects what [wsupply] still costs once [gwrow_gmo] is delegated
    here and the RMW wiring ([WeakRvwmoWalk] §4.5b') has removed
    [lb_rmwfree], and states the capstone at that residue.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports
    this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakLitmus.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvLang.
Require Import RiscvAdequacy.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakLang.
Require Import WeakEvCapstone.
Require Import WeakEvAdequacy.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvProv.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoProbeK1.
Require Import WeakRvwmoLinInd.
Require Import WeakGhost.
Require Import WeakRvwmoLock.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import WeakRvwmoGlue2.
Require Import WeakSrvwmoLitmus.
Require Import WeakSrvwmoCapstone.
Require Import WeakRvwmoCapstone.
Require Import WeakRvwmoWalk.
Require Import WeakRvwmoProgress.
Require Import WeakRvwmoCycWit.
Require Import WeakRvwmoWalk2.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE MEASURE: same-hart WRITE inversions

    [gviolw] is [WeakRvwmoXchg.gviol] with the witness required to be a
    WRITE — so [e] and [w] are two writes of one hart, [e] po-before [w],
    with [w] gmo-before [e].  [nviolw] counts them over
    [WeakRvwmoNorm.gpairs], the enumeration that is LITERALLY equal for two
    [rows_rel]-related graphs. *)

Definition gviolw (G : gexec) (e w : geid) : Prop :=
  gviol G e w ∧ gis_w G e = true.

Local Instance pn_gmem_dec G e : Decision (gmem G e).
Proof.
  rewrite /gmem. destruct (gx_lbl G e) as [l|].
  - destruct (lb_is_mem l) eqn:Hm.
    + left. by exists l.
    + right. intros (l' & Hl' & Hm'). simplify_eq. by rewrite Hm in Hm'.
  - right. intros (l' & Hl' & _). by simplify_eq.
Qed.

Local Instance pn_glbl_is_dec G e P : Decision (glbl_is G e P).
Proof.
  rewrite /glbl_is. destruct (gx_lbl G e) as [l|].
  - destruct (P l) eqn:Hm.
    + left. by exists l.
    + right. intros (l' & Hl' & Hm'). simplify_eq. by rewrite Hm in Hm'.
  - right. intros (l' & Hl' & _). by simplify_eq.
Qed.

Local Instance pn_gpo_dec G e1 e2 : Decision (gpo G e1 e2).
Proof. rewrite /gpo. apply _. Qed.

Local Instance pn_gmo_lt_dec G e1 e2 : Decision (gmo_lt G e1 e2).
Proof. rewrite /gmo_lt. apply _. Qed.

Local Instance pn_gviol_dec G e w : Decision (gviol G e w).
Proof. rewrite /gviol. apply _. Qed.

Local Instance pn_gviolw_dec G e w : Decision (gviolw G e w).
Proof. rewrite /gviolw. apply _. Qed.

Definition violwp (G : gexec) (p : geid * geid) : Prop := gviolw G p.1 p.2.

Local Instance pn_violwp_dec G p : Decision (violwp G p).
Proof. rewrite /violwp. apply _. Qed.

Definition nviolw (G : gexec) : nat := length (filter (violwp G) (gpairs G)).

Lemma gviolw_gpairs G e w : gviolw G e w → (e, w) ∈ gpairs G.
Proof. intros [H _]. by apply gviol_gpairs. Qed.

(** [gis_w] TRANSPORTS along [rows_rel], so a monotone [gviol] gives a
    monotone [gviolw]. *)
Lemma violw_mono_rows (π : nat → nat) (G G' : gexec) :
  rows_rel π G G' →
  (∀ e' w', gviolw G' e' w' → gviol G e' w') →
  ∀ e' w', gviolw G' e' w' → gviolw G e' w'.
Proof.
  intros Hr Hmono e' w' Hv. split; [by apply Hmono|].
  rewrite -(rows_rel_gis_w π G G' e' Hr). by destruct Hv as (_ & H).
Qed.

Lemma nviolw_le G G' :
  gpairs G' = gpairs G → (∀ e w, gviolw G' e w → gviolw G e w) →
  (nviolw G' ≤ nviolw G)%nat.
Proof.
  intros Hp Hmono. rewrite /nviolw Hp.
  apply filter_length_le. intros [e w]. apply Hmono.
Qed.

Lemma nviolw_lt G G' e w :
  gpairs G' = gpairs G → (∀ e' w', gviolw G' e' w' → gviolw G e' w') →
  gviolw G e w → ¬ gviolw G' e w → (nviolw G' < nviolw G)%nat.
Proof.
  intros Hp Hmono Hv Hnv. rewrite /nviolw Hp.
  apply (filter_length_lt _ _ _ (e, w)); [|by apply gviolw_gpairs|done|done].
  intros [e' w']. apply Hmono.
Qed.

(** THE TARGET.  No same-hart write inversion IS [WeakRvwmoWalk.gwrow_gmo]:
    gmo positions and write indices order the writes the same way
    ([gwix_gpos_lt]), so "not gmo-after" is "write-index-before". *)
Lemma nviolw_zero G : gwf G → nviolw G = 0%nat → gwrow_gmo G.
Proof.
  intros Hwf H0 x j k Hjk Hj Hk. pose proof Hwf as (Hnd & _ & _).
  have Hje : (x, j) ∈ gwrites G.
  { destruct Hj as (l & Hl & Hw).
    eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
  have Hke : (x, k) ∈ gwrites G.
  { destruct Hk as (l & Hl & Hw).
    eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
  have Hjg : (x, j) ∈ gx_gmo G by (apply gwrites_elem_of in Hje as [H _]).
  have Hkg : (x, k) ∈ gx_gmo G by (apply gwrites_elem_of in Hke as [H _]).
  have Hne : (x, j) ≠ (x, k) by (intros Heq; injection Heq as Heq'; lia).
  apply (proj2 (gwix_gpos_lt G (x, j) (x, k) Hnd Hje Hke)).
  destruct (gmo_lt_total G (x, j) (x, k) Hnd Hjg Hkg Hne) as [(_ & _ & H)|Hbad];
    [exact H|exfalso].
  have Hv : gviolw G (x, j) (x, k).
  { split; [split_and!|].
    - split_and!; [done|simpl; lia| |].
      + destruct Hj as (l & Hl & _). by exists l.
      + destruct Hk as (l & Hl & _). by exists l.
    - by apply glbl_is_w_gmem.
    - exact Hk.
    - exact Hbad.
    - destruct Hj as (l & Hl & Hw). by rewrite /gis_w Hl. }
  pose proof (filter_pos (violwp G) (gpairs G) ((x, j), (x, k))
                (gviolw_gpairs G _ _ Hv) Hv).
  rewrite /nviolw in H0. lia.
Qed.

(* ====================================================================== *)
(** * 2. THE THREE KILL CONFIGURATIONS

    Each quantifies over the [gd_equiv] orbit, for the reason
    [WeakRvwmoNorm]'s header gives (the configurations arise at INTERMEDIATE
    graphs of the exchange chain and do not pull back).  Each carries the
    descent's own two minimality facts, both now RESTRICTED to write
    witnesses — which is what makes these hypotheses strictly weaker than
    [WeakRvwmoNorm]'s: the violation premise [gviolw e w] itself says [w]
    carries a write witness, and the LB non-collapse graph
    ([WeakRvwmoGraph.lbg]) has none. *)

Definition ww_min (GD' : gdexec) (w : geid) : Prop :=
  ∀ e' w', gviolw (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w.

Definition ww_pomin (GD' : gdexec) (w e : geid) : Prop :=
  ∀ e', gviolw (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat.

(** K2: an interval READ reads one of the descending write's bytes at an
    OLDER write index — B2c's co-maximality side condition. *)
Definition kill_ww_K2 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a t v v',
    gviolw (gd_g GD') e w →
    ww_min GD' w → ww_pomin GD' w e →
    gis_w (gd_g GD') z = false →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    greads_byte (gd_g GD') z a t v →
    gwrites_byte (gd_g GD') e a v' →
    (t < gwix (gd_g GD') e)%nat →
    False.

(** K3: a CROSS-HART SAME-BYTE write sits gmo-inside the interval — the
    kit's deliberately excluded (W,W) case. *)
Definition kill_ww_K3 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a v v',
    gviolw (gd_g GD') e w →
    ww_min GD' w → ww_pomin GD' w e →
    gis_w (gd_g GD') z = true → z.1 ≠ e.1 →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    gwrites_byte (gd_g GD') z a v → gwrites_byte (gd_g GD') e a v' →
    False.

(** K4 — THE NEW ONE.  An interval READ that is ppo-ordered (or
    dep-ordered) before the descending write.  Under [WeakRvwmoNorm]'s
    full rule-14 discipline this is refuted by po-minimality over MEMORY
    events; the write-only minimality of this file does not reach it. *)
Definition kill_ww_K4 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z,
    gviolw (gd_g GD') e w →
    ww_min GD' w → ww_pomin GD' w e →
    gis_w (gd_g GD') z = false →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    (gppo (gd_g GD') z e ∨ (z, e) ∈ gd_deps GD') →
    False.

(** HOW THESE COMPARE TO [WeakRvwmoNorm]'s.  The violation premise is
    STRONGER (the witness must be a write) and the two minimality premises
    are WEAKER (they constrain only write witnesses), so neither kill set
    implies the other pointwise.  What is unambiguously gained is that
    [kill_K1] — the read-descent kill, the ONE the tree's own non-collapse
    witness refutes — has no counterpart here at all, and that the LB
    graph's configuration cannot instantiate any of K2/K3/K4 either: its
    gmo-minimal violating write has no WRITE witness, so [gviolw e w] fails
    outright. *)

(* ====================================================================== *)
(** * 3. ONE DESCENT STEP, ABSTRACTLY — [WeakRvwmoNorm.swap_invariant] at
       the write-restricted measure *)

(** The (R,W) move's violation monotonicity at [gviolw].  [WeakRvwmoXchg.
    gswap_viol_mono_rw] asks for [¬ gpo G z e], which the write-only
    po-minimality does NOT supply when [z] is a read — but the pair the
    swap can newly invert is exactly [(z, e)], and a READ [z] never gives a
    [gviolw].  So the restricted measure is monotone with no side
    condition at all. *)
Lemma gswap_violw_mono_rw G n z e :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some z → gx_gmo G !! S n = Some e →
  gis_w G z = false →
  ∀ e' w', gviolw (gswap G n) e' w' → gviol G e' w'.
Proof.
  intros Hnd Hz He Hzw e' w' [(Hpo & Hme & Hw & Hgmo) Hisw].
  rewrite gswap_po in Hpo. rewrite gswap_mem in Hme.
  rewrite gswap_lbl_is in Hw.
  split_and!; [done|done|done|].
  destruct (gswap_gmo_lt_inv G n z e w' e' Hnd Hz He Hgmo) as [?|[-> ->]];
    [done|].
  exfalso.
  have Hw2 : glbl_is (gswap G n) z lb_is_w by apply gis_w_glbl_is.
  rewrite gswap_lbl_is in Hw2.
  by rewrite (glbl_is_w_gis_w _ _ Hw2) in Hzw.
Qed.

Lemma swap_invariant_w (π : nat → nat) (G G' : gexec) (w e z : geid) (n : nat) :
  gwf G →
  gx_gmo G !! n = Some z → gx_gmo G !! S n = Some e →
  rows_rel π G G' →
  gx_gmo G' = gx_gmo (gswap G n) →
  (∀ e' w', gviolw G' e' w' → gviolw G e' w') →
  gviolw G e w → (gpos G w < n)%nat →
  (∀ e' w', gviolw G e' w' → ¬ gmo_lt G w' w) →
  (∀ e', gviolw G e' w → ¬ (e'.2 < e.2)%nat) →
  (nviolw G' ≤ nviolw G)%nat ∧
  gviolw G' e w ∧
  (∀ e' w', gviolw G' e' w' → ¬ gmo_lt G' w' w) ∧
  (∀ e', gviolw G' e' w → ¬ (e'.2 < e.2)%nat) ∧
  gpos G' e = n ∧ gpos G' w = gpos G w.
Proof.
  intros Hwf Hz He Hrows Hgmo Hmono Hv Hwn Hmin Hpmin.
  pose proof Hwf as (Hnd & _ & _).
  assert (Hzne : w ≠ z).
  { intros Heqz. rewrite Heqz (gpos_of_lookup G n z Hnd Hz) in Hwn. lia. }
  pose proof Hv as (Hv0 & Hew).
  pose proof Hv0 as (Hpo & Hme & Hww & Hmo).
  assert (Hwin : w ∈ gx_gmo G) by (by destruct Hmo as (? & _ & _)).
  split_and!.
  - apply nviolw_le; [by eapply rows_rel_gpairs|exact Hmono].
  - split; [split_and!|].
    + by apply (rows_rel_gpo π G G' e w Hrows).
    + by apply (rows_rel_gmem π G G' e Hrows).
    + by apply (rows_rel_glbl_is π G G' w lb_is_w Hrows (lbl_ren_is_w π)).
    + apply (gmo_lt_gmo_eq G' (gswap G n) w e Hgmo).
      apply (gswap_gmo_lt G n z e w e Hnd Hz He Hmo). by intros [-> _].
    + by rewrite (rows_rel_gis_w π G G' e Hrows).
  - intros e' w' Hv' Hlt'.
    apply (gmo_lt_gmo_eq G' (gswap G n) w' w Hgmo) in Hlt'.
    destruct (gswap_gmo_lt_inv G n z e w' w Hnd Hz He Hlt') as [Hg|[-> ->]];
      [|done].
    by apply (Hmin e' w' (Hmono e' w' Hv')).
  - intros e' Hv'. by apply Hpmin, Hmono.
  - rewrite (gpos_gmo_eq G' (gswap G n) e Hgmo).
    by apply (gswap_gpos_upper G n z e Hnd Hz He).
  - rewrite (gpos_gmo_eq G' (gswap G n) w Hgmo)
            (gswap_gpos G n z e w Hnd Hz He Hwin).
    apply sidx_id; lia.
Qed.

(* ====================================================================== *)
(** * 4. THE DESCENT, AND THE NORMALIZATION

    [w] is the gmo-minimal write carrying a WRITE witness and [e] is its
    po-minimal one.  Slide [e] down one gmo slot at a time until it sits
    directly above [w], then swap the pair — which kills the WW inversion
    while creating none. *)

Section descent_ww.
  Context (GD0 : gdexec).
  Context (HK2 : kill_ww_K2 GD0) (HK3 : kill_ww_K3 GD0) (HK4 : kill_ww_K4 GD0).

  Lemma descent_ww (D : nat) (GD : gdexec) (w e : geid) :
    gd_equiv GD0 GD →
    gviolw (gd_g GD) e w →
    ww_min GD w →
    ww_pomin GD w e →
    (gpos (gd_g GD) e - gpos (gd_g GD) w ≤ D)%nat →
    ∃ GD', gd_equiv GD0 GD' ∧ (nviolw (gd_g GD') < nviolw (gd_g GD))%nat.
  Proof.
    revert GD w e. induction D as [|D IH]; intros GD w e Heq Hv Hmin Hpmin Hd.
    { exfalso. destruct Hv as ((_ & _ & _ & (_ & _ & Hlt)) & _). lia. }
    pose proof Heq as (π & Hrows0 & Hwp0 & Hdeps0 & Hcons).
    pose proof Hcons as (Hc & Hdwf & Hdgmo).
    pose proof Hc as (Hwf & Hppo & Hlv & Hatom).
    pose proof Hwf as (Hnd & Hmemi & Hshape).
    pose proof Hv as (Hv0 & Hewisw).
    pose proof Hv0 as (Hpo_ew & Hmem_e & Hlw & Hmo_we).
    destruct Hpo_ew as (Hag_ew & Hlt_ew & Hse & Hsw).
    pose proof Hmo_we as (Hwin & Hein & Hposlt).
    assert (Hwisw : gis_w (gd_g GD) w = true) by (by apply glbl_is_w_gis_w).
    assert (HSn : gx_gmo (gd_g GD) !! gpos (gd_g GD) e = Some e)
      by (by apply gpos_elem_lookup).
    (* THE VACUITY LEMMA, write-restricted: a WRITE gmo-inside the interval
       and po-before [e] would itself be a write witness of [w], po-earlier
       than [e]. *)
    assert (Hnoblock : ∀ y, gis_w (gd_g GD) y = true →
              gmo_lt (gd_g GD) w y → y.1 = e.1 → (y.2 < e.2)%nat → False).
    { intros y Hyw Hmo Hag Hlt.
      apply (Hpmin y); [|exact Hlt]. split; [split_and!|exact Hyw].
      - split_and!; [by rewrite Hag Hag_ew|lia| |exact Hsw].
        destruct (gis_w_glbl_is _ _ Hyw) as (l & Hl & _). by exists l.
      - by apply gis_w_gmem.
      - exact Hlw.
      - exact Hmo. }
    destruct (decide (gpos (gd_g GD) e = S (gpos (gd_g GD) w))) as [Hfin|Hint].
    - (* ------------------------------------------------------------- *)
      (* THE FINAL SWAP: two same-hart writes, byte-disjoint by poloc.   *)
      (* ------------------------------------------------------------- *)
      set (n := gpos (gd_g GD) w).
      assert (Hn : gx_gmo (gd_g GD) !! n = Some w) by (by apply gpos_elem_lookup).
      assert (HSn' : gx_gmo (gd_g GD) !! S n = Some e) by (by rewrite -Hfin).
      assert (Hnppo : ¬ gppo (gd_g GD) w e).
      { intros Hp. destruct (gppo_po_lt _ _ _ Hp) as [_ Hlt]. lia. }
      assert (Hdisj : ∀ a, (∃ v, gwrites_byte (gd_g GD) w a v) →
                           ¬ ∃ v', gwrites_byte (gd_g GD) e a v').
      { intros a (v & Hwv) (v' & Hev).
        assert (Hpl : gppo (gd_g GD) e w).
        { left. split; [by split_and!|]. exists a. split.
          - left. by exists v'.
          - left. by exists v. }
        pose proof (Hppo e w Hpl) as (_ & _ & ?). lia. }
      assert (Hdep : (w, e) ∉ gd_deps GD).
      { intros Hin. destruct (Hdwf (w, e) Hin) as (_ & Hlt & _ & _).
        simpl in Hlt. lia. }
      pose proof (gswapw_ww_deps GD n w e Hcons Hn HSn' Hwisw Hewisw
                    Hdisj Hnppo Hdep) as Hcons'.
      assert (Hk : (0 < gwix (gd_g GD) w)%nat)
        by (apply gwix_pos; by apply gis_w_gwrites).
      exists (GDExec (gswapw (gd_g GD) n (gwix (gd_g GD) w)) (gd_deps GD)).
      split.
      + exists (λ t, tswap (gwix (gd_g GD) w) (π t)). split_and!.
        * eapply rows_rel_trans;
            [exact Hrows0|exact (rows_rel_gswapw (gd_g GD) n _ Hk)|done].
        * eapply wperm_trans;
            [exact Hwp0
            |exact (wperm_gswapw (gd_g GD) n w e Hnd Hn HSn' Hwisw Hewisw)
            |done].
        * done.
        * exact Hcons'.
      + simpl. destruct (gswapw_resolves (gd_g GD) n w e Hwf Hn HSn' Hwisw
                           Hewisw Hag_ew Hlt_ew) as [_ Hnv].
        eapply (nviolw_lt _ _ e w).
        * exact (rows_rel_gpairs _ _ _ (rows_rel_gswapw (gd_g GD) n _ Hk)).
        * apply (violw_mono_rows (tswap (gwix (gd_g GD) w)) _ _
                   (rows_rel_gswapw (gd_g GD) n _ Hk)).
          intros e' w' [Hv' _].
          eapply (gswapw_viol_mono (gd_g GD) n (gwix (gd_g GD) w) w e);
            [exact Hnd|exact Hn|exact HSn'| |exact Hv'].
          intros Hp. destruct Hp as (_ & Hlt & _ & _). lia.
        * exact Hv.
        * by intros [H _].
    - (* ------------------------------------------------------------- *)
      (* AN INTERIOR SWAP.                                              *)
      (* ------------------------------------------------------------- *)
      assert (Hgap : (S (gpos (gd_g GD) w) < gpos (gd_g GD) e)%nat) by lia.
      set (n := (gpos (gd_g GD) e - 1)%nat).
      assert (HSn' : gx_gmo (gd_g GD) !! S n = Some e).
      { replace (S n) with (gpos (gd_g GD) e) by (rewrite /n; lia). exact HSn. }
      assert (Hnlt : (n < length (gx_gmo (gd_g GD)))%nat).
      { rewrite /n. pose proof (gpos_lt_len (gd_g GD) e Hein). lia. }
      apply lookup_lt_is_Some_2 in Hnlt as [z Hz].
      assert (Hzin : z ∈ gx_gmo (gd_g GD)) by (by eapply elem_of_list_lookup_2).
      assert (Hzpos : gpos (gd_g GD) z = n) by (by apply gpos_of_lookup).
      assert (Hzmem : gmem (gd_g GD) z) by (by eapply gwf_gmo_mem).
      assert (Hwn : (gpos (gd_g GD) w < n)%nat) by (rewrite /n; lia).
      assert (Hmo_wz : gmo_lt (gd_g GD) w z) by (split_and!; [done|done|lia]).
      assert (Hmo_ze : gmo_lt (gd_g GD) z e) by (split_and!; [done|done|lia]).
      assert (Hzs : is_Some (gx_lbl (gd_g GD) z))
        by (destruct Hzmem as (l & Hl & _); by exists l).
      assert (Hzne_e : z ≠ e).
      { intros Heqze. rewrite Heqze in Hmo_ze. by eapply gmo_lt_irrefl. }
      assert (Hstep : ∃ (π' : nat → nat) (G' : gexec),
                rows_rel π' (gd_g GD) G' ∧ wperm π' (gd_g GD) G' ∧
                gx_gmo G' = gx_gmo (gswap (gd_g GD) n) ∧
                rvwmo_minus_deps_consistent (GDExec G' (gd_deps GD)) ∧
                (∀ e' w', gviolw G' e' w' → gviol (gd_g GD) e' w')).
      { destruct (gis_w (gd_g GD) z) eqn:Hzw.
        - (* (W,W): byte-disjoint, or K3 *)
          assert (Hnppo : ¬ gppo (gd_g GD) z e).
          { intros Hp. destruct (gppo_po_lt _ _ _ Hp) as [Hag Hlt].
            exact (Hnoblock z Hzw Hmo_wz Hag Hlt). }
          assert (Hnpo : ¬ gpo (gd_g GD) z e).
          { intros (Hag & Hlt & _ & _). exact (Hnoblock z Hzw Hmo_wz Hag Hlt). }
          assert (Hdep : (z, e) ∉ gd_deps GD).
          { intros Hin. destruct (Hdwf (z, e) Hin) as (Hag & Hlt & _ & _).
            simpl in Hag, Hlt. exact (Hnoblock z Hzw Hmo_wz Hag Hlt). }
          assert (Hkz : (0 < gwix (gd_g GD) z)%nat)
            by (apply gwix_pos, (gis_w_gwrites (gd_g GD) z Hwf Hzs Hzw)).
          assert (Hdisj : ∀ a, (∃ v, gwrites_byte (gd_g GD) z a v) →
                               ¬ ∃ v', gwrites_byte (gd_g GD) e a v').
          { intros a (v & Hzv) (v' & Hev).
            destruct (decide (z.1 = e.1)) as [Hag|Hag].
            - destruct (decide (z.2 < e.2)%nat) as [Hlt|Hge].
              { exact (Hnoblock z Hzw Hmo_wz Hag Hlt). }
              destruct (decide (z.2 = e.2)) as [Heq2|Hne2].
              { destruct Hzne_e. by apply injective_projections. }
              assert (Hpl : gppo (gd_g GD) e z).
              { left. split.
                - split_and!; [by rewrite Hag|lia|exact Hse|exact Hzs].
                - exists a. split; [left; by exists v'|left; by exists v]. }
              pose proof (Hppo e z Hpl) as (_ & _ & ?). lia.
            - exact (HK3 GD Heq w e z a v v' Hv Hmin Hpmin Hzw Hag
                       Hmo_wz Hmo_ze Hzv Hev). }
          exists (tswap (gwix (gd_g GD) z)),
                 (gswapw (gd_g GD) n (gwix (gd_g GD) z)).
          split_and!.
          + exact (rows_rel_gswapw (gd_g GD) n _ Hkz).
          + exact (wperm_gswapw (gd_g GD) n z e Hnd Hz HSn' Hzw Hewisw).
          + done.
          + exact (gswapw_ww_deps GD n z e Hcons Hz HSn' Hzw Hewisw Hdisj
                     Hnppo Hdep).
          + intros e' w' [Hv' _].
            exact (gswapw_viol_mono (gd_g GD) n (gwix (gd_g GD) z) z e e' w'
                     Hnd Hz HSn' Hnpo Hv').
        - (* (R,W): the co-max condition (else K2), the ppo/dep block (K4) *)
          assert (Hnppo : ¬ gppo (gd_g GD) z e).
          { intros Hp.
            exact (HK4 GD Heq w e z Hv Hmin Hpmin Hzw Hmo_wz Hmo_ze
                     (or_introl Hp)). }
          assert (Hdep : (z, e) ∉ gd_deps GD).
          { intros Hin.
            exact (HK4 GD Heq w e z Hv Hmin Hpmin Hzw Hmo_wz Hmo_ze
                     (or_intror Hin)). }
          assert (Hcomax : ∀ a t v, greads_byte (gd_g GD) z a t v →
                     (∃ v', gwrites_byte (gd_g GD) e a v') →
                     (gwix (gd_g GD) e ≤ t)%nat).
          { intros a t v Hrd (v' & Hwb).
            destruct (decide (gwix (gd_g GD) e ≤ t)%nat) as [?|Hgt]; [done|].
            exfalso.
            exact (HK2 GD Heq w e z a t v v' Hv Hmin Hpmin Hzw Hmo_wz Hmo_ze
                     Hrd Hwb ltac:(lia)). }
          exists (λ t, t), (gswap (gd_g GD) n). split_and!.
          + apply rows_rel_gswap.
          + exact (wperm_gswap_lo (gd_g GD) n z e Hz HSn' Hzw).
          + done.
          + exact (gswap_write_down_deps GD n z e Hcons Hz HSn' Hzw Hewisw
                     Hnppo Hcomax Hdep).
          + exact (gswap_violw_mono_rw (gd_g GD) n z e Hnd Hz HSn' Hzw). }
      destruct Hstep as (π' & G' & Hrows' & Hwp' & Hgmo' & Hcons' & Hmono0).
      have Hmono' : ∀ e' w', gviolw G' e' w' → gviolw (gd_g GD) e' w'
        := violw_mono_rows π' (gd_g GD) G' Hrows' Hmono0.
      destruct (swap_invariant_w π' (gd_g GD) G' w e z n Hwf Hz HSn' Hrows'
                  Hgmo' Hmono' Hv Hwn Hmin Hpmin)
        as (Hnle & Hv' & Hmin' & Hpmin' & Hpe' & Hpw').
      assert (Heq' : gd_equiv GD0 (GDExec G' (gd_deps GD))).
      { exists (λ t, π' (π t)). split_and!.
        - by eapply rows_rel_trans.
        - by eapply wperm_trans.
        - done.
        - exact Hcons'. }
      destruct (IH (GDExec G' (gd_deps GD)) w e Heq' Hv' Hmin' Hpmin')
        as (GD'' & Heq'' & Hlt'').
      { simpl. rewrite Hpe' Hpw'. rewrite /n. lia. }
      exists GD''. split; [done|]. simpl in Hlt''. lia.
  Qed.
End descent_ww.

Lemma normalize_ww_aux (GD0 : gdexec) (N : nat) :
  kill_ww_K2 GD0 → kill_ww_K3 GD0 → kill_ww_K4 GD0 →
  ∀ GD, gd_equiv GD0 GD → (nviolw (gd_g GD) ≤ N)%nat →
  ∃ GD', gd_equiv GD0 GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros HK2 HK3 HK4. induction N as [|N IH]; intros GD Heq HN.
  - pose proof Heq as (π & _ & _ & _ & ((Hwf & _ & _ & _) & _ & _)).
    exists GD. split; [done|]. apply nviolw_zero; [done|lia].
  - pose proof Heq as (π & _ & _ & _ & Hcons).
    pose proof Hcons as ((Hwf & _ & _ & _) & _ & _).
    destruct (decide (nviolw (gd_g GD) = 0%nat)) as [H0|H0].
    { exists GD. split; [done|]. by apply nviolw_zero. }
    assert (Hne : filter (violwp (gd_g GD)) (gpairs (gd_g GD)) ≠ []).
    { intros Hnil. rewrite /nviolw Hnil in H0. by apply H0. }
    destruct (list_min_by (λ p : geid * geid, gpos (gd_g GD) p.2) _ Hne)
      as ([e0 w] & Hin & Hmin0).
    apply elem_of_list_filter in Hin as [Hv0 Hin0].
    assert (Hmin : ww_min GD w).
    { intros e' w' Hv' (_ & _ & Hlt).
      assert (Hin' : (e', w') ∈ filter (violwp (gd_g GD)) (gpairs (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv'|].
        by apply gviolw_gpairs. }
      pose proof (Hmin0 (e', w') Hin') as Hle. simpl in Hle, Hlt. lia. }
    assert (Hne2 : filter (λ e', gviolw (gd_g GD) e' w) (gevs' (gd_g GD)) ≠ []).
    { intros Hnil.
      assert (He0 : e0 ∈ filter (λ e', gviolw (gd_g GD) e' w) (gevs' (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv0|].
        destruct Hv0 as ((_ & (l & Hl & _) & _ & _) & _). apply elem_of_gevs'.
        by exists l. }
      rewrite Hnil in He0. by apply elem_of_nil in He0. }
    destruct (list_min_by (λ e' : geid, e'.2) _ Hne2) as (e & Hin2 & Hmin2).
    apply elem_of_list_filter in Hin2 as [Hv Hin2].
    assert (Hpmin : ww_pomin GD w e).
    { intros e' Hv' Hlt.
      assert (Hin' : e' ∈ filter (λ e'', gviolw (gd_g GD) e'' w)
                            (gevs' (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv'|].
        destruct Hv' as ((_ & (l & Hl & _) & _ & _) & _). apply elem_of_gevs'.
        by exists l. }
      pose proof (Hmin2 e' Hin') as Hle. simpl in Hle. lia. }
    destruct (descent_ww GD0 HK2 HK3 HK4
                (gpos (gd_g GD) e - gpos (gd_g GD) w)%nat GD w e
                Heq Hv Hmin Hpmin ltac:(lia)) as (GD1 & Heq1 & Hlt1).
    apply (IH GD1 Heq1). lia.
Qed.

(** THE DELIVERABLE.  Every RVWMO⁻(+deps)-consistent graph whose three
    residual configurations are refuted has a [gd_equiv] member — same
    image, same rows up to the write-index renaming, same dep fragment,
    still consistent — whose same-hart writes reach the log in PROGRAM
    ORDER, which is exactly [WeakRvwmoWalk.wsupply]'s first clause. *)
Theorem normalize_ww (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  kill_ww_K2 GD → kill_ww_K3 GD → kill_ww_K4 GD →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros Hcons HK2 HK3 HK4.
  apply (normalize_ww_aux GD (nviolw (gd_g GD)) HK2 HK3 HK4 GD
           (gd_equiv_refl GD Hcons) (Nat.le_refl _)).
Qed.

(** ** 4.1 THE NON-COLLAPSE WITNESS DOES NOT REFUTE THIS NORMALIZATION

    [WeakRvwmoNorm.lbgd_kill_K1_false] is the tree's proof that the FULL
    normalization has a genuine obstruction: LB is an RVWMO⁻ behaviour
    outside sRVWMO, so an unconditionally successful rule-14 normalization
    would collapse the two models.  The write-order normalization is not
    exposed to it, and here is why in machine-checked form: [lbg] has no
    write-witness inversion at all — each hart's row is one load then one
    store — so [gviolw] is empty and every kill of §2 holds vacuously at
    it.  (This is the SANITY CHECK the K1 refutation is the shadow of: the
    weaker target had better not inherit the stronger one's counterexample.) *)

Lemma lbg_row_short (x k : nat) : is_Some (gx_lbl lbg (x, k)) → (k < 2)%nat.
Proof.
  rewrite /gx_lbl /=. destruct x as [|[|x]]; simpl; [..|by intros []];
    destruct k as [|[|k]]; simpl; try lia; by intros [].
Qed.

Lemma lbg_pos0_notw (x : nat) : gis_w lbg (x, 0%nat) = false.
Proof. rewrite /gis_w /gx_lbl /=. by destruct x as [|[|x]]. Qed.

Lemma lbg_no_violw e w : ¬ gviolw lbg e w.
Proof.
  intros ((Hpo & _ & _ & _) & He).
  destruct Hpo as (Hag & Hlt & Hse & Hsw).
  destruct e as [ex ek], w as [wx wk]. simpl in Hag, Hlt, Hse, Hsw.
  subst wx.
  have Hk2 : (wk < 2)%nat := lbg_row_short ex wk Hsw.
  have Hek : (ek < 2)%nat := lbg_row_short ex ek Hse.
  destruct ek as [|ek]; [by rewrite lbg_pos0_notw in He|lia].
Qed.

Lemma lbg_gwrow : gwrow_gmo lbg.
Proof.
  apply nviolw_zero; [by destruct lb_graph_consistent as (H & _)|].
  rewrite /nviolw. destruct (filter (violwp lbg) (gpairs lbg)) as [|p l] eqn:Hf;
    [done|exfalso].
  have Hp : p ∈ filter (violwp lbg) (gpairs lbg)
    by rewrite Hf; apply elem_of_list_here.
  apply elem_of_list_filter in Hp as [Hv _].
  exact (lbg_no_violw p.1 p.2 Hv).
Qed.

(* ====================================================================== *)
(** * 5. THE R-CYCLE ANALYSIS — WHAT EACH RESIDUAL ACTUALLY IS

    Every kill configuration carries the same two-edge [RacyD] path from
    the interval event [z] to the gmo-minimal violating write [w]:

       z  →(fr | co | ppo or dep)  e  →(po-into-a-write)  w.

    The second edge is [gpow], rule 14's own edge, and it is there by the
    violation premise alone.  The first is the configuration's own content:
    K2 gives [gfr] (the read's [ts] entry is BELOW [e]'s write index, at a
    byte [e] writes — literally [gfr]'s definition), K3 gives [gco] (two
    same-byte writes, and gmo position order IS write-index order), K4
    gives [gppo] or the dep fragment outright.

    So each kill is an [R]-CYCLE exactly when [w →⁺ z] holds — and THAT is
    the edge nothing supplies.  See the closing note (§7) for why. *)

(** [tc] is transitive; stdpp's instance is not usable by name here. *)
Lemma tc_app {A} (R : relation A) x y z : tc R x y → tc R y z → tc R x z.
Proof.
  intros H. revert z. induction H as [a b Hab|a b c Hab Hbc IH];
    intros z Hz.
  - eapply tc_l; [exact Hab|exact Hz].
  - eapply tc_l; [exact Hab|by apply IH].
Qed.

Lemma gviolw_gpow G e w : gviolw G e w → gpow G e w.
Proof.
  intros ((Hpo & Hme & Hlw & _) & _).
  split_and!; [exact Hpo|exact Hme|by apply glbl_is_w_gis_w].
Qed.

Lemma kill_ww_K2_Rpath (GD' : gdexec) (w e z : geid) a t v v' :
  gviolw (gd_g GD') e w →
  gmo_lt (gd_g GD') z e →
  greads_byte (gd_g GD') z a t v →
  gwrites_byte (gd_g GD') e a v' →
  (t < gwix (gd_g GD') e)%nat →
  tc (RacyD GD') z w.
Proof.
  intros Hv Hze Hrd Hwb Hlt.
  eapply tc_l; [|apply tc_once; left; left; exact (gviolw_gpow _ _ _ Hv)].
  left. right. right. right. left. split.
  - intros ->. by eapply gmo_lt_irrefl.
  - by exists a, t, v, v'.
Qed.

Lemma kill_ww_K3_Rpath (GD' : gdexec) (w e z : geid) a v v' :
  gwf (gd_g GD') →
  gviolw (gd_g GD') e w →
  gmo_lt (gd_g GD') z e →
  gwrites_byte (gd_g GD') z a v →
  gwrites_byte (gd_g GD') e a v' →
  tc (RacyD GD') z w.
Proof.
  intros Hwf Hv Hze Hzb Heb. pose proof Hwf as (Hnd & _ & _).
  eapply tc_l; [|apply tc_once; left; left; exact (gviolw_gpow _ _ _ Hv)].
  left. right. right. left. exists a, v, v'. split_and!; [done|done|].
  apply (proj2 (gwix_gpos_lt (gd_g GD') z e Hnd
                  (gwrites_byte_in_gwrites (gd_g GD') z a v Hwf Hzb)
                  (gwrites_byte_in_gwrites (gd_g GD') e a v' Hwf Heb))).
  by destruct Hze as (_ & _ & H).
Qed.

Lemma kill_ww_K4_Rpath (GD' : gdexec) (w e z : geid) :
  gviolw (gd_g GD') e w →
  (gppo (gd_g GD') z e ∨ (z, e) ∈ gd_deps GD') →
  tc (RacyD GD') z w.
Proof.
  intros Hv Hor2.
  eapply tc_l; [|apply tc_once; left; left; exact (gviolw_gpow _ _ _ Hv)].
  destruct Hor2 as [Hppo|Hdep]; [left; by right; right; right; right|by right].
Qed.

(** THE ONE MISSING EDGE, NAMED — and named at exactly the descent's own
    interval, so that it is a statement about a gmo gap between a
    violating write and its write witness, not a claim that [R] is total
    on gmo. *)
Definition ww_gap_link (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z,
    gviolw (gd_g GD') e w →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    tc (RacyD GD') w z.

(** … and with it, [RacyD]-acyclicity over the orbit discharges all three
    residuals. *)
Theorem kill_ww_of_acyclic (GD : gdexec) :
  (∀ GD', gd_equiv GD GD' → ∀ x, ¬ tc (RacyD GD') x x) →
  ww_gap_link GD →
  kill_ww_K2 GD ∧ kill_ww_K3 GD ∧ kill_ww_K4 GD.
Proof.
  intros Hacy Hlink. split_and!.
  - intros GD' Heq w e z a t v v' Hv _ _ _ Hwz Hze Hrd Hwb Hlt.
    apply (Hacy GD' Heq w). eapply tc_app; [exact (Hlink GD' Heq w e z Hv Hwz Hze)|].
    exact (kill_ww_K2_Rpath GD' w e z a t v v' Hv Hze Hrd Hwb Hlt).
  - intros GD' Heq w e z a v v' Hv _ _ _ _ Hwz Hze Hzb Heb.
    pose proof Heq as (_ & _ & _ & _ & ((Hwf & _) & _ & _)).
    apply (Hacy GD' Heq w). eapply tc_app; [exact (Hlink GD' Heq w e z Hv Hwz Hze)|].
    exact (kill_ww_K3_Rpath GD' w e z a v v' Hwf Hv Hze Hzb Heb).
  - intros GD' Heq w e z Hv _ _ _ Hwz Hze Hor.
    apply (Hacy GD' Heq w). eapply tc_app; [exact (Hlink GD' Heq w e z Hv Hwz Hze)|].
    exact (kill_ww_K4_Rpath GD' w e z Hv Hor).
Qed.

Theorem normalize_ww_of_acyclic (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ GD', gd_equiv GD GD' → ∀ x, ¬ tc (RacyD GD') x x) →
  ww_gap_link GD →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros Hcons Hacy Hlink.
  destruct (kill_ww_of_acyclic GD Hacy Hlink) as (HK2 & HK3 & HK4).
  by apply normalize_ww.
Qed.

(* ====================================================================== *)
(** * 6. WHAT [wsupply] STILL COSTS, AND THE CAPSTONE AT THAT RESIDUE

    With [gwrow_gmo] delegated to §4 and [lb_rmwfree] removed from the site
    datum by the RMW wiring ([WeakRvwmoWalk] §4.5b'), what is left of
    [WeakRvwmoWalk.wsupply] is the booted-hart bookkeeping and the WITNESS
    SET: its two side conditions and the per-position classification. *)

Definition wsupply_res (boot : agent → pexv6) (G : gexec) (N : nat) : Prop :=
  (∀ x k, is_Some (gx_lbl G (x, k)) → (x < N)%nat) ∧
  (∀ x k lb, gx_lbl G (x, k) = Some lb → lb_is_w lb = true →
     ∃ cpu m rs fn ib, boot x = PHart cpu m rs fn ib) ∧
  (∃ W : geid → Prop,
     W_poloc_closed G W ∧ wubA G W ∧ wsite_supply G W).

Lemma wsupply_of_gwrow (boot : agent → pexv6) (G : gexec) (N : nat) :
  gwrow_gmo G → wsupply_res boot G N → ∃ W, wsupply boot G W N.
Proof.
  intros H14 (H1 & H2 & (W & H3 & H4 & H5)). exists W. by split_and!.
Qed.

(** THE ONE STEP THE ORBIT COSTS, NAMED.  [normalize_ww] delivers
    [gwrow_gmo] for a [gd_equiv] MEMBER, never for [GD] itself — and
    [WeakRvwmoGlue2.walk_supply] is consumed at the very graph carrying the
    cycle, its conclusion [log_of (gd_g GD) …] pinning the log to THAT
    graph's write list, which the orbit's [wperm] permutes.  So the
    composition below is honest only modulo the pull-back below, which is
    where the remaining architectural work sits: the consumer
    ([cut_supply]/[cert_supply]/[cycle_kill]) has to be restated at the
    normalized member, or the walk's output transported. *)
Definition wsupply_orbit_pull (boot : agent → pexv6) (N : nat) : Prop :=
  ∀ GD GD', gd_equiv GD GD' →
    (∃ W, wsupply boot (gd_g GD') W N) → ∃ W, wsupply boot (gd_g GD) W N.

Theorem wsupply_of_prenorm (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh N : nat) (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  wsupply_orbit_pull boot N →
  (∀ GD' : gdexec,
     rvwmo_minus_deps_consistent GD' → gdexec_qconf boot d0 im nh GD' →
     wsupply_res boot (gd_g GD') N) →
  kill_ww_K2 GD → kill_ww_K3 GD → kill_ww_K4 GD →
  ∃ W, wsupply boot (gd_g GD) W N.
Proof.
  intros Hcons Hq Hpull Hres HK2 HK3 HK4.
  destruct (normalize_ww GD Hcons HK2 HK3 HK4) as (GD' & Heq & Hrow).
  pose proof Heq as (π & Hrows & Hwp & Hdeps & Hcons').
  apply (Hpull GD GD' Heq).
  apply (wsupply_of_gwrow boot (gd_g GD') N Hrow).
  apply (Hres GD' Hcons').
  by eapply gdexec_qconf_ren.
Qed.

(** THE CAPSTONE, with (R-2) SPLIT.  [xv6_rvwmo_safe_modulo_l2']'s single
    per-graph datum becomes

      (R-2a) [wsupply_res] — the booted-hart bounds and the WITNESS SET
             (its two side conditions and the per-position classification);
             note it no longer carries [lb_rmwfree] anywhere, an [LRmw]
             position being served by [WeakRvwmoWalk] §4.5b';
      (R-2b) [gwrow_gmo] — the write-order gate, which §4 reduces to the
             three residuals of §2 (equivalently, by §5, to
             [RacyD]-acyclicity over the orbit plus [ww_gap_link]) for a
             [gd_equiv] MEMBER of the graph. *)
Theorem xv6_rvwmo_safe_modulo_l2'' (Σ : gFunctors)
    `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) *)
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (* (R-2a) the witness set and the booted-hart bounds *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     wsupply_res (xboot σ0) (gd_g GD) (xN σ0)) →
  (* (R-2b) the write-order gate *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     gwrow_gmo (gd_g GD)) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hres Hrow.
  apply (xv6_rvwmo_safe_modulo_l2' Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  intros GD Hcons Hq.
  apply (wsupply_of_gwrow (xboot σ0) (gd_g GD) (xN σ0));
    [by apply Hrow|by apply Hres].
Qed.

(** … and the same capstone with (R-2b) traded for the orbit pull-back and
    the three residuals, i.e. the composition §4 was built for. *)
Theorem xv6_rvwmo_safe_modulo_l2''_prenorm (Σ : gFunctors)
    `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     wsupply_res (xboot σ0) (gd_g GD) (xN σ0)) →
  wsupply_orbit_pull (xboot σ0) (xN σ0) →
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     kill_ww_K2 GD ∧ kill_ww_K3 GD ∧ kill_ww_K4 GD) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hres Hpull Hkill.
  apply (xv6_rvwmo_safe_modulo_l2' Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  intros GD Hcons Hq.
  destruct (Hkill GD Hcons Hq) as (HK2 & HK3 & HK4).
  exact (wsupply_of_prenorm (xboot σ0) (wgdev σ0) (img_z (wgimg σ0))
           (xN σ0) (xN σ0) GD Hcons Hq Hpull Hres HK2 HK3 HK4).
Qed.

(* ====================================================================== *)
(** * 7. THE CLOSING NOTE — why [ww_gap_link] is not free, and what the
       counterexample is

    §5 reduces all three residuals to one edge, [w →⁺ z], where [w] is the
    gmo-minimal violating write and [z] an event of the gmo gap between [w]
    and its po-minimal write witness [e].  That edge is NOT derivable, and
    the reason is structural rather than technical: [w] is gmo-MINIMAL
    among the violating writes, and every arm of [R] out of a write needs a
    reason — [gco] a same-byte later write, [grf] a reader, [gpow]/[gppo] a
    po-later event of [w]'s OWN hart.  A store that nothing reads, whose
    byte nobody rewrites, and after which its hart does nothing, has no
    outgoing [R] edge at all.

    Concretely (two harts, all bytes distinct unless said):

      hart 0:  z = load a ;  e = store x ;  w = store y
      hart 1:  (nothing)
      gmo:     w , z , e            (so [w] gmo-before [z] gmo-before [e])
      ppo:     [z] →ppo [e]         (an address/data dependency into [e])

    This is RVWMO⁻-consistent (the only [gppo] edge, [z] → [e], is
    gmo-forward; [w] and [e] are byte-disjoint stores of one hart, which
    [gppo] does not order), it carries the WW inversion [(e, w)], and its
    [R] is [{z → e, z → w, e → w}] — ACYCLIC.  The descent of [e] is
    blocked at [z] by K4, and no [R]-cycle exists.  So [RacyD]-acyclicity
    alone does NOT discharge the residuals, and [ww_gap_link] is a genuine
    additional hypothesis.

    WHAT THE GRAPH ALSO SHOWS is that it is nonetheless NORMALIZABLE — by
    the move this file does not make: ASCEND [w] past [z] (a (W,R) swap
    whose side conditions, "[z] does not read [w]" and "[¬ gppo w z]", are
    both free here because [z] is po-BEFORE [w]) and then swap the adjacent
    pair.  A strategy mixing ascent of [w] with descent of [e] is therefore
    the natural next attempt, and its own blockers are informative: every
    blocker of the ASCENT of [w] hands back an [R] edge OUT of [w]
    ([grf w y] when [y] reads [w], [gco w y] when [y] rewrites [w]'s byte,
    [gppo w y] outright), which is exactly the edge §5 is missing.  When
    the two searches get stuck at the SAME event the cycle closes; the open
    question is the case where they get stuck at different ones. *)

Print Assumptions lbg_gwrow.
Print Assumptions normalize_ww.
Print Assumptions kill_ww_of_acyclic.
Print Assumptions normalize_ww_of_acyclic.
Print Assumptions wsupply_of_prenorm.
Print Assumptions xv6_rvwmo_safe_modulo_l2''.
Print Assumptions xv6_rvwmo_safe_modulo_l2''_prenorm.
