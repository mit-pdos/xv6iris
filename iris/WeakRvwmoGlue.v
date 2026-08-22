(** * WeakRvwmoGlue.v — THE GLUE: [cycle_kill] modulo the per-site
    classification (route B, stage B2e-3c)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.2(3) and the
    SIXTH-PASS checkpoint item 1 of
    [claude-notes/projects/weak-memory-certification.md].

    WHAT THIS FILE IS.  [WeakRvwmoLinInd.cycle_kill] is the one obligation
    T2-LIN's induction leaves open.  [WeakRvwmoKillArms.cycle_kill_arms]
    kills a cycle that is already presented as a list of CERTIFIED segments.
    This file is everything between the two:

      §1  THE SEGMENT DECOMPOSITION.  [cycle_segments]: an [RacyD] cycle IS
          a nonempty chain of segments — same-hart runs joined by
          cross-hart [gcross] edges — in [WeakRvwmoKillArms]' vocabulary.
          The same-hart arms ([gpow], [gppo], [gd_deps]) are ABSORBED into
          the segments; the decomposition is total because a cycle made of
          those arms ALONE is impossible ([Rsame_acyclic]: each of them is
          strictly po-increasing inside one hart).

      §2  THE PIN STATUS.  A segment's run gives [gmo_lt entry exit] only
          when PINNED, and the three graph sources are named:
          [gacq_po] (ppo rule 5), [gfence_covers] (rule 4), [gd_deps]
          (the store-dep fragment).  [seg_pin_gmo] is the discharge.

      §3  THE CUT.  [cut_ok] = [hull_ok] (po+rf closure) ∧ [wcut_closed]
          (gmo-downward closure on writes, [WeakRvwmoCert4] §2.2) ∧
          [proper_cut] (it drops an event).  The middle clause is
          [WeakRvwmoCert4]'s (O-B) and it is what makes [hren] the
          identity, hence what lets a certified prefix of the hull be a
          certified prefix of [G] ([ctrace_prefix_of_hull]).

      §4  THE REALIZATION ROUTE (THE DESIGN KNOT).  See the long note at
          §4 for which of the three candidate routes is taken and why.

      §5  THE RUN AND THE EXPORTS.  [run_erased] is [WeakSrvwmoCapstone.
          xv6_srvwmo_safe]'s (T1 ∘ the language lift) re-run so that the
          resulting ERASED run is exposed; the three export theorems of
          [WeakEvAdequacy] are then instantiated at its final state, whose
          log IS the candidate's log.

      §6  THE CLAIM AND THE GLUE.  [l2_claim] is the L2′ per-site
          classification, stated over the certified configuration's log.
          [cycle_kill_of_l2] discharges [cycle_kill] from it, and
          [t2lin_of_l2] composes with [WeakRvwmoLinInd.t2lin_of_cycle_kill].

      §7  NON-VACUITY, §8 the audit, §9 the exact ledger of what is left.

    A LEAF: nothing imports this file. *)
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

(* ====================================================================== *)
(** * 1. THE SEGMENT DECOMPOSITION

    [RacyD] splits into the SAME-HART arms — [gpow] (po into a write),
    [gppo] (ppo⁻) and the store-dep fragment [gd_deps] — and the CROSS
    arms [WeakRvwmoKillArms.gcross] (rf / co / fr).  The split is by ARM,
    not by hart: a same-hart rf/co/fr edge is treated as a cross edge, which
    is sound (the cross arms are gmo-forward regardless of hart) and is what
    keeps the decomposition total. *)

Definition Rsame (GD : gdexec) (x y : geid) : Prop :=
  gpow (gd_g GD) x y ∨ gppo (gd_g GD) x y ∨ (x, y) ∈ gd_deps GD.

Lemma RacyD_split GD x y :
  RacyD GD x y → Rsame GD x y ∨ gcross (gd_g GD) x y.
Proof.
  intros [[H|[H|[H|[H|H]]]]|H].
  - left; by left.
  - right; by left.
  - right; right; by left.
  - right; right; by right.
  - left; right; by left.
  - left; right; by right.
Qed.

(** Every same-hart arm is strictly po-increasing inside ONE hart. *)
Lemma gppo_lex G x y : gppo G x y → x.1 = y.1 ∧ (x.2 < y.2)%nat.
Proof.
  intros [H|[H|[H|H]]].
  - destruct H as ((H1 & H2 & _) & _). done.
  - destruct H as (pr & pw & sr & sw & (H1 & H2 & _) & _ & _). done.
  - destruct H as ((H1 & H2 & _) & _). done.
  - destruct H as ((H1 & H2 & _) & _). done.
Qed.

Lemma Rsame_lex GD x y :
  gdeps_wf (gd_g GD) (gd_deps GD) →
  Rsame GD x y → x.1 = y.1 ∧ (x.2 < y.2)%nat.
Proof.
  intros Hwf [(H & _ & _)|[H|H]].
  - destruct H as (H1 & H2 & _). done.
  - by apply (gppo_lex (gd_g GD) x y).
  - destruct (Hwf (x, y) H) as (H1 & H2 & _ & _). done.
Qed.

Lemma tc_Rsame_lex GD x y :
  gdeps_wf (gd_g GD) (gd_deps GD) →
  tc (Rsame GD) x y → x.1 = y.1 ∧ (x.2 < y.2)%nat.
Proof.
  intros Hwf. induction 1 as [x y H|x u y H Htc IH].
  - by apply (Rsame_lex GD x y).
  - destruct (Rsame_lex GD x u Hwf H) as (H1 & H2).
    destruct IH as (H3 & H4). split; [congruence|lia].
Qed.

(** … so a cycle made of same-hart arms alone is impossible. *)
Theorem Rsame_acyclic GD x :
  gdeps_wf (gd_g GD) (gd_deps GD) → ¬ tc (Rsame GD) x x.
Proof. intros Hwf Hc. destruct (tc_Rsame_lex GD x x Hwf Hc). lia. Qed.

(** A SEGMENT's run: its entry reaches its exit by same-hart arms only. *)
Definition seg_run (GD : gdexec) (s : seg) : Prop :=
  rtc (Rsame GD) (sg_entry s) (sg_exit s).

(** THE RAW CHAIN — [WeakRvwmoKillArms.chain] with the certificates
    replaced by the geometry they certify: a cross edge into each entry,
    and a same-hart run from entry to exit. *)
Fixpoint raw_chain (GD : gdexec) (x y : geid) (ss : list seg) : Prop :=
  match ss with
  | [] => x = y
  | s :: ss' => gcross (gd_g GD) x (sg_entry s) ∧ seg_run GD s ∧
                raw_chain GD (sg_exit s) y ss'
  end.

(** One "cross then run" step — the relation whose transitive closure IS a
    raw chain. *)
Definition Crun (GD : gdexec) (u v : geid) : Prop :=
  ∃ e, gcross (gd_g GD) u e ∧ rtc (Rsame GD) e v.

Lemma Crun_raw_chain GD a b :
  tc (Crun GD) a b → ∃ ss, ss ≠ [] ∧ raw_chain GD a b ss.
Proof.
  induction 1 as [a b (e & Hx & Hr)|a u b (e & Hx & Hr) Htc [ss [Hne Hch]]].
  - exists [Seg e.1 e b]. split; [done|]. by split_and!.
  - exists (Seg e.1 e u :: ss). split; [done|]. by split_and!.
Qed.

(** Appending a same-hart tail to a [Crun] chain. *)
Lemma Crun_append GD a b c :
  tc (Crun GD) a b → rtc (Rsame GD) b c → tc (Crun GD) a c.
Proof.
  induction 1 as [a b (e & Hx & Hr)|a u b H Htc IH]; intros Hbc.
  - apply tc_once. exists e. split; [exact Hx|by etrans].
  - eapply tc_l; [exact H|by apply IH].
Qed.

(** THE DECOMPOSITION LEMMA. *)
Lemma racyD_decompose GD a b :
  tc (RacyD GD) a b →
  tc (Rsame GD) a b ∨ ∃ y, rtc (Rsame GD) a y ∧ tc (Crun GD) y b.
Proof.
  induction 1 as [a b H|a u b H Htc IH].
  - destruct (RacyD_split GD a b H) as [Hs|Hx].
    + left. by apply tc_once.
    + right. exists a. split; [done|]. apply tc_once. by exists b.
  - destruct (RacyD_split GD a u H) as [Hs|Hx].
    + destruct IH as [IH|(y & Hry & Hty)].
      * left. by eapply tc_l.
      * right. exists y. split; [|exact Hty]. by eapply rtc_l.
    + destruct IH as [IH|(y & Hry & Hty)].
      * right. exists a. split; [done|]. apply tc_once. exists u.
        split; [exact Hx|]. by apply tc_rtc.
      * right. exists a. split; [done|]. eapply tc_l; [|exact Hty].
        by exists u.
Qed.

(** THE THEOREM.  An [RacyD] cycle is a nonempty raw chain from some event
    back to itself. *)
Theorem cycle_segments GD x :
  gdeps_wf (gd_g GD) (gd_deps GD) →
  tc (RacyD GD) x x →
  ∃ z ss, ss ≠ [] ∧ raw_chain GD z z ss.
Proof.
  intros Hwf Hcyc.
  destruct (racyD_decompose GD x x Hcyc) as [Hbad|(y & Hry & Hty)].
  - by destruct (Rsame_acyclic GD x Hwf Hbad).
  - exists y. apply Crun_raw_chain. by eapply Crun_append.
Qed.

(* ====================================================================== *)
(** * 2. THE PIN STATUS

    A segment's run is [rtc (Rsame GD)] — [gpow], [gppo] and [gd_deps]
    steps.  Only some of those are gmo-forward WITHOUT rule 14: [gpow] is
    rule 14 itself and is exactly what a causal cycle may violate.  So a
    segment yields [gmo_lt entry exit] only when it is PINNED, and §4d.2(3)
    names the three graph sources: ppo rule 5 ([gacq_po] — the entry is an
    acquire read), ppo rule 4 ([gfence_covers] — a fence between), and the
    store-dep fragment ([gd_deps] — address/data/control into the exit).
    A segment that is not pinned is a BACKWARD step and needs one of the
    other two arms of the certificate. *)

Definition seg_pin (GD : gdexec) (s : seg) : Prop :=
  gacq_po (gd_g GD) (sg_entry s) (sg_exit s) ∨
  gfence_covers (gd_g GD) (sg_entry s) (sg_exit s) ∨
  (sg_entry s, sg_exit s) ∈ gd_deps GD.

Theorem seg_pin_gmo GD s :
  rvwmo_minus_deps_consistent GD → seg_pin GD s →
  gmo_lt (gd_g GD) (sg_entry s) (sg_exit s).
Proof.
  intros (Hcons & _ & Hdg) [H|[H|H]].
  - apply (proj1 (proj2 Hcons)). right; right; by left.
  - apply (proj1 (proj2 Hcons)). right; by left.
  - exact (Hdg (sg_entry s, sg_exit s) H).
Qed.

(** A pinned segment, together with the cross edge its raw chain carries,
    IS a [WeakRvwmoKillArms.Pinned] certificate. *)
Lemma seg_pin_cert GD prev s :
  rvwmo_minus_deps_consistent GD →
  gcross (gd_g GD) prev (sg_entry s) → seg_pin GD s →
  cert (gd_g GD) prev s.
Proof.
  intros Hcons Hx Hp. apply Pinned; [exact Hx|by eapply seg_pin_gmo].
Qed.

(* ====================================================================== *)
(** * 3. THE CUT: the write-closed causal past

    §4d.2(1) realizes the cycle's causal past [P = past(K) ∖ K] by the
    induction hypothesis.  Three properties are needed of the per-hart
    prefix lengths [cs] that describe it, and they are exactly the three
    the machinery downstream asks for:

      - [hull_ok] — po-closure (free: a per-hart cut is a prefix) plus
        RF-closure.  [past(K) ∖ K] has it: a read in it whose source were
        outside would put the source causally between two elements of [K],
        hence inside the SCC.
      - [wcut_closed] ([WeakRvwmoCert4] §2.2, its open item (O-B)) —
        gmo-downward closure on WRITES.  This is NOT implied by [hull_ok]
        (which has no [co] clause) and it is what makes the hull's write
        indices — hence [hren], hence the hull's whole label layer —
        literally [G]'s ([gxh_lbl_eq]).  Without it the certified prefix
        cannot be transported back to [G] ([ctrace_prefix_of_hull]).
      - [proper_cut] — it drops at least one event, which is what makes
        the induction hypothesis applicable at all.  It holds as soon as
        the cycle's SCC [K] is nonempty, which it is.

    The construction of [cs] from the cycle's SCC is B2e-3b's (it is the
    "causal past" bookkeeping); here the three properties ARE the cut's
    interface, and everything below consumes only them. *)

Definition cut_ok (G : gexec) (cs : list nat) : Prop :=
  hull_ok G cs ∧ wcut_closed G cs ∧ proper_cut G cs.

Lemma cut_ok_proper G cs : cut_ok G cs → proper_cut G cs.
Proof. by intros (_ & _ & ?). Qed.

(** THE PAYOFF of [wcut_closed], restated at this file's interface: on the
    kept events the hull's labels are [G]'s own, so the hull's certified
    prefixes ARE [G]'s ([WeakRvwmoCert4.ctrace_prefix_of_hull]). *)
Corollary cut_ok_lbl G cs e :
  gwf G → cut_ok G cs → gcut cs e = true →
  gx_lbl (gx_hull G cs) e = gx_lbl G e.
Proof. intros Hwf (Hok & Hwc & _) Hc. by apply gxh_lbl_eq. Qed.

Corollary cut_ok_ctrace G cs c ev W :
  gwf G → cut_ok G cs →
  (∀ p s, cd_tr c !! p = Some s → gcut cs (ev p) = true) →
  ctrace_prefix (gx_hull G cs) c ev W →
  ctrace_prefix G c ev W.
Proof. intros Hwf (Hok & Hwc & _) Hcut Hgt. by eapply ctrace_prefix_of_hull. Qed.

(* ====================================================================== *)
(** * 4. THE REALIZATION ROUTE — THE DESIGN KNOT

    The knot.  To run the certification (§4d.2(2)) one needs the realized
    causal past as a candidate that is a [WeakRvwmoCert3.ctrace_prefix] OF
    [G] — same labels, same write indices.  Three routes were available:

    (a) [WeakRvwmoLin2.gtrace_linearization] on the hull directly.  It
        renames NOTHING, but it needs a [ptrace_ext] of the hull, i.e. a
        linear extension of [po ∪ rf ∪ gmo|W].  The induction hypothesis
        gives [RacyD]-acyclicity, and [RacyD] does NOT contain po into a
        READ — so [ptrace_rel]-acyclicity does not follow from it
        (early reads), and [topo_sort_exists] has nothing to run on.
        REJECTED: the missing acyclicity is precisely rule 14, which the
        hull need not satisfy.

    (b) Retime the hull to a rule-14 graph ([WeakRvwmoNorm.
        normalize_of_acyclic]) and take the RANK trace
        ([WeakRvwmoLin2.glin_ptrace_ext]) of THAT.  This works — and it is
        what (c) does internally — but it delivers a [gtrace_prefix] of the
        RETIMED graph [G'], not of the hull, and transporting
        [gtrace_prefix] along [rows_rel π] is a whole new transport theory
        (every clause of [WeakRvwmoFloor.gtrace_prefix] mentions write
        indices).  REJECTED as more expensive than it buys.

    (c) TAKEN: [WeakRvwmoLinInd.hull_realizable_of_acyclic] — which is
        (b) packaged, and already proved — composed with
        [WeakRvwmoCert4.hull_realizable_rows_G], so that the residual
        renaming is a SINGLE function [rho = pi ∘ hren G cs] stated
        against [G]'s OWN rows.  [wcut_closed] (§3) kills the [hren] half
        outright ([WeakRvwmoCert4.hren_id]), so the whole residue is the
        normalization's [pi] — ONE named function, confined to the row
        equation of [run_data] below, and the only thing the certification
        step has to be tolerant of.  Nothing downstream of §5 sees it: the
        exports read the LOG, and the log is the candidate's own.

    This is the honest state of the knot: route (c) makes the residue a
    single named renaming rather than removing it, and removing it is
    [WeakRvwmoCert4] (O-A)/(O-D) — export a [gtrace_prefix] for a
    linearization and re-derive (a) at a graph that has been retimed
    ROW-WISE.  That is not attempted here. *)

Record run_data (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (c : cand) (pst : nat → list pexv6)
    (dv : nat → dev_state) : Prop := RunData {
  rd_cons : srvwmo_consistent c;
  rd_img  : cd_img c = gx_img G;
  rd_pst0 : pst 0%nat = boot <$> seq 0 N;
  rd_dv0  : dv 0%nat = d0;
  rd_prog : exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c);
}.

(** THE ROUTE, assembled: the induction hypothesis at a good cut realizes
    the causal past, with the row equation carrying the ONE renaming. *)
Theorem hull_run (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat)
    (GD : gdexec) (cs : list nat) (N : nat) :
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  cut_ok (gd_g GD) cs →
  (∀ x, ¬ tc (RacyD (gd_hull GD cs)) x x) →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6) (rho : nat → nat),
    run_data boot d0 N (gd_g GD) c pst (λ _, d0) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren rho
              <$> take (default 0%nat (cs !! i))
                    (default [] (gx_prog (gd_g GD) !! i))).
Proof.
  intros Hcons Hq Hcut Hacy HN.
  destruct (hull_realizable_rows_G boot d0 im nh GD cs N Hcons Hq
              (cut_ok_proper _ _ Hcut) Hacy HN)
    as (c & pst & rho & Hc & Himg & Hpst & Hprog & Hrow).
  exists c, pst, rho. split; [|exact Hrow].
  by split.
Qed.

(* ====================================================================== *)
(** * 5. THE RUN AND THE EXPORTS

    [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s first bullet turns a realized
    candidate into a promise-free run of the event language; the export
    theorems of [WeakEvAdequacy] read an ERASED run.  [run_erased] is that
    composition with the erased run exposed and, crucially, the LOG
    IDENTIFICATION kept: the run's final [wglog] IS the candidate's own log.
    That identification is the whole seam — everything the kill arms read
    (F3′'s fold, F3″'s protection clause) is a predicate on that log. *)

Definition fresh_era (gen : nat) (σ0 : wgstate) : Prop :=
  gen = 0%nat ∧ wgpow σ0 = true ∧ wggen σ0 = 0%nat ∧ wglog σ0 = [] ∧
  (∀ cc : CPU, wgws σ0 cc = ws_init).

Theorem run_erased (gen : nat) (σ0 : wgstate) (boot : agent → pexv6)
    (d0 : dev_state) (N : nat) (G : gexec) (c : cand)
    (pst : nat → list pexv6) (dv : nat → dev_state) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  gx_img G = img_z (wgimg σ0) →
  run_data boot d0 N G c pst dv →
  ∃ t2 σ2,
    rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) ∧
    wglog σ2 = cd_log c (length (cd_tr c)).
Proof.
  intros (Hgen & Hpow & Hgen0 & Hlog & Hws) Hb1 Hb2 Hb3
         [Hcons Himg Hpst0 Hdv0 Hprog].
  have Hlive : ethread_live σ0 gen.
  { rewrite /ethread_live Hpow Hgen0 Hgen. by split. }
  destruct (srvwmo_realizable c Hcons) as (Hwf & Htr & Heximg).
  destruct (exec_wf_pf_run_prog pstep_ev pcls_ev pst dv (cand_exec c)
              pcls_ev_eqr Hwf Hprog) as (cf & Hrun & Hpg & Hdev & Hm).
  rewrite Heximg Himg Hb3 Hpst0 Hb1 Hdv0 Hb2 in Hrun.
  rewrite -(ecfg_of_init gen σ0 Hlog Hws) in Hrun.
  destruct (wp_pf_rtc_epf_rtc (ep_init gen) σ0 cf Hlive Hrun)
    as (P' & σ' & Hr & Heq).
  exists (epool_list P'), σ'. split.
  - pose proof (epf_rtc_erased (ep_init gen, σ0) (P', σ') Hr) as He.
    by rewrite /= epool_list_init in He.
  - destruct Hm as (_ & Hlg & _).
    rewrite -(ecfg_of_log P' σ') Heq -Hlg cand_ex_tr.
    exact (cand_elog c (length (cd_tr c)) ltac:(lia)).
Qed.

(** ** 5.1 THE WP PACKAGE, in the two flavours the exports need

    [wp_package] is [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s premise (b)
    verbatim; [wp_package_prot] is the same with the F3″ REGISTRATION SEAM
    [WeakGhost.wprot_regd] handed back — which is what
    [WeakLock.wplock_inv_regd] produces from a lock client's invariant.
    Per §4d.3′ the seam is per protected byte, so the glue takes it as a
    FAMILY indexed by the byte and its lock word. *)

Definition wp_package (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register) : Prop :=
  ∀ (HR : riscvGS Σ) (HW : weakGS Σ),
    ⊢ ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
         [∗ set] r ∈ D cc,
           reg_pointsto_at cc r (DfracOwn 1)
             (register_lookup r (wgregs σ0 cc))) ∗
      ([∗ map] a ↦ b ∈ wgimg σ0, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
      ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
      wlog_lb [] ∗
      uart_frag (wgdev σ0).(duart) ∗ plic_frag (wgdev σ0).(dplic) ∗
      virtio_frag (wgdev σ0).(dvirtio)
      ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤).

Definition wp_package_prot (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : namespace) (a base : Z) : Prop :=
  ∀ (HR : riscvGS Σ) (HW : weakGS Σ),
    ⊢ ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
         [∗ set] r ∈ D cc,
           reg_pointsto_at cc r (DfracOwn 1)
             (register_lookup r (wgregs σ0 cc))) ∗
      ([∗ map] a0 ↦ b ∈ wgimg σ0, wlat_pointsto (pa_z a0) (DfracOwn 1) 0%nat b) ∗
      ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
      wlog_lb [] ∗
      uart_frag (wgdev σ0).(duart) ∗ plic_frag (wgdev σ0).(dplic) ∗
      virtio_frag (wgdev σ0).(dvirtio)
      ={⊤}=∗ wprot_regd Nm a base ∗
             ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤).

(** ** 5.2 THE EXPORTS AT THE CERTIFIED RUN'S LOG

    F3″ (and, through it, F3′ at the lock word) at every REGISTERED
    protected byte, read at the log the certified configuration carries. *)

Definition prot_reg (P : Z → Z → Prop) (log : list wmsg) : Prop :=
  ∀ a base, P a base →
    ∃ (n0 r0 : nat) (h : option nat),
      wprot_at log a base n0 r0 ∧ wlp_at log base base n0 ∧
      wlp_alt log base n0 h.

Theorem prot_reg_of_run (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (t2 : list eexpr) (σ2 : wgstate) :
  fresh_era gen σ0 →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
  prot_reg P (wglog σ2).
Proof.
  intros (Hgen & Hpow & Hgen0 & Hlog & Hws) Hwp Hrtc a base HP.
  destruct (weak_ev_adequacy_prot Σ gen σ0 D (Nm a base) a base
              Hgen Hpow Hgen0 Hlog Hws (Hwp a base HP) t2 σ2 Hrtc)
    as (γ & n0 & r0 & h & Hpr & Hat & Halt).
  by exists n0, r0, h.
Qed.

(** φ, at the same run: the BAD arm's refutation.  [bad_run] is exactly
    [WeakRobust.violation_hart] at a pf-reachable configuration of the
    certified run — the shape §4d.2(3)'s third arm is stated in. *)
Definition bad_run (gen : nat) (σ0 : wgstate) : Prop :=
  ∃ ρ, rtc epf_run (ep_init gen, σ0) ρ ∧
       violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2).

Theorem no_bad_run (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register) :
  fresh_era gen σ0 → wp_package Σ gen σ0 D → ¬ bad_run gen σ0.
Proof.
  intros (Hgen & Hpow & Hgen0 & Hlog & Hws) Hwp (ρ & Hr & Hv).
  exact (weak_ev_pf_violation_free Σ gen σ0 D Hgen Hpow Hgen0 Hlog Hws Hwp
           ρ Hr Hv).
Qed.

(* ====================================================================== *)
(** * 6. THE L2′ CLAIM AND THE GLUE *)

(** ** 6.1 The CS-chained hypothesis bundle

    Everything [WeakRvwmoKillArms.cs_chained] needs about a segment EXCEPT
    what the exports supply.  The registration point [n0] and the
    protection point [r0] are NOT in the bundle: they are existential in
    F3″'s export, so the two honest side conditions the arms found
    ("registration precedes the reader's acquire", "the protected write is
    above the protection point") are carried as a ∀-clause over them. *)
Definition cs_hyps (GD : gdexec) (P : Z → Z → Prop) (log : list wmsg)
    (prev : geid) (s : seg) : Prop :=
  ∃ (b a : Z) (ACQ REL : geid),
    (* the byte is a REGISTERED protected byte of the lock word at [b] *)
    P a b ∧
    lock_word_byte log b ∧ lock_pattern (gd_g GD) b ∧
    (* the previous exit: an owned plain write of the protected byte,
       inside the log, not touching the lock word *)
    (∃ v, gwrites_byte (gd_g GD) prev a v) ∧ gcls (gd_g GD) prev WCplain ∧
    (gwix (gd_g GD) prev ≤ length log)%nat ∧
    (∀ v, ¬ gwrites_byte (gd_g GD) prev b v) ∧
    (* the reader's row: its acquire, its section, its release fence *)
    lock_acq (gd_g GD) b ACQ ∧ glbl_is (gd_g GD) ACQ lb_aq ∧
    (gwix (gd_g GD) ACQ ≤ length log)%nat ∧
    lock_cs (gd_g GD) b ACQ REL ∧
    gpo (gd_g GD) ACQ (sg_entry s) ∧
    gfence_covers (gd_g GD) (sg_entry s) REL ∧
    gpo (gd_g GD) ACQ (sg_exit s) ∧ gmem (gd_g GD) (sg_exit s) ∧
    ACQ.1 ≠ prev.1 ∧
    (* the registration/protection side conditions, at whatever points the
       export names *)
    (∀ n0 r0, wprot_at log a b n0 r0 →
       (r0 < gwix (gd_g GD) prev)%nat ∧ (n0 < gwix (gd_g GD) ACQ)%nat).

Lemma cs_hyps_cert GD P log prev s :
  rvwmo_minus_deps_consistent GD → log_of (gd_g GD) log → prot_reg P log →
  cs_hyps GD P log prev s → gcross (gd_g GD) prev (sg_entry s) →
  cert (gd_g GD) prev s.
Proof.
  intros (Hcons & _ & _) Hlog Hpr
    (b & a & ACQ & REL & HP & Hlwb & Hpat & Hwa & Hcl & Hlew & Hnob & Hacq &
     Haq & HleA & Hcs & Hpoe & Hfen & Hpox & Hmx & Hhart & Hside) Hx.
  destruct (Hpr a b HP) as (n0 & r0 & h & Hprot & Hat & Halt).
  destruct (Hside n0 r0 Hprot) as (Hr0 & Hn0A).
  apply CSchained.
  exact (cs_chained (gd_g GD) log b a n0 r0 h prev (sg_entry s) (sg_exit s)
           ACQ REL Hcons Hlog Hlwb Halt Hpat Hprot Hwa Hcl Hr0 Hlew Hnob
           Hacq Haq Hn0A HleA Hcs Hpoe Hfen Hx Hpox Hmx Hhart).
Qed.

(** ** 6.2 THE L2′ CLAIM

    THE PER-SITE CLASSIFICATION, at one graph.  Given the certified
    configuration THROUGH ITS LOG ([log_of] — log position [p] is graph
    write index [S p]) and the export seams at that log ([prot_reg] — F3″
    plus F3′ at the lock word, per registered protected byte), EVERY
    segment of EVERY cycle presentation falls in one of the three arms:

      (i)   GRAPH-PINNED  — [seg_pin]: ppo rule 5 ([gacq_po]), rule 4
            ([gfence_covers]), or the store-dep fragment ([gd_deps]);
      (ii)  CS-CHAINED    — [cs_hyps]: the segment's entry is a read inside
            its hart's critical section of a lock whose payload the
            PREVIOUS exit wrote;
      (iii) BAD           — [Bad]: the entry reads an owned-unpublished
            message, i.e. the certifying configuration exhibits a
            [WeakRobust.violation_hart] ([bad_run], §5.2), which φ refutes.

    This is the whole of B2e-3c that remains open; the glue below consumes
    exactly this. *)
Definition l2_claim_at (GD : gdexec) (P : Z → Z → Prop) (Bad : Prop) : Prop :=
  ∀ (log : list wmsg) (z : geid) (ss : list seg),
    rvwmo_minus_deps_consistent GD →
    log_of (gd_g GD) log →
    prot_reg P log →
    ss ≠ [] → raw_chain GD z z ss →
    ∀ (prev : geid) (s : seg),
      s ∈ ss → gcross (gd_g GD) prev (sg_entry s) → seg_run GD s →
      seg_pin GD s ∨ cs_hyps GD P log prev s ∨ Bad.

Definition l2_claim (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat)
    (P : Z → Z → Prop) (Bad : Prop) : Prop :=
  ∀ GD, gdexec_qconf boot d0 im nh GD → l2_claim_at GD P Bad.

(** A classified raw chain IS a [WeakRvwmoKillArms.chain]. *)
Lemma raw_chain_chain GD P log (Bad : Prop) (ss : list seg) :
  rvwmo_minus_deps_consistent GD → log_of (gd_g GD) log → prot_reg P log →
  ¬ Bad →
  (∀ prev s, s ∈ ss → gcross (gd_g GD) prev (sg_entry s) → seg_run GD s →
     seg_pin GD s ∨ cs_hyps GD P log prev s ∨ Bad) →
  ∀ (x y : geid) (ss' : list seg),
    ss' ⊆ ss → raw_chain GD x y ss' → chain (gd_g GD) x y ss'.
Proof.
  intros Hcons Hlog Hpr HnB Hcl x y ss'. revert x.
  induction ss' as [|s ss' IH]; intros x Hsub Hch; [exact Hch|].
  destruct Hch as (Hx & Hrun & Hrest).
  have Hs : s ∈ ss by (apply Hsub, elem_of_list_here).
  have Hsub' : ss' ⊆ ss.
  { intros y' Hy'. apply Hsub, elem_of_list_further, Hy'. }
  split; [|by apply IH].
  destruct (Hcl x s Hs Hx Hrun) as [Hp|[Hcsx|HB]].
  - by apply seg_pin_cert.
  - by eapply cs_hyps_cert.
  - by destruct (HnB HB).
Qed.

(** ** 6.3 THE TWO SUPPLIES B2e-3b OWES, named

    Both are §4d.2's own bookkeeping, and both are stated here rather than
    proved: they are the certification machinery, not the kill.

    [cut_supply] — the cycle's SCC has a causal past, and that past is a
    cut satisfying §3's [cut_ok].  ([WeakRvwmoCert4] (O-B): closing a cut
    downward in gmo preserves [hull_ok], but it must be DONE.)

    [cert_supply] — §4d.2(2): from the realized causal past, the SOLO-RUN
    certification of the cycle's own writes, ending at a candidate whose
    log is [G]'s whole write list ([log_of]).  This is
    [WeakRvwmoCert4.cert_cycle] plus the [Ctx] instantiation ((O-C)) and
    the gmo-order narrowing ((O-A)). *)
Definition cut_supply (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) : Prop :=
  ∀ (GD : gdexec) (z : geid) (ss : list seg),
    rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
    ss ≠ [] → raw_chain GD z z ss →
    ∃ cs, cut_ok (gd_g GD) cs.

Definition cert_supply (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat)
    : Prop :=
  ∀ (GD : gdexec) (cs : list nat) (c0 : cand) (pst0 : nat → list pexv6)
    (z : geid) (ss : list seg),
    rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
    cut_ok (gd_g GD) cs →
    run_data boot d0 N (gd_g GD) c0 pst0 (λ _, d0) →
    ss ≠ [] → raw_chain GD z z ss →
    ∃ (c : cand) (pst : nat → list pexv6) (dv : nat → dev_state),
      run_data boot d0 N (gd_g GD) c pst dv ∧
      log_of (gd_g GD) (cd_log c (length (cd_tr c))).

(** ** 6.4 THE BOOT TIE

    [WeakRvwmoLinInd.cycle_kill] quantifies over EVERY conformant graph and
    carries NO image clause, while the adequacy exports live at ONE booted
    state.  So the tie is a premise here.  FINDING, recorded: the clean fix
    is to add an image clause to [WeakRvwmoSupply.gdexec_qconf] (the bundle
    already fixes the programs and the device state; the image is the one
    piece of the machine's initial configuration it omits), after which
    [boot_tie]'s third conjunct is free at every producer. *)
Definition boot_tie (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat)
    (σ0 : wgstate) : Prop :=
  boot <$> seq 0 N = eps_init σ0 ∧
  d0 = wgdev σ0 ∧
  (∀ GD, gdexec_qconf boot d0 im nh GD →
     gx_img (gd_g GD) = img_z (wgimg σ0) ∧
     (length (gx_prog (gd_g GD)) ≤ N)%nat).

(** ** 6.5 THE GLUE *)
Theorem cycle_kill_of_l2 (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (im : image) (nh : nat)
    (N : nat) :
  fresh_era gen σ0 →
  boot_tie boot d0 im nh N σ0 →
  (* (b) THE WP PACKAGE, in the two flavours the exports need *)
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* the two certification supplies (§6.3) *)
  cut_supply boot d0 im nh →
  cert_supply boot d0 im nh N →
  (* THE L2′ CLAIM *)
  l2_claim boot d0 im nh P (bad_run gen σ0) →
  cycle_kill boot d0 im nh.
Proof.
  intros Hfr (Hb1 & Hb2 & Hb3) Hwp Hwpp Hcut Hcert Hl2.
  intros GD Hcons Hq HIH x Hcyc.
  (* (1) the cycle, as segments *)
  destruct (cycle_segments GD x (proj1 (proj2 Hcons)) Hcyc)
    as (z & ss & Hne & Hch).
  (* (2) the cut, and the realized causal past *)
  destruct (Hcut GD z ss Hcons Hq Hne Hch) as (cs & Hcut_ok).
  destruct (Hb3 GD Hq) as (Himg & HN).
  destruct (hull_run boot d0 im nh GD cs N Hcons Hq Hcut_ok
              (HIH cs (cut_ok_proper _ _ Hcut_ok)) HN) as (c0 & pst0 & rho & Hrd0 & _).
  (* (3) the certified configuration *)
  destruct (Hcert GD cs c0 pst0 z ss Hcons Hq Hcut_ok Hrd0 Hne Hch)
    as (c & pst & dv & Hrd & Hlog).
  (* (4) the erased run, and the exports at its log *)
  destruct (run_erased gen σ0 boot d0 N (gd_g GD) c pst dv Hfr Hb1 Hb2 Himg Hrd)
    as (t2 & σ2 & Hrtc & Hlgeq).
  have Hpr : prot_reg P (cd_log c (length (cd_tr c))).
  { rewrite -Hlgeq.
    exact (prot_reg_of_run Σ gen σ0 D Nm P t2 σ2 Hfr Hwpp Hrtc). }
  (* (5) the per-site classification, and the kill *)
  have HnB : ¬ bad_run gen σ0 := no_bad_run Σ gen σ0 D Hfr Hwp.
  eapply (cycle_kill_arms (gd_g GD) z ss (proj1 Hcons) Hne).
  eapply (raw_chain_chain GD P (cd_log c (length (cd_tr c)))
            (bad_run gen σ0) ss Hcons Hlog Hpr HnB); [| |exact Hch].
  - exact (Hl2 GD Hq (cd_log c (length (cd_tr c))) z ss Hcons Hlog Hpr Hne Hch).
  - done.
Qed.

(** … and T2-LIN itself. *)
Theorem t2lin_of_l2 (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (im : image) (nh : nat)
    (N : nat) :
  fresh_era gen σ0 →
  boot_tie boot d0 im nh N σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  cut_supply boot d0 im nh →
  cert_supply boot d0 im nh N →
  l2_claim boot d0 im nh P (bad_run gen σ0) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 im nh GD →
    ∀ x, ¬ tc (RacyD GD) x x.
Proof.
  intros Hfr Hbt Hwp Hwpp Hcut Hcert Hl2.
  apply t2lin_of_cycle_kill.
  by eapply (cycle_kill_of_l2 Σ gen σ0 D Nm P boot d0 im nh N).
Qed.

(* ====================================================================== *)
(** * 7. NON-VACUITY, ON BOTH SIDES

    (a) THE DECOMPOSITION FIRES on a real cycle: the LB witness
        ([WeakRvwmoLinInd.lbgd_cycle]) decomposes into a nonempty raw
        chain.  So [cycle_segments] is not a statement about an empty
        hypothesis.

    (b) THE CLAIM IS SATISFIABLE: at an [RacyD]-ACYCLIC graph there is no
        raw chain at all, so [l2_claim_at] holds trivially — [mpgd], the
        message-passing probe that VIOLATES rule 14, is such a graph
        ([WeakRvwmoLinInd.mpgd_acyclic]).  A witness with a REAL cycle and
        a REAL per-site classification would need a two-hart emitted
        cycle, which the tree still cannot build: [WeakRvwmoCert4]'s §5.7
        records why ([cycle_two_harts] + [nv4_one_hart] — only ONE
        emitted block exists, so every segs_run witness is single-hart,
        and [cycle_ok] forces at least two harts).  That is the same
        missing second emitted block the SIXTH-PASS checkpoint lists. *)

Lemma Rsame_RacyD GD x y : Rsame GD x y → RacyD GD x y.
Proof.
  intros [H|[H|H]]; [left; by left|left; right;right;right;by right|by right].
Qed.

Lemma rtc_Rsame_RacyD GD x y : rtc (Rsame GD) x y → rtc (RacyD GD) x y.
Proof.
  induction 1 as [x|x u y H _ IH]; [done|].
  eapply rtc_l; [by apply Rsame_RacyD|exact IH].
Qed.

Lemma raw_chain_tc GD x y ss :
  ss ≠ [] → raw_chain GD x y ss → tc (RacyD GD) x y.
Proof.
  revert x. induction ss as [|s ss IH]; intros x Hne Hch; [done|].
  destruct Hch as (Hx & Hrun & Hrest).
  have Hstep : tc (RacyD GD) x (sg_exit s).
  { eapply tc_rtc_r; [apply tc_once; left; by apply gcross_Racy|].
    by apply rtc_Rsame_RacyD. }
  destruct ss as [|s' ss].
  - simpl in Hrest. by subst y.
  - eapply tc_transitive; [exact Hstep|by apply IH].
Qed.

(** (a) *)
Theorem lbgd_segments : ∃ z ss, ss ≠ [] ∧ raw_chain lbgd z z ss.
Proof.
  destruct lbgd_cycle as [x Hx].
  eapply (cycle_segments lbgd x); [|exact Hx].
  by intros rw Hrw%elem_of_nil.
Qed.

(** (b) *)
Theorem l2_claim_mpgd (P : Z → Z → Prop) (Bad : Prop) : l2_claim_at mpgd P Bad.
Proof.
  intros log z ss _ _ _ Hne Hch. exfalso.
  eapply mpgd_acyclic. by eapply raw_chain_tc.
Qed.

(* ====================================================================== *)
(** * 8. AUDIT *)

Print Assumptions cycle_segments.
Print Assumptions Rsame_acyclic.
Print Assumptions seg_pin_gmo.
Print Assumptions cut_ok_ctrace.
Print Assumptions hull_run.
Print Assumptions run_erased.
Print Assumptions prot_reg_of_run.
Print Assumptions no_bad_run.
Print Assumptions cs_hyps_cert.
Print Assumptions raw_chain_chain.
Print Assumptions cycle_kill_of_l2.
Print Assumptions t2lin_of_l2.
Print Assumptions lbgd_segments.
Print Assumptions l2_claim_mpgd.

(* ====================================================================== *)
(** * 9. WHAT THIS FILE LEAVES OPEN — the exact ledger

    Nothing below is [Admitted]; these are the four PREMISES of
    [cycle_kill_of_l2] that are not discharged here, and what discharges
    each.

    (G-1) [l2_claim] — THE PER-SITE CLASSIFICATION (§6.2).  This is L2′
          proper, and it is the intended residue: B2e-3c's remaining work
          is to prove it site class by site class for xv6's real lock
          clients.  It is a HYPOTHESIS, never an axiom (the audit above
          shows [cycle_kill_of_l2] at exactly the five rv64d reservation
          axioms).

    (G-2) [cut_supply] (§6.3) — the cycle's SCC has a causal past, and
          that past is a [cut_ok] cut.  po-closure is free (a per-hart cut
          is a prefix), rf-closure is §4d.2(1)'s own argument (a source
          outside [past(K) ∖ K] would land in the SCC), [proper_cut] holds
          because [K] is nonempty; [wcut_closed] is
          [WeakRvwmoCert4] (O-B) and is the one clause that has to be
          ENGINEERED (close the cut downward in gmo, then re-close under
          rf, and re-check the measure).

    (G-3) [cert_supply] (§6.3) — §4d.2(2)'s solo-run certification, i.e.
          [WeakRvwmoCert4.cert_cycle] with its [Ctx] instantiated
          ((O-C)) and its gmo-order narrowing ((O-A)).  Its conclusion is
          stated exactly as this file consumes it: a [run_data] whose log
          is [log_of] of the WHOLE graph.

    (G-4) [boot_tie]'s third conjunct (§6.4) — the image/hart-count tie
          between the graph and the booted state.  See the FINDING there:
          adding an image clause to [WeakRvwmoSupply.gdexec_qconf] makes
          it free.

    THE ADEQUACY COMPOSITION, enumerated (all of it PROVED here, §5):

      run_data                                       (§4, [hull_run] or (G-3))
        -> [WeakAxiomatic3.srvwmo_realizable]         (T1, the exec_wf half)
        -> [WeakAxRealize.exec_wf_pf_run_prog]        (T1, program-carrying)
        -> [WeakEvCapstone.ecfg_of_init]              (the booted config)
        -> [WeakEvCapstone.wp_pf_rtc_epf_rtc]         (the language lift)
        -> [WeakEvPf.epf_rtc_erased]                  (pf run => erased run)
        -> log identification via [WeakEvPf.ecfg_of_log] +
           [WeakAxiomatic2.cand_elog]                 ([run_erased])
        -> [WeakEvAdequacy.weak_ev_adequacy_prot]     (F3" + F3', [prot_reg])
        -> [WeakEvAdequacy.weak_ev_pf_violation_free] (phi, [no_bad_run])

    [WeakEvAdequacy.weak_ev_adequacy_lockalt] is NOT in the chain: F3"'s
    export ([weak_ev_adequacy_prot]) already returns the lock word's
    [wlp_at]/[wlp_alt] alongside [wprot_at], which is exactly the pair
    [WeakRvwmoKillArms.cs_chained] consumes, so the [wlock_regd] seam is
    subsumed by the [wprot_regd] one and only ONE WP-package flavour is
    needed per protected byte. *)
