(** * WeakRvwmoCert4.v — B2e-3b SLICE 3c: THE CYCLE-ORDER CERTIFICATION

    Design: [claude-notes/design/weak-memory-route-b.md] §4e ("SLICE 3's
    SHAPE AND ITS ONE OPEN RISK", "SLICES 2b/3, STATED") and the FIFTH-PASS
    checkpoint item 1 of
    [claude-notes/projects/weak-memory-certification.md].

    WHAT THIS FILE IS.  [WeakRvwmoCert3.cert_segment'] certifies ONE hart's
    segment against a carried context [Ctx]; slice 3c walks it around an
    [R]-cycle.  Three things are landed here.

    (1) THE RENAMING RECONCILIATION (§2–§3) — the finding this slice was
        asked to produce.  Two DIFFERENT renamings sit between the realized
        causal past and [WeakRvwmoCert3.ctrace_prefix], and only one of them
        is an artifact:

        - [WeakRvwmoLinInd.hull_realizable_of_acyclic] hands back rows equal
          to the HULL's rows up to [lbl_ren pi], with [pi] from
          [WeakRvwmoNorm.normalize_of_acyclic].  Composing with
          [WeakRvwmoHull.gxh_row] ([hull_realizable_rows_G], §2.1) the total
          renaming against [G]'s OWN rows is [pi ∘ hren G cs].  The [pi]
          half is avoidable — [WeakRvwmoLin2.gtrace_linearization]
          linearizes an acyclic hull with NO renaming at all — but the
          [hren] half is NOT: [WeakRvwmoHull.gx_hull] renames by
          construction, because a hull's write indices count only the
          hull's writes.

        - [hren] IS the identity exactly when the cut is gmo-DOWNWARD-CLOSED
          on writes ([wcut_closed], §2.2) — and then, and only then, the
          hull's labels are literally [G]'s ([gxh_lbl_eq], §2.3) and a
          [ctrace_prefix] of the HULL is a [ctrace_prefix] of [G]
          ([ctrace_prefix_of_hull], §3.1).  [hull_ok] does NOT imply
          [wcut_closed] (it is po-closure + rf-closure, no co clause), so
          this is a real side condition on the cut the cycle's causal past
          picks.

    (2) THE FLOOR DOES NOT TOLERATE A RENAMED LOG (§3.2), and the proof is
        not a counterexample but an identity: [ctrace_prefix]'s own [ctp_wix]
        clause FORCES the candidate's writes to be appended in gmo order
        ([ctp_wix_gmo_mono]).  [WeakRvwmoFloor.gvis_ub] reads a log index [s]
        as "[gwrite_at G s]", so a log that is not a gmo prefix makes
        [cert_floor_ok] false, not merely unprovable.  CONSEQUENCE, and the
        narrowing this file adopts: slice 3c is stated for cycles whose exit
        writes are appended in gmo order ([Hgmo_order] below, §5.3); the
        general case's obligation is stated in §6 (O-A).

    (3) THE CYCLE ITERATION (§4–§5).  [segs_run] is the walk around the
        cycle — a list of per-segment certifications, each one a
        [seg_step], threaded through a [cyc_state] = (candidate, process
        supply, device supply).  [cert_cycle] is the theorem: the walk ends
        at a consistent candidate with a real [exec_prog_ok'] supply at the
        quiet fabric, and EVERY segment's appended trace sits at a KNOWN
        OFFSET in the final candidate ([cert_cycle_stable]) — so the exit
        writes ([cert_cycle_exit]) and the entry read steps
        ([cert_cycle_pos]) are addressable by B2e-3c's kill arms.
        [seg_step_of_segment] (§4.3) shows the interface is exactly what
        [cert_segment'] delivers, and §5.1 that a ONE-segment cycle cannot
        exist.

    Nothing below is [Admitted] or [Axiom]-ed. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoHull.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoConfWit.
Require Import WeakEvProv.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoLinInd.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. TWO LIST FACTS *)

(** A filter whose predicate is DOWNWARD CLOSED along the list is a PREFIX
    of it.  This is the whole combinatorial content of §2.2. *)
Lemma filter_downward_prefix {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) :
  (∀ i j x y, (i < j)%nat → l !! i = Some x → l !! j = Some y → P y → P x) →
  filter P l = take (length (filter P l)) l.
Proof.
  induction l as [|x l IH]; intros Hdc; [done|].
  destruct (decide (P x)) as [Hx|Hx].
  - rewrite (filter_cons_True P x l Hx) /=. f_equal.
    apply IH. intros i j y z Hij Hi Hj Hz.
    by apply (Hdc (S i) (S j) y z ltac:(lia) Hi Hj).
  - rewrite (filter_cons_False P x l Hx) /=.
    have Hnil : filter P l = [].
    { destruct (filter P l) as [|y tl] eqn:E; [done|exfalso].
      have Hy : y ∈ filter P l by (rewrite E; apply elem_of_list_here).
      apply elem_of_list_filter in Hy as [HPy Hyl].
      apply elem_of_list_lookup in Hyl as [j Hj].
      apply Hx. by apply (Hdc 0%nat (S j) x y ltac:(lia) eq_refl Hj). }
    by rewrite Hnil.
Qed.

(** A pointwise-identity [fmap]. *)
Lemma fmap_id_pointwise {A} (f : A → A) (l : list A) :
  (∀ i x, l !! i = Some x → f x = x) → f <$> l = l.
Proof.
  induction l as [|x l IH]; intros H; [done|].
  rewrite fmap_cons (H 0%nat x eq_refl). f_equal.
  apply IH. intros i y Hy. by apply (H (S i)).
Qed.

(** [gwix] is positive only on writes. *)
Lemma gwix_pos_elem G e : (0 < gwix G e)%nat → e ∈ gwrites G.
Proof.
  rewrite /gwix.
  destruct (list_find (λ e', e' = e) (gwrites G)) as [[i y]|] eqn:Hf;
    [|lia].
  intros _. apply list_find_Some in Hf as (Hi & -> & _).
  by eapply elem_of_list_lookup_2.
Qed.

(* ====================================================================== *)
(** * 2. THE RENAMING RECONCILIATION *)

(** ** 2.1 The renaming a realized hull actually carries

    [hull_realizable_of_acyclic] states its row equation against the HULL's
    rows.  Unfolded against [G]'s own rows it is a SINGLE renaming, the
    composite [pi ∘ hren G cs] — [pi] from the normalization,
    [hren] from the hull itself. *)
Theorem hull_realizable_rows_G (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (GD : gdexec) (cs : list nat) (N : nat) :
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  proper_cut (gd_g GD) cs →
  (∀ x, ¬ tc (RacyD (gd_hull GD cs)) x x) →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6) (rho : nat → nat),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren rho
              <$> take (default 0%nat (cs !! i))
                    (default [] (gx_prog (gd_g GD) !! i))).
Proof.
  intros Hcons Hq Hpc Hacy HN.
  destruct (hull_realizable_of_acyclic boot d0 im nh GD cs N Hcons Hq Hpc Hacy HN)
    as (c & pst & pi & Hc & Himg & Hpst & Hpo & Hrow).
  exists c, pst, (λ t, pi (hren (gd_g GD) cs t)). split_and!;
    [exact Hc|exact Himg|exact Hpst|exact Hpo|].
  intros i. rewrite (Hrow i) gxh_row.
  by apply (row_ren_comp (hren (gd_g GD) cs) pi).
Qed.

(** ** 2.2 When [hren] is the identity: a gmo-downward-closed cut *)

(** THE SIDE CONDITION.  [hull_ok] is po-closure + rf-closure; it says
    NOTHING about [co].  This is the missing clause. *)
Definition wcut_closed (G : gexec) (cs : list nat) : Prop :=
  ∀ w1 w2, w1 ∈ gwrites G → w2 ∈ gwrites G → gcut cs w2 = true →
           (gwix G w1 < gwix G w2)%nat → gcut cs w1 = true.

(** Under it the hull's writes are a PREFIX of [G]'s. *)
Lemma wcut_closed_prefix G cs :
  NoDup (gx_gmo G) → wcut_closed G cs →
  gwrites (gx_hull G cs)
  = take (length (gwrites (gx_hull G cs))) (gwrites G).
Proof.
  intros Hnd Hwc. rewrite gxh_gwrites_G. apply filter_downward_prefix.
  intros i j x y Hij Hi Hj Hy.
  apply Is_true_true_1 in Hy. apply Is_true_true.
  apply (Hwc x y (gwrites_lookup_elem G i x Hi)
           (gwrites_lookup_elem G j y Hj) Hy).
  rewrite (gwix_of_lookup G i x Hnd Hi) (gwix_of_lookup G j y Hnd Hj). lia.
Qed.

(** … so a hull write's index is unchanged. *)
Theorem hull_gwix_eq G cs w :
  NoDup (gx_gmo G) → wcut_closed G cs →
  w ∈ gwrites G → gcut cs w = true →
  gwix (gx_hull G cs) w = gwix G w.
Proof.
  intros Hnd Hwc Hw Hc.
  have Hnd' : NoDup (gx_gmo (gx_hull G cs)).
  { rewrite gxh_gmo /gx_cut /=. by apply list_relations.NoDup_filter. }
  have Hmem : w ∈ gwrites (gx_hull G cs)
    by (apply gxh_gwrites_elem; split; [exact Hc|exact Hw]).
  destruct (gwix_lookup (gx_hull G cs) w Hmem) as (i & Hi & Heq).
  rewrite Heq. symmetry. apply (gwix_of_lookup G i w Hnd).
  rewrite (wcut_closed_prefix G cs Hnd Hwc) in Hi.
  by eapply lookup_take_Some.
Qed.

Corollary hren_id G cs t :
  NoDup (gx_gmo G) → wcut_closed G cs →
  (∀ w, gwrite_at G t = Some w → gcut cs w = true) →
  hren G cs t = t.
Proof.
  intros Hnd Hwc Hcut. rewrite /hren.
  destruct (gwrite_at G t) as [w|] eqn:Ht; [|done].
  have Hc : gcut cs w = true := Hcut w eq_refl.
  rewrite Hc -gxh_gwix.
  destruct (gwrite_at_inv G t w Hnd Ht) as (Hw & <-).
  by apply (hull_gwix_eq G cs w Hnd Hwc Hw Hc).
Qed.

(** ** 2.3 THE PAYOFF: the hull's labels are [G]'s own

    Every [ts] entry of a kept label either names no write at all
    ([gwrite_at G t = None], where [hren] is the identity by definition) or
    names a write the cut keeps ([hull_ok]'s rf clause), where §2.2 applies. *)
Theorem gxh_lbl_eq G cs e :
  gwf G → hull_ok G cs → wcut_closed G cs → gcut cs e = true →
  gx_lbl (gx_hull G cs) e = gx_lbl G e.
Proof.
  intros Hwf Hok Hwc Hc.
  have Hnd : NoDup (gx_gmo G) := proj1 Hwf.
  rewrite gxh_lbl Hc.
  destruct (gx_lbl G e) as [l|] eqn:Hl; [|done]. simpl. f_equal.
  have Hts : ∀ base ts vs, lb_rd l = Some (base, ts, vs) →
                           hren G cs <$> ts = ts.
  { intros base ts vs Hrd.
    have Hlen : length vs = length ts.
    { destruct l; simplify_eq/=.
      - exact (gshape G Hwf e _ Hl).
      - destruct (gshape G Hwf e _ Hl) as (_ & _ & H). exact H. }
    apply fmap_id_pointwise. intros j t Hj.
    apply (hren_id G cs t Hnd Hwc). intros w Hw.
    destruct (lookup_lt_is_Some_2 vs j
                ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
    apply (hull_ok_rf G cs e (WeakAxiomatic.acc_addr base j) t v w Hok Hc); [|exact Hw].
    by exists l, base, ts, vs, j. }
  destruct l as [aq base ts vs|rl base vs kc|pr pw sr sw
                |aq rl base ts rvs wvs kc]; simpl.
  - by rewrite (Hts base ts vs eq_refl).
  - done.
  - done.
  - by rewrite (Hts base ts rvs eq_refl).
Qed.

(* ====================================================================== *)
(** * 3. THE BRIDGE, AND WHY IT CANNOT BE DONE UP TO A RENAMING *)

(** ** 3.1 A certified prefix of the HULL is a certified prefix of [G] *)
Theorem ctrace_prefix_of_hull G cs c ev W :
  gwf G → hull_ok G cs → wcut_closed G cs →
  (∀ p s, cd_tr c !! p = Some s → gcut cs (ev p) = true) →
  ctrace_prefix (gx_hull G cs) c ev W →
  ctrace_prefix G c ev W.
Proof.
  intros Hwf Hok Hwc Hcut Hgt.
  have Hnd : NoDup (gx_gmo G) := proj1 Hwf.
  have Hlbl : ∀ e, gcut cs e = true →
                   gx_lbl (gx_hull G cs) e = gx_lbl G e
    := λ e He, gxh_lbl_eq G cs e Hwf Hok Hwc He.
  (* a hull write index IS a G write index *)
  have Hwix : ∀ e, (0 < gwix (gx_hull G cs) e)%nat →
                   gwix (gx_hull G cs) e = gwix G e.
  { intros e He. apply gwix_pos_elem, gxh_gwrites_elem in He as [Hc Hw].
    by apply hull_gwix_eq. }
  destruct Hgt as [Himg Hag Hpos Hstep Hwixc Hlog]. split.
  - by rewrite Himg gxh_img.
  - exact Hag.
  - exact Hpos.
  - intros p s Hs. destruct (Hstep p s Hs) as [[HnW Hl]|[HW Hw]].
    + left. split; [exact HnW|]. by rewrite -(Hlbl _ (Hcut p s Hs)).
    + right. split; [exact HW|].
      destruct Hw as (base & n & ts0 & vs0 & Hl & Hn & Hlb).
      exists base, n, ts0, vs0. split_and!;
        [by rewrite -(Hlbl _ (Hcut p s Hs))|exact Hn|exact Hlb].
  - intros p s Hs Hw. rewrite -(Hwix (ev p)); [by apply (Hwixc p s Hs)|].
    rewrite (Hwixc p s Hs Hw). lia.
  - intros s Hs Hle. destruct (Hlog s Hs Hle) as (w & Hw & Heq).
    have Hnd' : NoDup (gx_gmo (gx_hull G cs)).
    { rewrite gxh_gmo /gx_cut /=. by apply list_relations.NoDup_filter. }
    destruct (gwrite_at_inv (gx_hull G cs) s w Hnd' Hw) as (Hmem & Hix).
    apply gxh_gwrites_elem in Hmem as [Hc Hmem].
    have Hg : gwix G w = s
      by rewrite -Hix (hull_gwix_eq G cs w Hnd Hwc Hmem Hc).
    exists w. split; [rewrite -Hg; by apply gwrite_at_gwix|].
    rewrite Heq /gwmsg (Hlbl w Hc) //.
Qed.

(** The certification context (§3.3 of [WeakRvwmoCert3]) transported the
    same way. *)
Corollary cpol_ctx_of_hull G cs (W : geid → Prop) (x : agent) (c : cand) :
  gwf G → hull_ok G cs → wcut_closed G cs →
  (∃ ev, ctrace_prefix (gx_hull G cs) c ev W ∧
         (∀ p s, cd_tr c !! p = Some s → gcut cs (ev p) = true) ∧
         wit_fence_ub G c ev W (x, gcnt x (cd_tr c))) →
  cpol_ctx G W x c.
Proof.
  intros Hwf Hok Hwc (ev & Hgt & Hcut & Hub).
  exists ev. split_and!;
    [by apply (ctrace_prefix_of_hull G cs)|exact Hub].
Qed.

(** ** 3.2 THE OBSTRUCTION, as an identity rather than a counterexample

    [ctp_wix] pins the log index of an appended write to its [gwix G].
    Since the candidate's log GROWS BY EXACTLY ONE at every write step, the
    clause forces the appended writes to be gmo-INCREASING.  So a candidate
    whose writes are appended out of gmo order is not a [ctrace_prefix] at
    all — there is no renaming to be tolerant of, and
    [WeakRvwmoFloor.gvis_ub] (which reads a log index [s] as
    [gwrite_at G s]) is where the demand comes from. *)
Lemma es_msg_len_w s :
  lb_is_w (es_lb s) = true → length (es_msg s) = 1%nat.
Proof.
  intros Hw. destruct (lb_is_w_wr _ Hw) as (base & vs & Hwr).
  by rewrite /es_msg Hwr.
Qed.

Theorem ctp_wix_gmo_mono G c ev W p q sp sq :
  ctrace_prefix G c ev W →
  cd_tr c !! p = Some sp → cd_tr c !! q = Some sq →
  lb_is_w (es_lb sp) = true → lb_is_w (es_lb sq) = true →
  (p < q)%nat → (gwix G (ev p) < gwix G (ev q))%nat.
Proof.
  intros Hgt Hp Hq Hwp Hwq Hpq.
  rewrite (ctp_wix G c ev W Hgt p sp Hp Hwp)
          (ctp_wix G c ev W Hgt q sq Hq Hwq).
  have H1 : length (cd_log c (S p)) = S (length (cd_log c p)).
  { rewrite (cd_log_S c p sp Hp) length_app (es_msg_len_w sp Hwp). lia. }
  have H2 : (length (cd_log c (S p)) ≤ length (cd_log c q))%nat
    := cd_log_len_le c (S p) q ltac:(lia).
  lia.
Qed.

(** The same fact in the form slice 3c consumes: the certified log IS a gmo
    prefix, so an exit write appended at candidate position [p] has
    [gwix G] equal to its log position. *)
Corollary cert_log_is_gmo_prefix G c ev W p s :
  ctrace_prefix G c ev W → cd_tr c !! p = Some s →
  lb_is_w (es_lb s) = true →
  gwrite_at G (S (length (cd_log c p))) = Some (ev p) ∧
  gwix G (ev p) = S (length (cd_log c p)).
Proof.
  intros Hgt Hs Hw.
  have Hix : gwix G (ev p) = S (length (cd_log c p))
    := ctp_wix G c ev W Hgt p s Hs Hw.
  split; [|exact Hix]. rewrite -Hix.
  apply gwrite_at_gwix, gwix_pos_elem. lia.
Qed.

(* ====================================================================== *)
(** * 4. THE CYCLE ITERATION *)

(** ** 4.1 The object that is threaded

    A certified configuration is a candidate together with the process and
    device supplies that make it a real promise-free run.  This is exactly
    the triple [cert_segment'] consumes and produces. *)
Record cyc_state : Type := CSt {
  cst_c : cand;
  cst_pst : nat → list pexv6;
  cst_dv : nat → dev_state;
}.

Definition cst_ok (d0 : dev_state) (S : cyc_state) : Prop :=
  srvwmo_consistent (cst_c S) ∧
  exec_prog_ok' pstep_ev pcls_ev (cst_pst S) (cst_dv S) (cand_exec (cst_c S)) ∧
  cst_dv S (cd_end (cst_c S)) = d0.

(** ** 4.2 One segment, and the walk

    [segout] records everything B2e-3c's kill arms need to ADDRESS a
    segment inside the final candidate: whose it is, which row segment it
    certifies, WHERE its appended steps start, and what they are. *)
Record segout : Type := SegOut {
  so_hart : agent;
  so_row  : list lbl;
  so_off  : nat;
  so_tr   : list estep;
}.

Definition seg_step (d0 : dev_state) (o : segout) (S S' : cyc_state) : Prop :=
  cst_ok d0 S ∧
  cst_ok d0 S' ∧
  so_off o = cd_end (cst_c S) ∧
  cd_tr (cst_c S') = cd_tr (cst_c S) ++ so_tr o ∧
  (∀ s, s ∈ so_tr o → es_ag s = so_hart o) ∧
  Forall2 lbl_reidx_w (so_row o) ((λ s, es_lb s) <$> so_tr o).

(** THE WALK.  Segment 1 is the one with the SUBSTITUTED entry (its source
    is gmo-above its own exit — the backward step); every later segment's
    entry reads the previous segment's exit, which the previous [seg_step]
    has already appended.  Both facts live in the [Ctx] the instantiation
    carries ([cpol_ctx], §3.1); the walk itself is bookkeeping. *)
Inductive segs_run (d0 : dev_state) : list segout → cyc_state → cyc_state → Prop :=
| segs_done S : cst_ok d0 S → segs_run d0 [] S S
| segs_more o l S S' S'' :
    seg_step d0 o S S' → segs_run d0 l S' S'' → segs_run d0 (o :: l) S S''.

Lemma segs_run_ok d0 l S S' : segs_run d0 l S S' → cst_ok d0 S' .
Proof. induction 1 as [S HS|o l S S' S'' Hst Hrun IH]; [exact HS|exact IH]. Qed.

Lemma segs_run_start d0 l S S' : segs_run d0 l S S' → cst_ok d0 S.
Proof.
  destruct 1 as [S HS|o l S S' S'' Hst _]; [exact HS|apply Hst].
Qed.

Lemma segs_run_prefix d0 l S S' :
  segs_run d0 l S S' → ∃ ext, cd_tr (cst_c S') = cd_tr (cst_c S) ++ ext.
Proof.
  induction 1 as [S HS|o l S S' S'' Hst Hrun IH].
  - exists []. by rewrite app_nil_r.
  - destruct IH as [ext Hext].
    destruct Hst as (_ & _ & _ & Htr & _).
    exists (so_tr o ++ ext). by rewrite Hext Htr app_assoc.
Qed.

(** THE POSITION FACT: every segment's appended steps sit at their recorded
    offset in the FINAL candidate — later segments only append. *)
Theorem segs_run_stable d0 l S S' :
  segs_run d0 l S S' →
  ∀ o, o ∈ l → ∀ k s, so_tr o !! k = Some s →
    cd_tr (cst_c S') !! (so_off o + k)%nat = Some s.
Proof.
  induction 1 as [S HS|o l S S' S'' Hst Hrun IH];
    intros o' Ho' k s Hk; [by apply elem_of_nil in Ho'|].
  apply elem_of_cons in Ho' as [->|Ho']; [|by apply IH].
  destruct Hst as (_ & _ & Hoff & Htr & _ & _).
  destruct (segs_run_prefix d0 l S' S'' Hrun) as [ext Hext].
  have Hlt : (so_off o + k < length (cd_tr (cst_c S')))%nat.
  { rewrite Htr length_app Hoff /cd_end.
    pose proof (lookup_lt_Some _ _ _ Hk). lia. }
  rewrite Hext (lookup_app_l _ ext _ Hlt) Htr.
  rewrite lookup_app_r; [|rewrite Hoff /cd_end; lia].
  rewrite Hoff /cd_end. by replace (length (cd_tr (cst_c S)) + k
    - length (cd_tr (cst_c S)))%nat with k by lia.
Qed.

(** … and every segment of the walk really was one [seg_step]. *)
Lemma segs_run_elem d0 l S S' :
  segs_run d0 l S S' → ∀ o, o ∈ l → ∃ S1 S2, seg_step d0 o S1 S2.
Proof.
  induction 1 as [S HS|o l S S' S'' Hst Hrun IH]; intros o' Ho';
    [by apply elem_of_nil in Ho'|].
  apply elem_of_cons in Ho' as [->|Ho']; [by exists S, S'|by apply IH].
Qed.

(** ** 4.3 THE INTERFACE IS INHABITED BY [cert_segment'']

    Nothing in §4.2 is specific to the certification: [seg_step] is exactly
    what [WeakRvwmoCert3.cert_segment''] delivers, with the carried context
    [Ctx] (intended: [cpol_ctx G W x], §3.1) coming along.

    MIGRATED to [cert_segment''] (§5b of [WeakRvwmoCert3]).  Three things
    change at this interface, and all three are what retires
    [WeakRvwmoWalk.wwit_vindep]:

      - THE NODE IS EXPOSED.  The reachability parameter [Nd : nat → M unit
        → Prop] is handed to the policy at every block ([Nd k m]), so a site
        datum about the monad NODE is dischargeable rather than assumed.
        Its two closure laws are [WeakRvwmoCert3.ndreach]'s own constructors,
        and the segment's EXIT node comes back reachable at the row position
        the segment ends at — which is what lets a walk carry [Nd] from one
        segment of a hart to the next.
      - THE INVARIANT IS [csync], NOT "the same node".  The acting hart's
        two runs may have parted company at a witness; they are back in
        LOCKSTEP at the end of any segment whose row ENDS IN A WRITE
        ([seg_locked]), which is exactly the walk's segment shape.
      - THE EMISSION MUST BE DEVICE-QUIET ([LDev ∉ es.*1]), which
        [WeakRvwmoSupply.em_devfree] supplies. *)
Theorem seg_step_of_segment (x : agent) (cpu : CPU) (d0 : dev_state)
    (T : list wreg) (Q : nat → lbl → Prop)
    (Ctx : nat → cand → Prop) (Cls : cand → lbl → Prop)
    (Nd : nat → M unit → Prop)
    (Hpres : ∀ (k : nat) (c0 : cand) (lb lb' : lbl),
        Ctx k c0 → srvwmo_consistent c0 → Q k lb → lbl_reidx_w lb lb' →
        mstep_ok (cand_last_st c0) x lb' → Cls c0 lb' →
        Ctx (S k) (cand_snoc c0 (EStep x lb')))
    (* the dependency-freedom of the segment's blocks: no block whose node
       the reachability admits reads a carrier the taint set holds.  At
       [T = []] it is free. *)
    (Hrds : ∀ (k : nat) (lb : lbl) (ws : wstate) (l : wlabel)
        (rds : list wreg) (wrs : list register)
        (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
        (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32),
        Q k lb → Nd k m →
        cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
        rds_ok (λ n, n ∉ T) rds)
    (Hrdsp : ∀ (k : nat) (lb : lbl) (ws : wstate) (l1 l2 : wlabel)
        (rds : list wreg) (wrs : list register)
        (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
        (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32),
        Q k lb → Nd k m →
        cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
        rds_ok (λ n, n ∉ T) rds)
    (* (N-D) the reachability parameter's two closure laws *)
    (HNdadm : ∀ (k : nat) (m m' : M unit) (rs rs' : regstate)
        (fn fn' : ofence) (ib ib' : oib32) (ls : list wlabel)
        (rds : list wreg) (wrs : list register) (ann : bool),
        Nd k m → (∀ l0, l0 ∈ ls → lb_admin true l0) →
        phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 → Nd k m')
    (HNdblk : ∀ (k : nat) (m m' : M unit) (ws : wstate) (lb : lbl)
        (l : wlabel) (rds : list wreg) (wrs : list register)
        (rs rs' : regstate) (fn fn' : ofence) (ib ib' : oib32),
        Nd k m → Q k lb →
        cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' → Nd (S k) m')
    (HNdblkp : ∀ (k : nat) (m m' : M unit) (ws : wstate) (lb : lbl)
        (l1 l2 : wlabel) (rds : list wreg) (wrs : list register)
        (rs rs' : regstate) (fn fn' : ofence) (ib ib' : oib32),
        Nd k m → Q k lb →
        cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
        Nd (S k) m')
    (* THE READ/REGISTER POLICY, at a block whose NODE is pinned by [Nd] *)
    (Hpol'' : ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
        (rds : list wreg) (wrs : list register)
        (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
        (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
        srvwmo_consistent c0 → Ctx k c0 → Q k lb →
        w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
        dreg_agree (λ n, n ∉ T) rs1 rs2 →
        rds_ok (λ n, n ∉ T) rds →
        Nd k m →
        cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
        ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence)
          (ib2' : oib32),
          cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
          mstep_ok (cand_last_st c0) x lb' ∧
          lbl_reidx_w lb lb' ∧
          Cls c0 lb' ∧
          csync T m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
          (lb_is_w lb = true →
             clockstep T m' rs1' fn' ib' m2' rs2' fn2' ib2'))
    (* (O-F) the pair policy — [WeakRvwmoCert3.cpolpr] *)
    (Hpolp : cpolpr x cpu d0 T Nd Ctx Cls Q)
    (k0 : nat) (ws0 : wstate) (rowseg : list lbl) (es : list eitem)
    (pfin : pexv6) (m0 : M unit) (rs10 : regstate) (fn0 : ofence)
    (ib0 : oib32) (St : cyc_state) (m20 : M unit) (rs20 : regstate)
    (fn20 : ofence) (ib20 : oib32) :
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  LDev ∉ es.*1 →
  (∀ i lb, rowseg !! i = Some lb → Q (k0 + i)%nat lb) →
  cst_ok d0 St →
  Ctx k0 (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x
    = Some (PHart cpu m20 rs20 fn20 ib20) →
  Nd k0 m0 →
  csync T m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    Ctx (k0 + length rowseg)%nat (cst_c St') ∧
    (** (O-E), carried through from [cert_segment'']'s own conclusion. *)
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat ∧
    (** THE CHAINING DATA, also [cert_segment'']'s own: where the acting
        hart's process ENDS (the emission's own final state, up to the
        taint AND up to a witness's divergence), what its release-pending
        bit becomes, and the FRAME for every other hart.  A walk whose
        invariant speaks of all harts at every state needs precisely
        these — and, since the walk's rows end in a write, [seg_locked]
        hands it back the LOCKSTEP it started with. *)
    (∃ (m1 : M unit) (rs11 : regstate) (fn1 : ofence) (ib1 : oib32)
       (m21 : M unit) (rs21 : regstate) (fn21 : ofence) (ib21 : oib32),
       pfin = PHart cpu m1 rs11 fn1 ib1 ∧
       cst_pst St' (cd_end (cst_c St')) !! x
         = Some (PHart cpu m21 rs21 fn21 ib21) ∧
       csync T m1 rs11 fn1 ib1 m21 rs21 fn21 ib21 ∧
       (seg_locked rowseg
          (clockstep T m0 rs10 fn0 ib0 m20 rs20 fn20 ib20) →
          clockstep T m1 rs11 fn1 ib1 m21 rs21 fn21 ib21) ∧
       Nd (k0 + length rowseg)%nat m1) ∧
    w_relp (ms_ws (cand_last_st (cst_c St')) x)
      = w_relp (row_ws_aux k0 ws0 rowseg) ∧
    (∀ y, y ≠ x →
       cst_pst St' (cd_end (cst_c St')) !! y
       = cst_pst St (cd_end (cst_c St)) !! y) ∧
    (∀ y, y ≠ x → w_relp (ms_ws (cand_last_st (cst_c St')) y)
                = w_relp (ms_ws (cand_last_st (cst_c St)) y)).
Proof.
  intros Hem Hdev HQ HS HCtx Hp Hnd Hsync Hrelp.
  destruct HS as (Hc & Hpo & Hdv).
  destruct (cert_segment'' x cpu d0 T Q Ctx Cls Hpres Nd Hrds Hrdsp
              HNdadm HNdblk HNdblkp Hpol'' Hpolp
              k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin Hem Hdev HQ
              m0 rs10 fn0 ib0 eq_refl Hnd
              (cst_c St) (cst_pst St) (cst_dv St) m20 rs20 fn20 ib20
              Hc HCtx Hpo Hp Hdv Hsync Hrelp)
    as (c' & pst' & dv' & tradd & m1 & rs11 & fn1 & ib1 &
        m21 & rs21 & fn21 & ib21 &
        Htr & Hagf & Hf2 & Hc' & HCtx' & Hpo' & Hp' & Hdv' & Hfin & Hsyncf
        & Hlockf & Hrelpf & Himg & Hpst0 & Hdv0 & Hfr & Hfrp & Hndf).
  exists (CSt c' pst' dv'), tradd.
  split; [|split_and!; [exact HCtx'|exact Himg|exact Hpst0|exact Hdv0
          |(exists m1, rs11, fn1, ib1, m21, rs21, fn21, ib21; split_and!;
              [exact Hfin|exact Hp'|exact Hsyncf|exact Hlockf|exact Hndf])
          |exact Hrelpf|exact Hfr|exact Hfrp]].
  split_and!; [split_and!; [exact Hc|exact Hpo|exact Hdv]| |done| | |];
    [split_and!; [exact Hc'|exact Hpo'|exact Hdv']
    |exact Htr|exact Hagf|exact Hf2].
Qed.

(* ====================================================================== *)
(** * 5. THE CYCLE'S GEOMETRY, THE THEOREM, AND NON-VACUITY *)

(** ** 5.1 The cycle, as data

    §4e's "[R]-cycle given as a list of SEGMENTS": each segment is one
    hart's stretch from an ENTRY event to an EXIT write, and consecutive
    segments are joined by a CROSS-HART [Racy] edge (rf/co/fr/ppo). *)
Record cyseg : Type := CySeg {
  cy_hart  : agent;
  cy_entry : geid;
  cy_exit  : geid;
}.

Definition cyseg_ok (o : cyseg) : Prop :=
  (cy_entry o).1 = cy_hart o ∧ (cy_exit o).1 = cy_hart o ∧
  ((cy_entry o).2 ≤ (cy_exit o).2)%nat.

Definition cy_link (G : gexec) (o1 o2 : cyseg) : Prop :=
  cy_hart o1 ≠ cy_hart o2 ∧ Racy G (cy_exit o1) (cy_entry o2).

Definition cycle_ok (G : gexec) (l : list cyseg) : Prop :=
  l ≠ [] ∧ Forall cyseg_ok l ∧
  (∀ j o1 o2, l !! j = Some o1 → l !! (S j) = Some o2 → cy_link G o1 o2) ∧
  (∀ o1 o2, l !! (length l - 1)%nat = Some o1 → l !! 0%nat = Some o2 →
            cy_link G o1 o2).

(** THE FIRST NON-VACUITY OBLIGATION: a ONE-segment "cycle" cannot exist —
    its wrap-around link would join a hart to itself, and the cycle's edges
    are cross-hart by construction. *)
Theorem cycle_two_segments G l : cycle_ok G l → (2 ≤ length l)%nat.
Proof.
  intros (Hne & _ & _ & Hwrap).
  destruct l as [|o l]; [by destruct Hne|].
  destruct l as [|o2 l]; [|simpl; lia]. exfalso.
  destruct (Hwrap o o eq_refl eq_refl) as [Hne2 _]. by apply Hne2.
Qed.

(** ** 5.2 THE BACKWARD STEP, and why its entry is a plain load

    The walk starts where the cycle goes BACKWARD in gmo ([WeakRvwmoAcyc]'s
    [caus_cycle_gviol] argument supplies such an index; here it is data).
    [WeakRvwmoCert3.witness_not_aq] then says the substituted entry cannot
    be an acquire — which is what lets [ctp_wit] write [aq = false]. *)
Definition cy_backward (G : gexec) (o : cyseg) : Prop :=
  gmo_lt G (cy_exit o) (cy_entry o).

Corollary cy_backward_not_aq G o :
  gppo_gmo G → gpo G (cy_entry o) (cy_exit o) →
  WeakRvwmoGraph.gmem G (cy_exit o) →
  glbl_is G (cy_entry o) lb_is_r →
  cy_backward G o →
  ¬ glbl_is G (cy_entry o) lb_aq.
Proof.
  intros Hppo Hpo Hmem Hr Hb Haq.
  exact (witness_not_aq G (cy_entry o) (cy_exit o) Hppo Hpo Hmem Hr Haq Hb).
Qed.

(** ** 5.3 [cert_cycle]

    THE THEOREM.  The walk's end is a real promise-free run at the quiet
    fabric, and every segment is ADDRESSABLE inside it: its appended steps
    at a known offset, its exit write with [G]'s own label (address, data
    and class), its entry read step at a known position.

    THE NARROWING (§3.2).  The candidate the walk builds is a
    [ctrace_prefix] only if its writes are appended in gmo order — the
    correspondence's own [ctp_wix] clause forces it ([ctp_wix_gmo_mono]),
    and [WeakRvwmoFloor.gvis_ub] is the consumer that demands it.  So the
    facts below are stated on the WALK, and the gmo-order hypothesis lives
    where the [Ctx] is instantiated (it is [Hpres]'s content, P-1); the
    general, out-of-gmo-order case is (O-A) in §6. *)
Theorem cert_cycle (d0 : dev_state) (l : list segout) (S0 Sf : cyc_state) :
  segs_run d0 l S0 Sf →
  (* (a) a real promise-free run at the quiet fabric *)
  srvwmo_consistent (cst_c Sf) ∧
  exec_prog_ok' pstep_ev pcls_ev (cst_pst Sf) (cst_dv Sf)
    (cand_exec (cst_c Sf)) ∧
  cst_dv Sf (cd_end (cst_c Sf)) = d0 ∧
  (* (b) every segment's steps at a known offset *)
  (∀ o, o ∈ l → ∀ k s, so_tr o !! k = Some s →
     cd_tr (cst_c Sf) !! (so_off o + k)%nat = Some s) ∧
  (* (c) every exit write, with G's label, at a known position *)
  (∀ o, o ∈ l → ∀ j rl base vs kc,
     so_row o !! j = Some (WeakAxiomatic.LStore rl base vs kc) →
     cd_tr (cst_c Sf) !! (so_off o + j)%nat
       = Some (EStep (so_hart o) (WeakAxiomatic.LStore rl base vs kc))) ∧
  (* (d) every appended step is the certifying hart's, and the row
         correspondence survives *)
  (∀ o, o ∈ l → (∀ s, s ∈ so_tr o → es_ag s = so_hart o) ∧
                Forall2 lbl_reidx_w (so_row o) ((λ s, es_lb s) <$> so_tr o)).
Proof.
  intros Hrun.
  destruct (segs_run_ok d0 l S0 Sf Hrun) as (Hc & Hpo & Hdv).
  have Hseg : ∀ o, o ∈ l → (∀ s, s ∈ so_tr o → es_ag s = so_hart o) ∧
                 Forall2 lbl_reidx_w (so_row o) ((λ s, es_lb s) <$> so_tr o).
  { intros o Ho.
    destruct (segs_run_elem d0 l S0 Sf Hrun o Ho)
      as (S1 & S2 & (_ & _ & _ & _ & Hag & Hf2)).
    split; [exact Hag|exact Hf2]. }
  split_and!; [exact Hc|exact Hpo|exact Hdv
              |exact (segs_run_stable d0 l S0 Sf Hrun)| |exact Hseg].
  intros o Ho j rl base vs kc Hj.
  destruct (Hseg o Ho) as [Hag Hf2].
  apply (segs_run_stable d0 l S0 Sf Hrun o Ho).
  by apply (seg_exit_write (so_hart o) (so_row o) (so_tr o) j).
Qed.

(** The entry read's position, in the form the export seam consumes: an
    appended step of a segment is a step of the FINAL candidate at a known
    index, so a [prot_read] record minted at a segment's entry is minted at
    that index. *)
Corollary cert_cycle_pos (d0 : dev_state) (l : list segout) (S0 Sf : cyc_state)
    (o : segout) (j : nat) (lb : lbl) :
  segs_run d0 l S0 Sf → o ∈ l →
  so_tr o !! j = Some (EStep (so_hart o) lb) →
  cd_tr (cst_c Sf) !! (so_off o + j)%nat = Some (EStep (so_hart o) lb).
Proof. intros Hrun Ho Hj. by apply (segs_run_stable d0 l S0 Sf Hrun o Ho). Qed.

(** ** 5.4 THE EXIT WRITE'S MESSAGE, AT A KNOWN LOG POSITION

    B2e-3c's kill arms read the exit write as a MESSAGE, not as a row
    position.  A store step at candidate position [p] contributes exactly
    one message, at log index [length (cd_log c p)], and it stays there. *)
Lemma exit_msg_in_log (c : cand) (p : nat) (x : agent)
    (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class) :
  cd_tr c !! p = Some (EStep x (WeakAxiomatic.LStore rl base vs kc)) →
  ∀ q, (S p ≤ q)%nat →
    cd_log c q !! (length (cd_log c p)) = Some (WMsg base vs (Some x) kc).
Proof.
  intros Hp q Hq.
  have Hs : cd_log c (S p) = cd_log c p ++ [WMsg base vs (Some x) kc].
  { by rewrite (cd_log_S c p _ Hp). }
  destruct (cd_log_split c (S p) q Hq) as [ext Hext].
  rewrite Hext Hs -app_assoc.
  rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag.
Qed.

Corollary cert_cycle_exit_msg (d0 : dev_state) (l : list segout)
    (S0 Sf : cyc_state) (o : segout) (j : nat)
    (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class) :
  segs_run d0 l S0 Sf → o ∈ l →
  so_row o !! j = Some (WeakAxiomatic.LStore rl base vs kc) →
  cd_log_end (cst_c Sf) !! (length (cd_log (cst_c Sf) (so_off o + j)))
  = Some (WMsg base vs (Some (so_hart o)) kc).
Proof.
  intros Hrun Ho Hj.
  destruct (cert_cycle d0 l S0 Sf Hrun) as (_ & _ & _ & _ & Hex & _).
  have Hp := Hex o Ho j rl base vs kc Hj.
  rewrite /cd_log_end /cd_end.
  apply (exit_msg_in_log (cst_c Sf) (so_off o + j) (so_hart o)
           rl base vs kc Hp).
  pose proof (lookup_lt_Some _ _ _ Hp). lia.
Qed.

(** ** 5.5 APPENDING ONE MORE SEGMENT

    The walk grows at its END — "append one more segment, whose entry reads
    the previous exit truly": the truth of that read is [src_in_log], which
    §5.4 supplies as data (the previous exit's message IS in the log the
    next segment starts from), and the admissibility is
    [WeakRvwmoCert3.cpol_read] through the carried [Ctx]. *)
Lemma segs_run_snoc d0 l o S S' S'' :
  segs_run d0 l S S' → seg_step d0 o S' S'' → segs_run d0 (l ++ [o]) S S''.
Proof.
  induction 1 as [S1 HS1|o1 l1 S1 S2 S3 Hst Hrun IH]; intros Hstep.
  - apply (segs_more d0 o [] S1 S'' S''); [exact Hstep|].
    apply segs_done. by destruct Hstep as (_ & HS & _).
  - rewrite -app_comm_cons.
    apply (segs_more d0 o1 (l1 ++ [o]) S1 S2 S''); [exact Hst|by apply IH].
Qed.

(** ** 5.6 NON-VACUITY: one REAL segment in the walk

    [WeakRvwmoCert3]'s [sw &started] block, re-run through §4.3's interface
    and placed in a one-element [segs_run].  This is the per-segment
    iteration instantiated at a real emission, for a ONE-HART prefix. *)
Section nonvacuity4.
  Context (cpu : CPU) (rs : regstate) (ib : oib32) (d0 : dev_state).

  Notation img0 := (λ _ : Z, @None (bv 8)).

  Definition nv4_S0 : cyc_state :=
    CSt (sm_c img0) (sm_pst cpu rs ib) (sm_dv d0).

  Lemma nv4_S0_ok : cst_ok d0 nv4_S0.
  Proof.
    split_and!;
      [apply (sm_consistent img0)|apply (sm_prog0 img0 cpu rs ib d0)
      |reflexivity].
  Qed.

  Theorem segs_run_witness :
    ∃ (Sf : cyc_state) (tradd : list estep),
      segs_run d0 [SegOut 0%nat ev_row 0%nat tradd] nv4_S0 Sf ∧
      cd_tr (cst_c Sf) !! 0%nat
      = Some (EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                             (wbytes 4 WeakLock.lock_one) WCplain)).
  Proof.
    have Hrds0 : ∀ rds : list wreg, rds_ok (λ n, n ∉ []) rds.
    { intros rds n _. apply not_elem_of_nil. }
    have Hpol : ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
        (rds : list wreg) (wrs : list register)
        (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib0 : oib32)
        (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
        srvwmo_consistent c0 → True → lb_store_ne lb →
        w_relp (ms_ws (cand_last_st c0) 0%nat) = w_relp ws →
        dreg_agree (λ n, n ∉ []) rs1 rs2 →
        rds_ok (λ n, n ∉ []) rds →
        True →
        cblk cpu d0 ws lb l rds wrs m rs1 fn ib0 m' rs1' fn' ib' →
        ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence)
          (ib2' : oib32),
          cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib0 m2' rs2' fn2' ib2' ∧
          mstep_ok (cand_last_st c0) 0%nat lb' ∧
          lbl_reidx_w lb lb' ∧
          True ∧
          csync [] m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
          (lb_is_w lb = true →
             clockstep [] m' rs1' fn' ib' m2' rs2' fn2' ib2').
    { intros k c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib'
        Hc _ Hlb Hrelp Hag _ _ Hblk.
      destruct (pol_store' 0%nat cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib0
                  m' rs1' fn' ib' Hc Hlb Hrelp Hag Hblk)
        as (lb' & l' & rds' & wrs' & rs2' & H1 & H2 & H3 & _ & H5).
      exists lb', l', rds', wrs', rs2', m', fn', ib'.
      split_and!; [exact H1|exact H2|exact H3|exact I| |intros _];
        [left|]; by split_and!. }
    destruct (seg_step_of_segment 0%nat cpu d0 [] (λ _ : nat, lb_store_ne)
                (λ (_ : nat) (_ : cand), True) (λ _ _, True)
                (λ (_ : nat) (_ : M unit), True)
                (λ k c0 lb lb' _ _ _ _ _ _, I)
                (λ k lb ws l rds wrs m rs1 fn ib0 m' rs1' fn' ib' _ _ _,
                   Hrds0 rds)
                (λ k lb ws l1 l2 rds wrs m rs1 fn ib0 m' rs1' fn' ib' _ _ _,
                   Hrds0 rds)
                (λ k m m' rs1 rs1' fn fn' ib0 ib' ls rds wrs ann _ _ _, I)
                (λ k m m' ws lb l rds wrs rs1 rs1' fn fn' ib0 ib' _ _ _, I)
                (λ k m m' ws lb l1 l2 rds wrs rs1 rs1' fn fn' ib0 ib' _ _ _, I)
                Hpol
                (cpolpr_of_cpolp 0%nat cpu d0 []
                   (λ (_ : nat) (_ : M unit), True)
                   (λ (_ : nat) (_ : cand), True) (λ _ _, True)
                   (λ _ : nat, lb_store_ne)
                   (cpolp_of_rmwfree 0%nat cpu d0 []
                      (λ (_ : nat) (_ : cand), True) (λ _ _, True)
                      (λ _ : nat, lb_store_ne)
                      (λ _ lb Hlb, lb_store_ne_rmwfree lb Hlb)))
                0%nat ws_init ev_row _ _
                ev_x2.2 rs None ib nv4_S0 ev_x2.2 rs None ib
                (nv_hemit cpu rs ib d0)
                (ev_em_devfree cpu rs ib)
                (λ i lb Hi, Forall_lookup_1 lb_store_ne ev_row i lb
                              nv_row_class Hi)
                nv4_S0_ok I eq_refl I
                ltac:(left; split_and!;
                        [reflexivity|reflexivity|reflexivity
                        |apply dreg_agree_refl])
                ltac:(by rewrite (sm_ws img0)))
      as (Sf & tradd & Hstep & _).
    exists Sf, tradd. split.
    - eapply segs_more; [exact Hstep|].
      apply segs_done. destruct Hstep as (_ & HS' & _). exact HS'.
    - destruct Hstep as (_ & _ & _ & Htr & Hag & Hf2).
      have H0 : cd_tr (cst_c nv4_S0) = [] by reflexivity.
      rewrite Htr H0 app_nil_l.
      by apply (seg_exit_write 0%nat ev_row tradd 0%nat).
  Qed.
End nonvacuity4.

(** ** 5.7 WHY THERE IS NO 2-HART CYCLE WITNESS YET — recorded

    A cycle needs at least two DISTINCT harts ([cycle_two_harts], from the
    cross-hart links), while the only emitted block this tree has is
    [WeakRvwmoConfWit]'s single [sw &started], and the witness supply
    accordingly carries exactly ONE hart ([nv4_one_hart]).  So the
    one-segment instantiation of §5.6 is as far as non-vacuity can go
    without a second emitted block; a genuine two-hart cycle witness is
    priced as a follow-up, exactly as [WeakRvwmoLockWit] was for
    [cs_kill]. *)
Lemma cycle_two_harts G l :
  cycle_ok G l → ∃ o1 o2, o1 ∈ l ∧ o2 ∈ l ∧ cy_hart o1 ≠ cy_hart o2.
Proof.
  intros Hok. pose proof (cycle_two_segments G l Hok) as Hlen.
  destruct Hok as (_ & _ & Hcons & _).
  destruct (lookup_lt_is_Some_2 l 0%nat ltac:(lia)) as [o1 H1].
  destruct (lookup_lt_is_Some_2 l 1%nat ltac:(lia)) as [o2 H2].
  exists o1, o2. split_and!;
    [by eapply elem_of_list_lookup_2|by eapply elem_of_list_lookup_2|].
  by destruct (Hcons 0%nat o1 o2 H1 H2) as [Hne _].
Qed.

Lemma nv4_one_hart (cpu : CPU) (rs : regstate) (ib : oib32) (d0 : dev_state)
    (k : nat) : length (cst_pst (nv4_S0 cpu rs ib d0) k) = 1%nat.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** * 6. WHAT THIS SLICE LEAVES OPEN

    Nothing below is [Admitted]; these are the statements this file does NOT
    make, so that B2e-3c inherits an exact list.  (P-1)–(P-4) of
    [WeakRvwmoCert3] §7 are inherited unchanged.

    (O-A) THE OUT-OF-GMO-ORDER CYCLE.  §3.2 shows that a candidate whose
          writes are appended out of gmo order is NOT a
          [WeakRvwmoCert3.ctrace_prefix] of [G] — [ctp_wix] pins the log
          index of a write to its [gwix G], and the log grows by exactly one
          per write step, so the appended writes are necessarily
          gmo-increasing ([ctp_wix_gmo_mono]).  A renamed variant
          ([ctrace_prefix] up to [lbl_ren rho] on the log indices) does NOT
          rescue the floor: [WeakRvwmoFloor.gvis_ub] READS a log index [s]
          as [gwrite_at G s], so the certification would have to be
          re-proved against a renamed [gvis_ub], i.e. against a renamed
          graph.  THE OBLIGATION, for the general case: either certify in a
          gmo-respecting order rather than cycle order (§4e's own fallback —
          the two orders agree on the read-pinned pairs the kill needs), or
          restate [WeakRvwmoFloor]'s whole floor over a renamed write
          index.  This file takes the first branch by stating the walk's
          facts without a [ctrace_prefix] claim on the walk's own writes;
          the milestone's kill arms are stated for a log that IS a gmo
          prefix.

    (O-B) [wcut_closed] (§2.2) is a HYPOTHESIS on the causal past's cut.
          [WeakRvwmoHull.hull_ok] does not imply it (it is po-closure +
          rf-closure; there is no [co] clause), and [WeakRvwmoHull.gx_hull]
          renames precisely because of that.  Where the cycle's causal past
          is CHOSEN (B2e-3c), taking the cut gmo-downward-closed on writes
          is free — closing a cut downward in gmo adds writes and preserves
          [hull_ok] — but it must be DONE, and the [proper_cut] measure
          argument re-checked at the closed cut.

    (O-C) THE [Ctx] INSTANTIATION.  §4.3 hands [cert_segment'] its context
          abstractly; instantiating [Ctx := cpol_ctx G W x] needs
          [WeakRvwmoCert3] (P-1) ([Hpres], the ctrace bookkeeping) and the
          per-segment witness set [W] (segment 1's entry, plus its
          poloc-later reads — [W_poloc_closed]).  §3.1 supplies the hull
          half of that context; the per-segment half is B2e-3c's.

    (O-D) NO [gtrace_prefix] IS EXPORTED FOR A LINEARIZATION.
          [WeakRvwmoLin2]'s [tprefix]/[tfull] — "the candidate of a
          [ptrace_ext] trace IS a [gtrace_prefix]" — are [Local] to that
          file's [Section Trace], so §3.1's transfer cannot be COMPOSED with
          [gtrace_linearization] from a leaf; only its exported conclusions
          (consistency, image, rows, full log) are visible.  Exporting
          [tfull] from [WeakRvwmoLin2] is a one-line change there and is the
          cheapest way to close the chain "acyclic hull ⇒ realized
          [ctrace_prefix] of [G]"; it is not done here because this slice is
          a new leaf. *)

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions filter_downward_prefix.
Print Assumptions hull_realizable_rows_G.
Print Assumptions wcut_closed_prefix.
Print Assumptions hull_gwix_eq.
Print Assumptions hren_id.
Print Assumptions gxh_lbl_eq.
Print Assumptions ctrace_prefix_of_hull.
Print Assumptions cpol_ctx_of_hull.
Print Assumptions ctp_wix_gmo_mono.
Print Assumptions cert_log_is_gmo_prefix.
Print Assumptions segs_run_stable.
Print Assumptions seg_step_of_segment.
Print Assumptions cycle_two_segments.
Print Assumptions cy_backward_not_aq.
Print Assumptions cert_cycle.
Print Assumptions cert_cycle_pos.
Print Assumptions exit_msg_in_log.
Print Assumptions cert_cycle_exit_msg.
Print Assumptions segs_run_snoc.
Print Assumptions segs_run_witness.
Print Assumptions cycle_two_harts.
