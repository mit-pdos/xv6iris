(** * WeakRvwmoWalk.v — R-2: THE CERTIFICATION WALK

    Design: [claude-notes/design/weak-memory-route-b.md] §4e ("SLICE 3's
    SHAPE", "SLICES 2b/3, STATED") and §4f; the EIGHTH-PASS checkpoint
    item 1 of [claude-notes/projects/weak-memory-certification.md].

    [WeakRvwmoGlue2] reduces the glue's (G-3) to ONE named supply,
    [walk_supply]: from a consistent, [gdexec_qconf]-conformant graph,
    hand back a [WeakRvwmoCert4.segs_run] whose endpoint boots from
    [boot]/[d0], carries the graph's image, and whose LOG is
    [WeakRvwmoKillArms.log_of] of the WHOLE graph.  This leaf builds that
    walk.

    ------------------------------------------------------------------------
    THE SHAPE, and why it is an iteration over WRITES and not over the
    cycle's segments.

    [walk_supply]'s conclusion is a full-graph [log_of]: "the certified
    candidate's log IS the graph's whole write list, in gmo order".  The
    cycle's own segments are not enough for that — they cover the cycle,
    not the graph — and the order is not free either:
    [WeakRvwmoGlue2.walk_exits_gmo_forced] shows the exit writes of a walk
    whose endpoint is a [ctrace_prefix] are appended in strictly increasing
    [gwix].  So the walk processes the graph's WRITES IN GMO ORDER, one
    segment per write: at log length [n] the next segment runs the hart of
    [G]'s [(n+1)]-st write from its current position through that write.
    [WeakRvwmoGlue.l2_claim_at] is per-segment and reads only the FINAL
    log, so the cycle's own order is never needed (that is (O-A)'s cheap
    branch, recorded at [walk_exits_gmo_forced]).

    THE START IS FREE.  [WeakRvwmoGlue2] §2 found that [cut_supply] is
    discharged by the ZERO cut, at which [WeakRvwmoGlue.hull_run] hands
    back the EMPTY candidate.  So the walk starts at the empty trace over
    [gx_img G] with [pst] constantly [boot <$> seq 0 N] — [cst_ok] there is
    two [reflexivity]s ([wlk_start_inv]) — and the [run_data] premise
    [walk_supply] carries is not consumed at all.

    ------------------------------------------------------------------------
    WHAT IS HERE.

      §1  THE LOG PREFIX.  [wlog_pfx G n log] — "[log] is the message list
          of [G]'s first [n] writes" — with its [nil]/[snoc] steps and
          [log_of_of_pfx]: at [n = length (gwrites G)] it IS [log_of].
          Note it needs no [gwf]: both directions of [log_of] are the two
          directions of the array indexing.

      §2  THE WALK ENGINE.  [wlk_inv] (the invariant the walk maintains),
          [wlk_step] (one segment, one write), [wlk_run] (the induction on
          the writes that remain), and [walk_supply_of_steps] — the
          theorem: a per-state segment supply IS a [walk_supply].  All
          [Qed], no hypothesis about the kernel.

      §3  THE SEGMENT'S LOG ARITHMETIC.  A certified segment appends
          exactly one message, and it is the exit write's:
          [seg_step_msgs] / [wlk_step_of_seg].  This is where
          [WeakRvwmoCert2.lbl_reidx] is used in the direction that matters
          — a store is related to ITSELF, so the exit message is [G]'s own.
          Also [hemit_app] (§3.1): a row's emission splits at every prefix,
          which is what makes "hart [x]'s stretch from its current position
          through its next write" a [hemit] the segment machinery accepts.

      §4  THE POLICY.  [wlk_seg_of_cert] — the segment IS what
          [WeakRvwmoCert3.cert_segment'] delivers at
          [Ctx := cpol_ctx G W x], with (P-1) discharged through
          [WeakRvwmoGlue2.cpol_Hpres] and the TWO HONEST PREMISES quantified
          where they are honestly stated: (P-3) [wit_fence_ub] at the next
          position, and the read policy [Hpol'] itself — which §4.0c
          DISCHARGES ([wpol_of_sites]), on both routes: [G]'s own label at
          a non-witness position, the candidate's latest-source read at a
          witness one.  [walk_policy] bundles the per-state supply;
          [walk_supply_of_policy] is the theorem.

      §4.5–§4.6  THE CHAINED WALK.  §4.1–§4.4 build ONE segment at ONE
          state; chaining them generically needs two changes.  (a) THE
          WITNESS SET IS FROZEN: [cpol_ctx G (wwit G n) x] cannot be
          carried across a step, because [wwit G n] shrinks with [n] while
          [ctrace_prefix] is not monotone in that direction (a substituted
          position carries the candidate's LATEST-source read, not [G]'s
          label, so the [¬ W] arm cannot take over when the position leaves
          [W]).  So the walk carries ONE set [W] throughout, and [wwit G n]
          survives only inside the per-position SITE DATUM [wsite_cls].
          (b) THE INVARIANT CARRIES THE PROCESS STATES: [wlk_inv'] records,
          for every hart, its emission from its current row position
          ([wemit]), the walk state's process identified with it
          ([pex_dag]), its release-pending fold, and the ROW-POSITION
          BOUNDARY ([wpos_lo]/[wpos_hi]).  [wlk_step'_of_supply] then
          DERIVES the whole per-state datum — which write, whose, where the
          hart stands, that nothing between is a write, the site data, the
          emission — from a per-GRAPH datum [wsupply], and
          [walk_supply_of_sites] is the theorem.

      §5  THE CAPSTONE SHAPE, restated: [cycle_kill_of_l2''''],
          [t2lin_of_l2'''] and [xv6_rvwmo_safe_modulo_walk] — the capstone
          with (R-2) replaced by the policy.  The capstone file is NOT
          edited.

      §6  the audit, §7 the ledger.

    Nothing below is [Admitted] or [Axiom]-ed. *)
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
Require Import WeakRvwmoCapstone.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE LOG PREFIX

    [WeakRvwmoKillArms.log_of] is an equivalence between log positions and
    graph write indices ("log position [p] IS write index [S p]").  The
    walk reaches it one write at a time, so the invariant is its PREFIX
    form. *)

Definition wlog_pfx (G : gexec) (n : nat) (log : list wmsg) : Prop :=
  length log = n ∧
  ∀ p w, (p < n)%nat → gwrite_at G (S p) = Some w → gmsg G w = log !! p.

Lemma wlog_pfx_nil G : wlog_pfx G 0%nat [].
Proof. split; [done|]. intros p w Hp. lia. Qed.

Lemma wlog_pfx_snoc G n log w m :
  wlog_pfx G n log →
  gwrite_at G (S n) = Some w → gmsg G w = Some m →
  wlog_pfx G (S n) (log ++ [m]).
Proof.
  intros [Hlen Hpfx] Hw Hm. split; [rewrite length_app /=; lia|].
  intros p w' Hp Hw'.
  destruct (decide (p < n)%nat) as [Hlt|Hlt].
  - rewrite lookup_app_l; [|lia]. by apply Hpfx.
  - have Hpn : p = n by lia. subst p.
    rewrite Hw in Hw'. injection Hw' as <-.
    rewrite lookup_app_r; [|lia]. rewrite Hlen Nat.sub_diag /=. exact Hm.
Qed.

(** THE PAYOFF: at the full write count the prefix IS [log_of].  Both
    directions are the two directions of the array indexing, so no
    well-formedness hypothesis is involved. *)
Theorem log_of_of_pfx G log :
  wlog_pfx G (length (gwrites G)) log → log_of G log.
Proof.
  intros [Hlen Hpfx] p m. split.
  - intros Hp.
    have Hlt : (p < length (gwrites G))%nat
      by (pose proof (lookup_lt_Some _ _ _ Hp); lia).
    destruct (lookup_lt_is_Some_2 (gwrites G) p Hlt) as [w Hw].
    exists w. split; [exact Hw|]. rewrite (Hpfx p w Hlt Hw) //.
  - intros (w & Hw & Hm).
    have Hlt : (p < length (gwrites G))%nat
      by (rewrite /gwrite_at in Hw; pose proof (lookup_lt_Some _ _ _ Hw); lia).
    rewrite -(Hpfx p w Hlt Hw) //.
Qed.

(* ====================================================================== *)
(** * 2. THE WALK ENGINE

    The invariant a walk state carries, one step of the walk, and the
    induction that runs it to the end.  Nothing in this section mentions
    the kernel, the emission or the read policy: it is the ORDER
    ARGUMENT — writes in gmo order, one segment each — and it is
    everything the [log_of] conclusion needs. *)

Definition wlk_inv (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (St : cyc_state) (n : nat) : Prop :=
  cst_ok d0 St ∧
  cd_img (cst_c St) = gx_img G ∧
  cst_pst St 0%nat = boot <$> seq 0 N ∧
  cst_dv St 0%nat = d0 ∧
  wlog_pfx G n (cd_log_end (cst_c St)).

(** ONE STEP: a certified segment whose appended messages are exactly the
    one message of [G]'s [(n+1)]-st write.

    THE THREE BOOKKEEPING CLAUSES (image, [pst 0], [dv 0]) are true BY
    CONSTRUCTION of [WeakRvwmoCert3.cert_segment'] — it builds its output by
    [cand_snoc]/[pst_snoc]/[dv_snoc], none of which touches the image or
    index 0 — and (O-E) is now CLOSED: [cert_segment'] STATES all three, so
    §4.1 delivers them and nothing supplies them by hand. *)
Definition wlk_step (G : gexec) (d0 : dev_state) (St : cyc_state) (n : nat)
    : Prop :=
  ∃ (o : segout) (S' : cyc_state) (w : geid) (m : wmsg),
    seg_step d0 o St S' ∧
    cd_img (cst_c S') = cd_img (cst_c St) ∧
    cst_pst S' 0%nat = cst_pst St 0%nat ∧
    cst_dv S' 0%nat = cst_dv St 0%nat ∧
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some m ∧
    cd_log_end (cst_c S') = cd_log_end (cst_c St) ++ [m].

Lemma wlk_inv_step boot d0 N G St n :
  wlk_inv boot d0 N G St n →
  wlk_step G d0 St n →
  ∃ o S', seg_step d0 o St S' ∧ wlk_inv boot d0 N G S' (S n).
Proof.
  intros (Hok & Himg & Hpst & Hdv & Hlog)
         (o & S' & w & m & Hst & Himg' & Hpst' & Hdv' & Hw & Hm & Hlog').
  exists o, S'. split; [exact Hst|]. split_and!.
  - by destruct Hst as (_ & ? & _).
  - by rewrite Himg' Himg.
  - by rewrite Hpst' Hpst.
  - by rewrite Hdv' Hdv.
  - rewrite Hlog'. by eapply wlog_pfx_snoc.
Qed.

(** THE ITERATION.  [k] is the number of writes that remain; the supply is
    consumed once per write. *)
Lemma wlk_run boot d0 N G (Hsup : ∀ St n, wlk_inv boot d0 N G St n →
                             (n < length (gwrites G))%nat → wlk_step G d0 St n)
    (k : nat) :
  ∀ n St, wlk_inv boot d0 N G St n → (n + k)%nat = length (gwrites G) →
    ∃ l Sf, segs_run d0 l St Sf ∧ wlk_inv boot d0 N G Sf (length (gwrites G)).
Proof.
  induction k as [|k IH]; intros n St Hinv Hn.
  - exists [], St. split.
    + apply segs_done. by destruct Hinv as (? & _).
    + by replace (length (gwrites G)) with n by lia.
  - destruct (wlk_inv_step boot d0 N G St n Hinv
                (Hsup St n Hinv ltac:(lia))) as (o & S' & Hst & Hinv').
    destruct (IH (S n) S' Hinv' ltac:(lia)) as (l & Sf & Hrun & Hfin).
    exists (o :: l), Sf. split; [|exact Hfin]. by eapply segs_more.
Qed.

(** ** 2.1 THE START: the empty candidate over the graph's image

    [WeakRvwmoGlue2] §2's finding, used: the zero cut's hull is the empty
    program, so the walk may start from the empty trace — and there
    [cst_ok] is free at EVERY process supply, because [exec_prog_ok']
    quantifies over the trace's positions and there are none. *)
Definition wlk_start (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) : cyc_state :=
  CSt (Cand (gx_img G) []) (λ _, boot <$> seq 0 N) (λ _, d0).

Lemma wlk_start_inv boot d0 N G : wlk_inv boot d0 N G (wlk_start boot d0 N G) 0%nat.
Proof.
  split_and!.
  - split_and!.
    + apply srvwmo_of_wf, cand_reachable. intros k s Hs. by destruct k.
    + intros k s Hs. rewrite cand_ex_tr in Hs. by destruct k.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply wlog_pfx_nil.
Qed.

(** ** 2.2 THE THEOREM: a per-state segment supply IS a [walk_supply] *)

Definition walk_steps (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) : Prop :=
  ∀ St n, wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
         wlk_step G d0 St n.

Theorem walk_supply_of_steps (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     walk_steps boot d0 N (gd_g GD)) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hsup GD cs c0 pst0 z ss Hcons Hq Hcut Hrd0 Hne Hch.
  destruct (wlk_run boot d0 N (gd_g GD) (Hsup GD Hcons Hq)
              (length (gwrites (gd_g GD))) 0%nat
              (wlk_start boot d0 N (gd_g GD))
              (wlk_start_inv boot d0 N (gd_g GD)) ltac:(lia))
    as (l & Sf & Hrun & Hok & Himg & Hpst & Hdv & Hlog).
  exists l, (wlk_start boot d0 N (gd_g GD)), Sf.
  split_and!; [exact Hrun|exact Himg|exact Hpst|exact Hdv|].
  rewrite -/(cd_end (cst_c Sf)) -/(cd_log_end (cst_c Sf)).
  by apply log_of_of_pfx.
Qed.

(* ====================================================================== *)
(** * 3. THE SEGMENT'S LOG ARITHMETIC

    §2's [wlk_step] asks for a segment that appends EXACTLY ONE message,
    the exit write's.  That is a fact about the segment's ROW, and it is
    where [WeakRvwmoCert2.lbl_reidx] earns its shape: a certified step's
    label may differ from [G]'s in its read INDICES and in nothing else, so
    a read stays a read (contributing no message) and the exit STORE comes
    back verbatim ([lbl_reidx_store]).  A segment is therefore
    "non-writes, then one store", and its message list is a singleton. *)

(** ** 3.1 A row's emission SPLITS at every prefix

    "Hart [x]'s stretch from its current position through its next write"
    is a [take]/[drop] of the hart's row, and [WeakRvwmoSupply.gdexec_qconf]
    hands out an emission of the WHOLE row.  [hemit] is an append: the
    items concatenate, the fabric index advances by the prefix's length and
    the [wstate] index by the row fold. *)
Lemma hemit_app dv k ws row1 row2 p es pfin :
  hemit dv k ws (row1 ++ row2) p es pfin →
  ∃ (pm : pexv6) (es1 es2 : list eitem),
    hemit dv k ws row1 p es1 pm ∧
    hemit dv (k + length row1)%nat (row_ws_aux k ws row1) row2 pm es2 pfin ∧
    es = es1 ++ es2.
Proof.
  revert k ws p es. induction row1 as [|lb row1 IH]; intros k ws p es Hem.
  { exists p, [], es. rewrite Nat.add_0_r /=. split_and!;
      [apply HEnil|exact Hem|done]. }
  rewrite -app_comm_cons in Hem. inversion Hem as
    [ |k' ws' lb' row' p' ls pa da l p'' es' pfin' Har Hre Hst Hem' Hk
     |k' ws' lb' row' p' ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p'' es' pfin'
      Har1 Hre Hst1 Har2 Hst2 Hem' Hk]; subst.
  - destruct (IH (S k) (lbl_post k ws lb) p'' es' Hem')
      as (pm & es1 & es2 & H1 & H2 & ->).
    exists pm, (eadm ls ++ (l, Some k) :: es1), es2. split_and!.
    + eapply HEone; [exact Har|exact Hre|exact Hst|exact H1].
    + rewrite /= -Nat.add_succ_comm. exact H2.
    + by rewrite -app_assoc.
  - destruct (IH (S k) (lbl_post k ws lb) p'' es' Hem')
      as (pm' & es1 & es2 & H1 & H2 & ->).
    exists pm', (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es1),
           es2. split_and!.
    + eapply HEpair; [exact Har1|exact Hre|exact Hst1|exact Har2|exact Hst2
                     |exact H1].
    + rewrite /= -Nat.add_succ_comm. exact H2.
    + by rewrite -app_assoc -app_comm_cons -app_assoc.
Qed.

(** ** 3.2 A non-write step contributes no message *)

Lemma es_msg_notw (s : estep) : lb_is_w (es_lb s) = false → es_msg s = [].
Proof. rewrite /es_msg. by destruct (es_lb s). Qed.

Lemma tr_msgs_notw (tr : list estep) :
  Forall (λ s, lb_is_w (es_lb s) = false) tr → tr_msgs tr = [].
Proof.
  induction 1 as [|s tr Hs _ IH]; [done|].
  by rewrite /= (es_msg_notw s Hs) IH.
Qed.

(** ** 3.3 A [seg_step]'s log grows by its trace's messages *)
Lemma seg_step_log d0 o St St' :
  seg_step d0 o St St' →
  cd_log_end (cst_c St') = cd_log_end (cst_c St) ++ tr_msgs (so_tr o).
Proof.
  intros (_ & _ & _ & Htr & _ & _).
  by rewrite !cd_log_end_full Htr tr_msgs_app.
Qed.

(** ** 3.4 A "non-writes, then one store" segment appends ONE message *)
Theorem seg_step_msgs d0 (o : segout) (St St' : cyc_state)
    (pre : list lbl) (rl : bool) (base : Z) (vs : list (bv 8))
    (kc : wm_class) :
  seg_step d0 o St St' →
  so_row o = pre ++ [WeakAxiomatic.LStore rl base vs kc] →
  Forall (λ lb, lb_is_w lb = false) pre →
  cd_log_end (cst_c St')
  = cd_log_end (cst_c St) ++ [WMsg base vs (Some (so_hart o)) kc].
Proof.
  intros Hst Hrow Hpre.
  pose proof Hst as (_ & _ & _ & _ & Hag & Hf2).
  rewrite Hrow in Hf2.
  apply Forall2_app_inv_l in Hf2 as (k1 & k2 & Hk1 & Hk2 & Hk).
  (* the exit label survives verbatim *)
  destruct k2 as [|lst k2]; [by inversion Hk2|].
  apply Forall2_cons_1 in Hk2 as [Hlst Hnil].
  apply Forall2_nil_inv_l in Hnil. subst k2.
  apply lbl_reidx_w_store in Hlst. subst lst.
  (* split the appended trace at the same place *)
  have Hlen : length (so_tr o) = S (length k1).
  { have Hl := f_equal length Hk. rewrite length_fmap length_app /= in Hl. lia. }
  destruct (drop (length k1) (so_tr o)) as [|s rest] eqn:Hdrop.
  { exfalso. have Hl := f_equal length Hdrop.
    rewrite length_drop Hlen /= in Hl. lia. }
  have Hrest : rest = [].
  { have Hl := f_equal length Hdrop. rewrite length_drop Hlen /= in Hl.
    destruct rest; [done|simpl in Hl; lia]. }
  subst rest.
  set t1 := take (length k1) (so_tr o).
  have Hsplit : so_tr o = t1 ++ [s].
  { rewrite -Hdrop /t1. by rewrite take_drop. }
  have Hk' : ((λ s0 : estep, es_lb s0) <$> t1)
             ++ ((λ s0 : estep, es_lb s0) <$> [s])
             = k1 ++ [WeakAxiomatic.LStore rl base vs kc].
  { rewrite -fmap_app -Hsplit. exact Hk. }
  have Hlk1 : length ((λ s0 : estep, es_lb s0) <$> t1) = length k1.
  { rewrite length_fmap /t1 length_take Hlen. lia. }
  apply app_inj_1 in Hk' as [Hk1' Hk2']; [|exact Hlk1].
  cbn in Hk2'. injection Hk2' as Hes.
  (* the prefix contributes nothing *)
  have Hpre' : Forall (λ s0 : estep, lb_is_w (es_lb s0) = false) t1.
  { apply Forall_lookup_2. intros i s0 Hi.
    have Hy : k1 !! i = Some (es_lb s0)
      by rewrite -Hk1' list_lookup_fmap Hi.
    destruct (Forall2_lookup_r _ _ _ _ _ Hk1 Hy) as (lb & Hlb & Hri).
    eapply lbl_reidx_w_notw; [exact Hri|].
    by eapply (Forall_lookup_1 _ _ _ _ Hpre Hlb). }
  (* ... and the store contributes exactly its own message *)
  rewrite (seg_step_log d0 o St St' Hst) Hsplit tr_msgs_app.
  rewrite (tr_msgs_notw _ Hpre') /= app_nil_r /es_msg Hes /=.
  rewrite (Hag s); [done|].
  rewrite Hsplit. apply elem_of_app. right. apply elem_of_list_here.
Qed.

(** ** 3.5 … hence one [wlk_step] *)
Theorem wlk_step_of_seg (G : gexec) (d0 : dev_state) (St St' : cyc_state)
    (n : nat) (o : segout) (pre : list lbl) (rl : bool) (base : Z)
    (vs : list (bv 8)) (kc : wm_class) (w : geid) :
  seg_step d0 o St St' →
  so_row o = pre ++ [WeakAxiomatic.LStore rl base vs kc] →
  Forall (λ lb, lb_is_w lb = false) pre →
  cd_img (cst_c St') = cd_img (cst_c St) →
  cst_pst St' 0%nat = cst_pst St 0%nat →
  cst_dv St' 0%nat = cst_dv St 0%nat →
  gwrite_at G (S n) = Some w →
  gmsg G w = Some (WMsg base vs (Some (so_hart o)) kc) →
  wlk_step G d0 St n.
Proof.
  intros Hst Hrow Hpre Himg Hpst Hdv Hw Hm.
  exists o, St', w, (WMsg base vs (Some (so_hart o)) kc).
  split_and!; [exact Hst|exact Himg|exact Hpst|exact Hdv|exact Hw|exact Hm|].
  by eapply seg_step_msgs.
Qed.

(* ====================================================================== *)
(** * 4. THE POLICY

    §3 reduced the walk to "one certified segment per write".  This section
    says what a certified segment IS — [WeakRvwmoCert3.cert_segment'] at
    [Ctx := cpol_ctx G W x] and [Cls := wcls_at G W x] — and names, at the
    position each is honestly stated, the pieces the certification still
    owes.

    THE LEDGER IS TWO ITEMS.  §4.0 closes (W-3) and (W-4); §4.0b states
    what is left:

      [wub]   (W-2), (P-3) [wit_fence_ub] at the next position — a
              HYPOTHESIS by design ([WeakRvwmoCert3] §2.1): a witness
              raises [w_vrOld] byte-agnostically and that reaches a later
              read's floor only through a publishing fence, so the
              obligation is guarded and vacuous at a witness with no such
              fence.

      [wpol]  (W-1), the READ/REGISTER POLICY, carrying (P-4) PROGRESS and
              now also (W-3)'s classification.  This is where
              [WeakRvwmoCert3.boundary_reconverge_run] is applied: at a
              SUBSTITUTED read the certified run and the emission sit at
              different monad nodes ([WeakEvProv.taint_closure_load]), and
              that either REACHES its instruction boundary is the EWPs'
              content, not a graph-side lemma.  At an unsubstituted read
              the two runs are in lockstep and the clause is
              [WeakEvProv.instr_dagree_ev] plus
              [WeakRvwmoCert3.cpol_read]. *)

Definition wsrc_le (G : gexec) (n : nat) (e : geid) : Prop :=
  ∀ aq base ts vs, gx_lbl G e = Some (WeakAxiomatic.LLoad aq base ts vs) →
    ∀ (j : nat) t, ts !! j = Some t → (t ≤ n)%nat.

(** … and its negation, POSITIVELY: the walk's witness set at log length
    [n]. *)
Definition wwit (G : gexec) (n : nat) (e : geid) : Prop :=
  ∃ aq base ts vs,
    gx_lbl G e = Some (WeakAxiomatic.LLoad aq base ts vs) ∧
    ∃ (j : nat) t, ts !! j = Some t ∧ (n < t)%nat.

Lemma wsrc_le_not_wwit G n e : wsrc_le G n e → ¬ wwit G n e.
Proof.
  intros Hle (aq & base & ts & vs & Hl & j & t & Hj & Hlt).
  have Hle' := Hle aq base ts vs Hl j t Hj. lia.
Qed.

Lemma not_wwit_wsrc_le G n e : ¬ wwit G n e → wsrc_le G n e.
Proof.
  intros Hnw aq base ts vs Hl j t Hj.
  destruct (decide (t ≤ n)%nat) as [Hle|Hlt]; [exact Hle|].
  exfalso. apply Hnw. exists aq, base, ts, vs.
  split; [exact Hl|]. exists j, t. split; [exact Hj|lia].
Qed.

(** (W-4)'s content: a WRITE position is never a witness. *)
Lemma wwit_not_w G n e l :
  gx_lbl G e = Some l → lb_is_w l = true → ¬ wwit G n e.
Proof.
  intros Hl Hw (aq & base & ts & vs & Hl' & _).
  rewrite Hl' in Hl. injection Hl as <-. by simpl in Hw.
Qed.

(** THE CLASSIFICATION IS LOG-DECIDED.  At a position whose label is known,
    "witness" and "sources already in the log" are the two arms of a
    DECIDABLE alternative — the read's source list is finite and [n] is a
    number.  This is what lets the policy dispatch on the two routes
    without a [Decision] instance for [wwit] itself. *)
Lemma wsrc_or_wwit (G : gexec) (n : nat) (e : geid) (lb : lbl) :
  gx_lbl G e = Some lb → wsrc_le G n e ∨ wwit G n e.
Proof.
  intros Hl.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw
                 |aq rl base ts rvs wvs kc];
    [|left; intros aq0 base0 ts0 vs0 Hl0; congruence
     |left; intros aq0 base0 ts0 vs0 Hl0; congruence
     |left; intros aq0 base0 ts0 vs0 Hl0; congruence].
  destruct (decide (Exists (λ t, (n < t)%nat) ts)) as [Hex|Hex].
  - right. apply Exists_exists in Hex as (t & Hin & Hlt).
    apply elem_of_list_lookup in Hin as (j & Hj).
    exists aq, base, ts, vs. split; [exact Hl|]. by exists j, t.
  - left. intros aq0 base0 ts0 vs0 Hl0 j t Hj.
    rewrite Hl in Hl0. injection Hl0 as Ha Hb Hc Hd. subst.
    destruct (decide (t ≤ n)%nat) as [Hle|Hgt]; [exact Hle|].
    exfalso. apply Hex, Exists_exists. exists t.
    split; [by eapply elem_of_list_lookup_2|lia].
Qed.

(** THE GRAPH-SIDE DATUM the walk carries for the hart it is running: every
    read of hart [x] draws on a write the log has already reached.  It is
    decidable from [G] and [n], and it is what makes the segment need no
    substitution. *)
Definition wrow_in_log (G : gexec) (x : agent) (n : nat) : Prop :=
  ∀ k, (1 ≤ k)%nat → wsrc_le G n (x, k).

Definition wnw (W : geid → Prop) (x : agent) : Prop :=
  ∀ (c0 : cand), ¬ W (x, S (gcnt x (cd_tr c0))).

(** (W-4), DISCHARGED. *)
Theorem wnw_of_pfx (G : gexec) (x : agent) (n : nat) :
  wrow_in_log G x n → wnw (wwit G n) x.
Proof. intros Hrow c0. apply wsrc_le_not_wwit, Hrow. lia. Qed.

(** ** 4.0a (W-3): the classification, read off the log *)

(** THE PER-STEP CLASSIFICATION, as [WeakRvwmoGlue2.cpol_ctx_snoc] wants it.
    This is [WeakRvwmoCert3.cert_segment']'s [Cls] at the walk's instance. *)
Definition wcls_at (G : gexec) (W : geid → Prop) (x : agent) (c0 : cand)
    (lb' : lbl) : Prop :=
  cstep_cls G W x c0 lb' ∧
  (lb_is_w lb' = true →
     gwix G (x, gcnt x (cd_tr c0)) = S (length (cd_log_end c0))) ∧
  (** THE POISONED STEP'S FLOOR OBLIGATION at the appended label
      ([WeakRvwmoGlue2.cstep_pois_ok]).  Free at every route but the
      poisoned one: a true, store, fence or RMW step carries [G]'s own
      label and a witness step carries [G]'s own footprint, and each
      contradicts one of the obligation's premises. *)
  cstep_pois_ok G x c0 lb'.

(** At a NON-witness position the classification IS [G]'s own label, and
    the write clause is [wlog_pfx] read forward: the log has length [n], so
    "the appended write is [G]'s [(n+1)]-st" says exactly [gwix = S n]. *)
Theorem wcls_of_pfx (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (c0 : cand) (lb' : lbl) :
  wlog_pfx G n (cd_log_end c0) →
  gx_lbl G (x, gcnt x (cd_tr c0)) = Some lb' →
  ¬ W (x, gcnt x (cd_tr c0)) →
  (lb_is_w lb' = true → gwix G (x, gcnt x (cd_tr c0)) = S n) →
  wcls_at G W x c0 lb'.
Proof.
  intros [Hlen _] Hl HnW Hix. split_and!.
  - left. by split.
  - intros Hw. by rewrite (Hix Hw) Hlen.
  - intros _ Hne _. by destruct (Hne Hl).
Qed.

(** A log message's byte IS the graph write's byte. *)
Lemma gmsg_byte G w a v m :
  gwrites_byte G w a v → gmsg G w = Some m → msg_byte m a = Some v.
Proof.
  intros (l & base & vs & j & Hl & Hwr & Hj & Hb) Hm.
  rewrite /gmsg Hl Hwr in Hm. injection Hm as <-.
  rewrite /msg_byte /=. case_bool_decide as Hba; last first.
  { exfalso. apply Hba. rewrite -Hb /WeakAxiomatic.acc_addr. lia. }
  rewrite -Hb.
  replace (Z.to_nat (WeakAxiomatic.acc_addr base j - base)) with j
    by (rewrite /WeakAxiomatic.acc_addr; lia).
  exact Hj.
Qed.

(** (W-3)'s READ half: [src_in_log] IS "every source index is at most the
    current write count", at a candidate whose log is the gmo prefix.  This
    is the sentence the ledger's (W-3) called DATA, proved. *)
Theorem src_in_log_of_pfx (G : gexec) (n : nat) (c : cand) (e : geid)
    (aq : bool) (base : Z) (ts : list nat) (vs : list (bv 8)) :
  gload_value G →
  cd_img c = gx_img G →
  wlog_pfx G n (cd_log_end c) →
  gx_lbl G e = Some (WeakAxiomatic.LLoad aq base ts vs) →
  length vs = length ts →
  wsrc_le G n e →
  src_in_log c base ts vs.
Proof.
  intros Hlv Himg [Hlen Hpfx] Hl Hlenv Hle.
  split; [exact Hlenv|]. intros j t v Hj Hv.
  have Hrb : greads_byte G e (WeakAxiomatic.acc_addr base j) t v.
  { by exists (WeakAxiomatic.LLoad aq base ts vs), base, ts, vs, j. }
  destruct (Hlv _ _ _ _ Hrb) as [Hval _].
  have Ht : (t ≤ n)%nat := Hle aq base ts vs Hl j t Hj.
  destruct t as [|t'].
  - by rewrite log_byte_0 Himg.
  - destruct Hval as (w & Hw & Hwb & _).
    rewrite log_byte_S.
    have Hlt : (t' < n)%nat by lia.
    rewrite -(Hpfx t' w Hlt Hw).
    destruct (gmsg G w) as [m|] eqn:Hm.
    + rewrite /=. by apply (gmsg_byte G w _ v m).
    + exfalso. destruct Hwb as (l & base' & vs' & j' & Hl' & Hwr & _).
      by rewrite /gmsg Hl' Hwr in Hm.
Qed.

(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(** ** 4.0a' THE NODE, CARRIED: the walk's own [Nd], and the two side
       conditions the [csync] iteration names

    [WeakRvwmoCert3.cert_segment''] hands the policy [Nd k m] — "the hart
    can be at node [m] with [k] row events behind it" — and asks only that
    [Nd] be closed under one administrative stretch and one block.  The
    walk's instance is the BOOT-ANCHORED reachability [wnd]: [ndreach] from
    the hart's booted node, gated by [G]'s own labels.  Its closure laws
    ARE [ndreach]'s constructors, so it costs the caller nothing, and the
    walk's invariant carries it from one segment of a hart to the next
    because [cert_segment''] hands the exit node back reachable.

    [wrds_free] is the other thing the [csync] iteration names ([Hrds] /
    [Hrdsp]): no emitted block READS a carrier the taint set holds.  At
    [T = []] — the walk's own instantiation — it is free
    ([wrds_free_nil]). *)
Definition wQnd (G : gexec) (x : agent) (k : nat) (lb : lbl) : Prop :=
  gx_lbl G (x, k) = Some lb.

Definition wnd (d0 : dev_state) (G : gexec) (boot : agent → pexv6)
    (x : agent) (k : nat) (cpu : CPU) (m : M unit) : Prop :=
  ∃ (m0 : M unit) (rs0 : regstate) (fn0 : ofence) (ib0 : oib32),
    boot x = PHart cpu m0 rs0 fn0 ib0 ∧
    ndreach cpu d0 (wQnd G x) 0%nat m0 k m.

Lemma wnd_start (d0 : dev_state) (G : gexec) (boot : agent → pexv6)
    (x : agent) (cpu : CPU) (m0 : M unit) (rs0 : regstate) (fn0 : ofence)
    (ib0 : oib32) :
  boot x = PHart cpu m0 rs0 fn0 ib0 → wnd d0 G boot x 0%nat cpu m0.
Proof.
  intros H. exists m0, rs0, fn0, ib0. split; [exact H|apply nd_start].
Qed.

(** THE INVERSION THE SITES USE: at row position 0 the reachability is an
    administrative stretch out of the BOOTED node — no block has run yet —
    so any property of the boot node closed under administrative runs
    transfers to every node the datum is handed. *)
Lemma ndreach_fix (cpu : CPU) (d0 : dev_state) (Q : nat → lbl → Prop)
    (P : M unit → Prop) (m0 : M unit) :
  P m0 →
  (∀ (m1 m2 : M unit) (rs1 rs2 : regstate) (fn1 fn2 : ofence)
     (ib1 ib2 : oib32) (ls : list wlabel) (rds : list wreg)
     (wrs : list register) (ann : bool),
     P m1 → (∀ l0, l0 ∈ ls → lb_admin true l0) →
     phrun cpu ls rds wrs ann m1 rs1 fn1 ib1 d0 m2 rs2 fn2 ib2 d0 → P m2) →
  ∀ (k : nat) (m : M unit),
    ndreach cpu d0 Q 0%nat m0 k m → k = 0%nat → P m.
Proof.
  intros H0 Ha k m Hreach.
  induction Hreach as [|k m m' rs rs' fn fn' ib ib' ls rds wrs ann
                        Hreach IH Hadm Hrun
                      |k m m' ws lb l rds wrs rs rs' fn fn' ib ib'
                        Hreach IH Hq Hblk
                      |k m m' ws lb l1 l2 rds wrs rs rs' fn fn' ib ib'
                        Hreach IH Hq Hblk];
    intros Hk; [exact H0| |discriminate Hk|discriminate Hk].
  eapply Ha; [by apply IH|exact Hadm|exact Hrun].
Qed.

Lemma wnd_fix (d0 : dev_state) (G : gexec) (boot : agent → pexv6)
    (x : agent) (P : M unit → Prop) (cpu : CPU) (m : M unit) :
  (∀ m0 rs0 fn0 ib0, boot x = PHart cpu m0 rs0 fn0 ib0 → P m0) →
  (∀ (m1 m2 : M unit) (rs1 rs2 : regstate) (fn1 fn2 : ofence)
     (ib1 ib2 : oib32) (ls : list wlabel) (rds : list wreg)
     (wrs : list register) (ann : bool),
     P m1 → (∀ l0, l0 ∈ ls → lb_admin true l0) →
     phrun cpu ls rds wrs ann m1 rs1 fn1 ib1 d0 m2 rs2 fn2 ib2 d0 → P m2) →
  wnd d0 G boot x 0%nat cpu m → P m.
Proof.
  intros Hb Ha (m0 & rs0 & fn0 & ib0 & Hbx & Hreach).
  eapply (ndreach_fix cpu d0 (wQnd G x) P m0);
    [by eapply Hb|exact Ha|exact Hreach|reflexivity].
Qed.

(** THE CLOSURE LAWS, as one bundle at a fixed hart. *)
Definition wnd_ok (cpu : CPU) (d0 : dev_state) (Q : nat → lbl → Prop)
    (Nd : nat → CPU → M unit → Prop) : Prop :=
  (∀ (k : nat) (m m' : M unit) (rs rs' : regstate) (fn fn' : ofence)
     (ib ib' : oib32) (ls : list wlabel) (rds : list wreg)
     (wrs : list register) (ann : bool),
     Nd k cpu m → (∀ l0, l0 ∈ ls → lb_admin true l0) →
     phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 →
     Nd k cpu m') ∧
  (∀ (k : nat) (m m' : M unit) (ws : wstate) (lb : lbl) (l : wlabel)
     (rds : list wreg) (wrs : list register) (rs rs' : regstate)
     (fn fn' : ofence) (ib ib' : oib32),
     Nd k cpu m → Q k lb →
     cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
     Nd (S k) cpu m') ∧
  (∀ (k : nat) (m m' : M unit) (ws : wstate) (lb : lbl) (l1 l2 : wlabel)
     (rds : list wreg) (wrs : list register) (rs rs' : regstate)
     (fn fn' : ofence) (ib ib' : oib32),
     Nd k cpu m → Q k lb →
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
     Nd (S k) cpu m').

Lemma wnd_wnd_ok (cpu : CPU) (d0 : dev_state) (G : gexec)
    (boot : agent → pexv6) (x : agent) (Q : nat → lbl → Prop) :
  (∀ k lb, Q k lb → gx_lbl G (x, k) = Some lb) →
  wnd_ok cpu d0 Q (wnd d0 G boot x).
Proof.
  intros HQ. split_and!.
  - intros k m m' rs rs' fn fn' ib ib' ls rds wrs ann
      (m0 & rs0 & fn0 & ib0 & Hb & Hnd) Ha Hr.
    exists m0, rs0, fn0, ib0. split; [exact Hb|by eapply nd_adm].
  - intros k m m' ws lb l rds wrs rs rs' fn fn' ib ib'
      (m0 & rs0 & fn0 & ib0 & Hb & Hnd) Hq Hblk.
    exists m0, rs0, fn0, ib0. split; [exact Hb|].
    eapply nd_blk; [exact Hnd|by apply HQ|exact Hblk].
  - intros k m m' ws lb l1 l2 rds wrs rs rs' fn fn' ib ib'
      (m0 & rs0 & fn0 & ib0 & Hb & Hnd) Hq Hblk.
    exists m0, rs0, fn0, ib0. split; [exact Hb|].
    eapply nd_blkp; [exact Hnd|by apply HQ|exact Hblk].
Qed.

(** THE DEPENDENCY-FREEDOM SIDE CONDITION, at every emitted block. *)
Definition wrds_free (d0 : dev_state) (T : list wreg) : Prop :=
  ∀ (cpu : CPU) (ws : wstate) (lb : lbl) (l1 l2 : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs' : regstate)
    (fn' : ofence) (ib' : oib32),
    (cblk cpu d0 ws lb l1 rds wrs m rs fn ib m' rs' fn' ib' ∨
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib') →
    rds_ok (λ nn, nn ∉ T) rds.

Lemma wrds_free_nil (d0 : dev_state) : wrds_free d0 [].
Proof.
  intros cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' _ n _.
  apply not_elem_of_nil.
Qed.

(** ** 4.0b THE OBLIGATIONS, AND THE POSITION-INDEXED POLICY

    THE REPAIR ([WeakRvwmoWalk2] §4, the TENTH-PASS checkpoint item 3).  The
    policy used to be asked at EVERY candidate the certification context
    admits, while everything it must deliver — [mstep_ok] and the
    classification [wcls_at] — is about [G]'s label at THAT CANDIDATE'S OWN
    row position.  The two are irreconcilable: the EMPTY candidate is a
    context of every witness-free graph and its position is 0, so a policy
    carrying the segment's exit store pinned that store to row position 0
    ([WeakRvwmoWalk2.wpol_pins_store] / [wpol_exit_at_zero]).

    The cure is to INDEX BY ROW POSITION.  [wctx] is the walk's carried
    context — [cpol_ctx] together with the ALIGNMENT [gcnt x (cd_tr c) = k]
    and the log's own prefix state at that position — and [wQ] is the
    per-position segment predicate.  [wpol] is then the policy at an ALIGNED
    candidate, and (this is the second half of the repair) it is no longer
    an obligation at all: §4.0c discharges it outright from the graph. *)

Definition wub (G : gexec) (W : geid → Prop) (x : agent) : Prop :=
  ∀ (c0 : cand) (lb' : lbl) (ev' : nat → geid),
    ctrace_prefix G (cand_snoc c0 (EStep x lb')) ev' W →
    wit_fence_ub G (cand_snoc c0 (EStep x lb')) ev' W
      (x, S (gcnt x (cd_tr c0))).

(** (W-4) RESTRICTED TO THE SEGMENT.  [wnw] above asks the witness set to
    miss the successor of EVERY candidate's position; the walk only ever
    needs the positions its own segment covers, and a hart with witnesses
    elsewhere in its row is then not excluded. *)
Definition wnw_seg (G : gexec) (n : nat) (x : agent) (k0 kz : nat) : Prop :=
  ∀ k, (k0 ≤ k)%nat → (k ≤ kz)%nat → ¬ wwit G n (x, S k).

(** THE OLD, OVER-QUANTIFIED POLICY.  Kept ONLY as the subject of
    [WeakRvwmoWalk2] §4's machine-checked refutation; nothing builds a
    segment out of it any more. *)
Definition wpol_flat (G : gexec) (W : geid → Prop) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Q : lbl → Prop) : Prop :=
  ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    cpol_ctx G W x c0 →
    Q lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2',
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx_w lb lb' ∧
      wcls_at G W x c0 lb' ∧
      dreg_agree (λ nn, nn ∉ T) rs1' rs2'.

(** THE WITNESS SITE DATUM.  A position the log-decided witness set names
    is served by the SUBSTITUTED route — [WeakRvwmoCert2.cert_read_witness]
    at [WeakRvwmoCert.latest_read_lbl] — and three things must line up for
    the certified label to be [WeakRvwmoCert2.lbl_reidx]-related to [G]'s:
    [aq = false], [latest_bytes_ok] (the footprint's bytes exist at the
    candidate's latest source), and THE MACHINE-SIDE RE-CONVERGENCE.

    THE THIRD CLAUSE IS [wwit_nd], AND [wwit_vindep] IS RETIRED.  What the
    datum used to ask ([wwit_vindep]) was that the substituted read land at
    the emission's OWN successor node ([WeakRvwmoCert2.cblk_vfree]) — "the
    read's continuation ignores the value".  NO REAL LOAD DOES THAT (a load
    writes its destination register), and the premise could not even be
    stated at a site, because it quantified over EVERY [cblk] carrying the
    label: the concrete node was known only to [wlk_inv']'s
    [wemit]/[pex_dag] clauses, which the policy interface did not see.

    [WeakRvwmoCert3] §5b.4 supplies both repairs, and [wwit_nd] is their
    shape:

      - THE NODE IS PINNED, by the reachability parameter [Nd p cpu m] the
        policy is now handed.  The datum speaks only about the nodes the
        hart can actually be at with [p] row events behind it, so a
        concrete site discharges it by INVERTING the reachability.
      - THE CONCLUSION IS [WeakRvwmoCert3.csync], NOT "the same node".
        [WeakRvwmoCert2.cblk_subst] always provides the substituted block,
        at a DIFFERENT successor node; what the iteration needs is that the
        two runs re-converge — either at once (the LOCKSTEP arm, which a
        value-independent node gives: [WeakRvwmoCycWit.cy_pstep_ld']), or
        at the instruction BOUNDARY (the DIVERGED arm, which is what a real
        load whose value IS USED gives: [WeakRvwmoCycWit2]).

    The first two clauses are functions of [G] and the write count alone —
    the candidate is pinned by [cd_img c = gx_img G] and [wlog_pfx G n];
    the third is about the verified program at that site. *)
Definition wwit_nd (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (p : nat) : Prop :=
  ∀ (cpu : CPU) (ws : wstate) (aq : bool) (base : Z) (ts : list nat)
    (vs : list (bv 8)) (l : wlabel) (rds : list wreg)
    (wrs : list register) (m : M unit) (rs : regstate) (fn : ofence)
    (ib : oib32) (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32)
    (tvs2 : list (nat * bv 8)),
    Nd p cpu m →
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base ts vs) l rds wrs
      m rs fn ib m' rs' fn' ib' →
    length tvs2 = length ts →
    ∃ (l2 : wlabel) (rds2 : list wreg) (wrs2 : list register) (m2 : M unit),
      cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2)
        l2 rds2 wrs2 m rs fn ib m2 rs' fn' ib' ∧
      csync T m' rs' fn' ib' m2 rs' fn' ib'.

Definition wwit_site (G : gexec) (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (n : nat) (x : agent) (p : nat)
    : Prop :=
  (∀ (c : cand) (aq : bool) (base : Z) (ts : list nat) (vs : list (bv 8)),
     cd_img c = gx_img G →
     wlog_pfx G n (cd_log_end c) →
     gx_lbl G (x, p) = Some (WeakAxiomatic.LLoad aq base ts vs) →
     aq = false ∧ latest_bytes_ok c base (length ts)) ∧
  wwit_nd d0 T Nd p.

(** THE SITE DATUM: [G]'s label at row position [p], the log index a write
    there must carry, RMW-freedom, and — only where the position IS a
    witness — the substituted route's data.  What it NO LONGER asks (the
    tenth pass's OBSTRUCTION 2) is [wsrc_le]: a witness position is now
    servable, by the latest-read route. *)
Definition wsite_ok (G : gexec) (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (n : nat) (x : agent) (p : nat)
    (lb : lbl) : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  (lb_is_w lb = true → gwix G (x, p) = S n) ∧
  lb_rmwfree lb ∧
  (wwit G n (x, p) → wwit_site G d0 T Nd n x p).

(** The log length a candidate at row position [k] of the segment carries:
    the segment is "non-writes, then ONE store at [kz]", so the log is the
    gmo prefix of length [n] up to and including [kz], and of length [S n]
    after it. *)
Definition wlogn (n kz k : nat) : nat :=
  if bool_decide (k ≤ kz)%nat then n else S n.

(** THE WALK'S CARRIED CONTEXT, INDEXED BY ROW POSITION. *)
Definition wctx (G : gexec) (n : nat) (x : agent) (kz : nat)
    (k : nat) (c : cand) : Prop :=
  cpol_ctx G (wwit G n) x c ∧
  gcnt x (cd_tr c) = k ∧
  wlog_pfx G (wlogn n kz k) (cd_log_end c).

(** THE SEGMENT PREDICATE, INDEXED BY ROW POSITION: positions [k0 .. kz] of
    hart [x]'s row, non-writes before [kz] and the exit store at it. *)
Definition wQ (G : gexec) (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (n : nat) (x : agent) (k0 kz : nat)
    (k : nat) (lb : lbl) : Prop :=
  (k0 ≤ k)%nat ∧ (k ≤ kz)%nat ∧
  wsite_ok G d0 T Nd n x k lb ∧
  (lb_is_w lb = true ↔ k = kz).

Lemma wQ_rmwfree G d0 T Nd n x k0 kz k lb :
  wQ G d0 T Nd n x k0 kz k lb → lb_rmwfree lb.
Proof. by intros (_ & _ & (_ & _ & H & _) & _). Qed.

Lemma wQ_lbl G d0 T Nd n x k0 kz k lb :
  wQ G d0 T Nd n x k0 kz k lb → gx_lbl G (x, k) = Some lb.
Proof. by intros (_ & _ & (H & _) & _). Qed.

(** ** 4.0c THE POLICY AT AN ALIGNED CANDIDATE, AND ITS DISCHARGE *)

Definition wpol (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Nd : nat → CPU → M unit → Prop)
    (k0 kz : nat) : Prop :=
  ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    wctx G n x kz k c0 →
    wQ G d0 T Nd n x k0 kz k lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
    rds_ok (λ nn, nn ∉ T) rds →
    Nd k cpu m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx_w lb lb' ∧
      wcls_at G (wwit G n) x c0 lb' ∧
      csync T m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lb_is_w lb = true →
         clockstep T m' rs1' fn' ib' m2' rs2' fn2' ib2').

(** THE CLASSIFICATION AT A WITNESS: [cstep_cls]'s SUBSTITUTED disjunct,
    which the split of [WeakRvwmoCert3.cpol_ctx] made reachable. *)
Theorem wcls_of_wit (G : gexec) (W : geid → Prop) (x : agent) (c0 : cand)
    (base : Z) (ts : list nat) (vs : list (bv 8)) :
  gx_lbl G (x, gcnt x (cd_tr c0))
    = Some (WeakAxiomatic.LLoad false base ts vs) →
  W (x, gcnt x (cd_tr c0)) →
  wcls_at G W x c0 (latest_read_lbl c0 false base (length ts)).
Proof.
  intros Hl HW. split_and!.
  - right; left. split; [exact HW|].
    exists base, (length ts), ts, vs.
    split_and!; [exact Hl|reflexivity|reflexivity].
  - intros Hw. by rewrite latest_read_not_w in Hw.
  - intros _ _ Hnw. exfalso. apply Hnw.
    by exists base, (length ts), ts, vs.
Qed.

(** THE TWO READ ROUTES, AS ONE BLOCK POLICY.  The mirror
    ([WeakRvwmoCert2.cert_block_mirror] at the EMPTY taint set) moves the
    block across the register change without touching its label; then the
    LOG-DECIDED classification ([wsrc_or_wwit]) picks the route:

      - NOT a witness: [G]'s own label comes back verbatim
        ([lbl_reidx_refl]), admissible by [WeakRvwmoCert3.cpol_read] (whose
        [¬ W] premise is exactly what the split moved here) at
        [src_in_log_of_pfx], [cert_write_ok] or [cert_fence_ok];
      - A WITNESS: the candidate's LATEST-source read comes back
        ([WeakRvwmoCert.latest_read_lbl]), admissible by
        [WeakRvwmoCert2.cert_read_witness] with NO floor obligation, and
        the block is RE-TIMESTAMPED to it
        ([WeakRvwmoCert2.cblk_load_retime] — the values are the site
        datum's, so the successor monad node does not move). *)
Theorem wblk_pol_at (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Nd : nat → CPU → M unit → Prop)
    (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs1 rs2 : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs1' : regstate)
    (fn' : ofence) (ib' : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  srvwmo_consistent c0 →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G (wwit G n) x c0 →
  wsite_ok G d0 T Nd n x (gcnt x (cd_tr c0)) lb →
  dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
  rds_ok (λ nn, nn ∉ T) rds →
  Nd (gcnt x (cd_tr c0)) cpu m →
  cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
  ∃ (lb' : lbl) (l' : wlabel) (rds' : list wreg) (wrs' : list register)
    (rs2' : regstate) (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
    cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
    mstep_ok (cand_last_st c0) x lb' ∧
    lbl_reidx_w lb lb' ∧
    wcls_at G (wwit G n) x c0 lb' ∧
    csync T m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
    (lb_is_w lb = true →
       clockstep T m' rs1' fn' ib' m2' rs2' fn2' ib2').
Proof.
  intros Hcons Hpc Hc Himg Hpfx Hctx Hsite Hag Hrds Hnd Hblk.
  pose proof Hcons as (Hwf & _ & Hlv & _).
  pose proof Hsite as (Hl & Hix & Hrmw & Hwit).
  destruct (cert_block_mirror (λ nn, nn ∉ T) cpu d0 ws lb l rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk Hrds Hag)
    as (rs2' & Hblk2 & Hag2).
  destruct (wsrc_or_wwit G n (x, gcnt x (cd_tr c0)) lb Hl) as [Hle|HW].
  - (* ------------------------- THE TRUE ROUTE ------------------------- *)
    have HnW : ¬ wwit G n (x, gcnt x (cd_tr c0)) := wsrc_le_not_wwit _ _ _ Hle.
    exists lb, l, rds, wrs, rs2', m', fn', ib'.
    split_and!; [exact Hblk2| |apply lbl_reidx_w_refl
                |by apply (wcls_of_pfx G (wwit G n) n x c0 lb)
                |(left; split_and!;
                    [reflexivity|reflexivity|reflexivity|exact Hag2])
                |(intros _; split_and!;
                    [reflexivity|reflexivity|reflexivity|exact Hag2])].
    destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw
                   |aq rl base ts rvs wvs kc].
    + apply (cpol_read G (wwit G n) x c0 aq base ts vs Hcons Hpc Hctx
               HnW Hl).
      apply (src_in_log_of_pfx G n c0 (x, gcnt x (cd_tr c0)) aq base ts vs
               Hlv Himg Hpfx Hl (gshape G Hwf _ _ Hl) Hle).
    + apply cert_write_ok. exact (gshape G Hwf _ _ Hl).
    + apply cert_fence_ok.
    + by destruct Hrmw.
  - (* ------------------------ THE WITNESS ROUTE ----------------------- *)
    pose proof HW as (aq & base & ts & vs & Hl' & _).
    have Hlb : lb = WeakAxiomatic.LLoad aq base ts vs.
    { rewrite Hl' in Hl. by injection Hl as <-. }
    subst lb.
    destruct (Hwit HW) as (Hgs & Hvf).
    destruct (Hgs c0 aq base ts vs Himg Hpfx Hl') as (-> & Hbytes).
    destruct (Hvf cpu ws false base ts vs l rds wrs
                m rs2 fn ib m' rs2' fn' ib'
                (wit_tvs c0 base (length ts)) Hnd Hblk2
                (wit_tvs_length c0 base (length ts)))
      as (l2 & rds2 & wrs2 & m2 & Hblk3 & Hsync).
    rewrite (wit_tvs_lbl c0 false base (length ts)) in Hblk3.
    exists (latest_read_lbl c0 false base (length ts)), l2, rds2, wrs2, rs2',
      m2, fn', ib'.
    split_and!.
    + exact Hblk3.
    + by apply cert_read_witness.
    + right; left. rewrite /latest_read_lbl /=. split_and!;
        [reflexivity|reflexivity|reflexivity| |].
      * by rewrite /lrd_ts length_fmap length_seq.
      * apply lrd_length.
    + by apply (wcls_of_wit G (wwit G n) x c0 base ts vs).
    + exact (csync_regs T m' m2 rs2' rs1' rs2' fn' ib' Hsync Hag2).
    + intros Hw. by simpl in Hw.
Qed.

(** (W-1), DISCHARGED.  The alignment is what makes it derivable: the site
    data are read off [G] at the position the block sits at, and the
    candidate's own position IS that position. *)
Theorem wpol_of_sites (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Nd : nat → CPU → M unit → Prop)
    (k0 kz : nat) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  wpol G n x cpu d0 T Nd k0 kz.
Proof.
  intros Hcons Hpc k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hc (Hctx & Hgc & Hpfx) (Hk0 & Hkz & Hsite & _) Hrelp Hag Hrds Hnd Hblk.
  have Himg : cd_img c0 = gx_img G.
  { destruct Hctx as (ev & Hgt & _). exact (ctp_img G c0 ev _ Hgt). }
  have Hpfx' : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  apply (wblk_pol_at G n x cpu d0 T Nd c0 ws lb l rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Hpc Hc Himg Hpfx' Hctx);
    [by rewrite Hgc|exact Hag|exact Hrds|by rewrite Hgc|exact Hblk].
Qed.

(** ** 4.0d THE CONTEXT IS PRESERVED — (P-1) at the indexed instance *)
Theorem wctx_pres (G : gexec) (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (n : nat) (x : agent) (k0 kz : nat) :
  gwf G →
  wub G (wwit G n) x →
  ∀ (k : nat) (c0 : cand) (lb lb' : lbl),
    wctx G n x kz k c0 → srvwmo_consistent c0 →
    wQ G d0 T Nd n x k0 kz k lb →
    lbl_reidx_w lb lb' → mstep_ok (cand_last_st c0) x lb' →
    wcls_at G (wwit G n) x c0 lb' →
    wctx G n x kz (S k) (cand_snoc c0 (EStep x lb')).
Proof.
  intros Hwf Hub k c0 lb lb' (Hctx & Hgc & Hpfx) Hc
         (Hk0 & Hkz & Hsite & Hiff) Hri Hok (Hcl & Hix & Hstp).
  have Hpfxn : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  have Hlen : length (cd_log_end c0) = n by destruct Hpfxn as [H _].
  have Hgc2 : gcnt x (cd_tr (cand_snoc c0 (EStep x lb'))) = S k
    by rewrite gcnt_cand_snoc_self Hgc.
  split_and!.
  - eapply cpol_ctx_snoc;
      [exact Hwf|exact Hctx|exact Hcl|exact Hix
      |intros ev' Hev'; exact (Hub c0 lb' ev' Hev')|exact Hstp].
  - exact Hgc2.
  - rewrite cd_log_end_snoc.
    destruct (decide (k = kz)) as [->|Hne].
    + (* THE EXIT STORE: the log grows by G's (n+1)-st write's message *)
      have Hw : lb_is_w lb = true by apply Hiff.
      destruct Hsite as (Hl & Hgwix & Hrmw & Hwit).
      destruct lb as [aq0 b0 ts0 vs0|rl base vs kc|pr pw sr sw
                     |aq0 rl0 b0 ts0 rv0 wv0 kc0]; try by simpl in Hw.
      have Hlb' : lb' = WeakAxiomatic.LStore rl base vs kc
        := lbl_reidx_w_store rl base vs kc lb' Hri.
      subst lb'.
      have HnW : ¬ wwit G n (x, gcnt x (cd_tr c0)).
      { rewrite Hgc.
        exact (wwit_not_w G n (x, kz) (WeakAxiomatic.LStore rl base vs kc)
                 Hl eq_refl). }
      have Hlbl : gx_lbl G (x, gcnt x (cd_tr c0))
                = Some (WeakAxiomatic.LStore rl base vs kc).
      { destruct Hcl as [[_ H]|[[HW _]|(_ & Hpl & _ & _)]];
          [exact H|by destruct (HnW HW)
          |exfalso; have Hc0 := cpois_lbl_notw c0 _ Hpl;
           by simpl in Hc0]. }
      have Hwix : gwix G (x, gcnt x (cd_tr c0)) = S n
        by rewrite (Hix eq_refl) Hlen.
      have Hmem : (x, gcnt x (cd_tr c0)) ∈ gwrites G.
      { eapply gis_w_gwrites; [exact Hwf|by exists (WeakAxiomatic.LStore rl base vs kc)
                              |by rewrite /gis_w Hlbl]. }
      have Hat : gwrite_at G (S n) = Some (x, gcnt x (cd_tr c0))
        by rewrite -Hwix; apply gwrite_at_gwix.
      have Hmsg : gmsg G (x, gcnt x (cd_tr c0))
                = Some (WMsg base vs (Some x) kc)
        by rewrite /gmsg Hlbl.
      have -> : wlogn n kz (S kz) = S n.
      { rewrite /wlogn (bool_decide_eq_false_2 (S kz ≤ kz)%nat); [done|lia]. }
      have -> : es_msg (EStep x (WeakAxiomatic.LStore rl base vs kc))
              = [WMsg base vs (Some x) kc] by reflexivity.
      exact (wlog_pfx_snoc G n (cd_log_end c0) _ _ Hpfxn Hat Hmsg).
    + (* A NON-WRITE BLOCK: the log does not move *)
      have Hw : lb_is_w lb = false.
      { destruct (lb_is_w lb) eqn:Hb; [|done].
        exfalso. apply Hne. by apply Hiff. }
      have Hw' : lb_is_w lb' = false by eapply lbl_reidx_w_notw.
      rewrite (es_msg_notw (EStep x lb') Hw') app_nil_r.
      have -> : wlogn n kz (S k) = n.
      { rewrite /wlogn (bool_decide_eq_true_2 (S k ≤ kz)%nat); [done|lia]. }
      exact Hpfxn.
Qed.

(** ** 4.1 THE SEGMENT, from the emission and the REDUCED ledger

    (P-1) is [wctx_pres]; (W-1) is [wpol_of_sites]; (O-F) is
    [WeakRvwmoCert3.cpolp_of_rmwfree] (the site datum is RMW-free).  What is
    left at this interface is (W-2) [wub] alone: the restricted (W-4)
    [wnw_seg] is GONE with the split — the carried context no longer
    asserts that the next position is not a witness. *)
Theorem wlk_seg_of_cert (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Nd : nat → CPU → M unit → Prop)
    (k0 kz : nat) (ws0 : wstate) (rowseg : list lbl)
    (es : list eitem) (pfin : pexv6) (m0 : M unit) (rs10 : regstate)
    (fn0 : ofence) (ib0 : oib32) (St : cyc_state) (m20 : M unit)
    (rs20 : regstate) (fn20 : ofence) (ib20 : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  (* (W-2) *)
  wub G (wwit G n) x →
  (* the two side conditions the [csync] iteration names *)
  wrds_free d0 T →
  wnd_ok cpu d0 (wQ G d0 T Nd n x k0 kz) Nd →
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  LDev ∉ es.*1 →
  (∀ i lb, rowseg !! i = Some lb → wQ G d0 T Nd n x k0 kz (k0 + i)%nat lb) →
  cst_ok d0 St →
  wctx G n x kz k0 (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x
    = Some (PHart cpu m20 rs20 fn20 ib20) →
  Nd k0 cpu m0 →
  csync T m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    wctx G n x kz (k0 + length rowseg)%nat (cst_c St') ∧
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat.
Proof.
  intros Hcons Hpc Hub Hrdsf (HNa & HNb & HNbp) Hem Hdev HQ Hok
         Hctx Hp Hnd Hsync Hrelp.
  have Hwf : gwf G by destruct Hcons as (H & _).
  (* THE OLD, GLOBAL TAINT as the CONSTANT taint function: [wrds_free] gives
     the read-set freedom at every block, so the policy's poisoned branch is
     unreachable and the engine's new interface is met by the old one. *)
  have Hpol : ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
      (rds : list wreg) (wrs : list register)
      (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
      (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
      srvwmo_consistent c0 → wctx G n x kz k c0 →
      wQ G d0 T Nd n x k0 kz k lb →
      w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
      dreg_agree (λ nn, nn ∉ (λ _ : nat, T) k) rs1 rs2 →
      (λ k m, Nd k cpu m) k m →
      cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
        cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
        mstep_ok (cand_last_st c0) x lb' ∧
        lbl_reidx_w lb lb' ∧
        wcls_at G (wwit G n) x c0 lb' ∧
        csync ((λ _ : nat, T) (S k)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
        (lb_is_w lb = true →
           clockstep ((λ _ : nat, T) (S k)) m' rs1' fn' ib' m2' rs2' fn2' ib2').
  { intros k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
      Hc Hcx HQ0 Hrp Hag Hn0 Hblk.
    exact (wpol_of_sites G n x cpu d0 T Nd k0 kz Hcons Hpc
             k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
             Hc Hcx HQ0 Hrp Hag
             (Hrdsf cpu ws lb l l rds wrs m rs1 fn ib m' rs1' fn' ib'
                (or_introl Hblk)) Hn0 Hblk). }
  destruct (seg_step_of_segment x cpu d0 (λ _ : nat, T)
              (wQ G d0 T Nd n x k0 kz)
              (wctx G n x kz) (wcls_at G (wwit G n) x)
              (λ k m, Nd k cpu m)
              (λ _ : nat, reflexivity T)
              (wctx_pres G d0 T Nd n x k0 kz Hwf Hub)
              (λ k lb ws l1 l2 rds wrs m rs fn ib m' rs' fn' ib' _ _ Hblk,
                 Hrdsf cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib'
                   (or_intror Hblk))
              HNa HNb HNbp
              Hpol
              (cpolpr_of_cpolp x cpu d0 T (λ k m, Nd k cpu m)
                 (wctx G n x kz) (wcls_at G (wwit G n) x)
                 (wQ G d0 T Nd n x k0 kz)
                 (cpolp_of_rmwfree x cpu d0 T (wctx G n x kz)
                    (wcls_at G (wwit G n) x) (wQ G d0 T Nd n x k0 kz)
                    (λ k lb H, wQ_rmwfree G d0 T Nd n x k0 kz k lb H)))
              k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St m20 rs20 fn20 ib20
              Hem Hdev HQ Hok Hctx Hp Hnd Hsync Hrelp)
    as (St' & tradd & Hstep & Hctx' & Himg & Hpst0 & Hdv0 & _).
  exists St', tradd.
  split_and!; [exact Hstep|exact Hctx'|exact Himg|exact Hpst0|exact Hdv0].
Qed.

(** ** 4.2 THE WALK'S SUPPLY, and the theorem

    [walk_policy] is the per-state obligation the walk consumes: at a state
    whose log is the gmo prefix of length [n], the hart of [G]'s
    [(n+1)]-st write has a CERTIFIED SEGMENT through that write.  §4.1 is
    what builds it; the two bookkeeping equations beside it are (O-E). *)
Definition walk_policy (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) : Prop :=
  ∀ St n, wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
  ∃ (x : agent) (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (pre : list lbl) (tradd : list estep) (St' : cyc_state) (w : geid),
    (* the graph side: the segment's exit IS [G]'s [(n+1)]-st write *)
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some (WMsg base vs (Some x) kc) ∧
    (* the segment: hart [x]'s stretch through that write *)
    Forall (λ lb, lb_is_w lb = false) pre ∧
    seg_step d0 (SegOut x (pre ++ [WeakAxiomatic.LStore rl base vs kc])
                   (cd_end (cst_c St)) tradd) St St' ∧
    (* the image (free from [cpol_ctx], §4.1) and (O-E) *)
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat.

Theorem walk_policy_steps boot d0 N G :
  walk_policy boot d0 N G → walk_steps boot d0 N G.
Proof.
  intros Hpol St n Hinv Hn.
  destruct (Hpol St n Hinv Hn)
    as (x & rl & base & vs & kc & pre & tradd & St' & w &
        Hw & Hm & Hpre & Hstep & Himg & Hpst & Hdv).
  by eapply (wlk_step_of_seg G d0 St St' n _ pre rl base vs kc w).
Qed.

(** THE THEOREM. *)
Theorem walk_supply_of_policy (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     walk_policy boot d0 N (gd_g GD)) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hpol. apply walk_supply_of_steps.
  intros GD Hcons Hq. by apply walk_policy_steps, Hpol.
Qed.

(* ====================================================================== *)
(** * 4.5 THE CHAINED WALK: A FROZEN WITNESS SET, AND AN INVARIANT THAT
       CARRIES WHAT THE NEXT STEP NEEDS

    §4.1–§4.4 build ONE segment at ONE state.  Chaining them generically
    needs two things the interface above does not have.

    THE WITNESS SET MUST BE FROZEN.  [wctx] carries [cpol_ctx G (wwit G n) x]
    — the certification context AT THE CURRENT WRITE COUNT — and [wwit G n]
    SHRINKS as [n] grows (a read whose source is [≤ n+1] is no longer a
    witness at [n+1]).  [ctrace_prefix] is not monotone in that direction:
    a position substituted at [n] carries the candidate's LATEST-source
    read, which is NOT [G]'s label, so the [¬ W] arm of [ctp_step] cannot
    take over when the position leaves [W].  (And it really is the wrong
    label: the substituted read read the latest bytes AT ITS TIME, before
    the write that would have made it true was appended.)  So the walk
    carries ONE witness set [W] for its whole run, and the log-decided
    [wwit G n] appears only in the SITE DATUM that classifies each newly
    visited position ([wsite_cls]): "not in [W] and its sources are already
    in the log" or "in [W], a genuine witness at this count, and carrying
    the substitution data".  [ctrace_prefix] is then stable under appends
    for free — the set never moves.

    THE INVARIANT MUST CARRY THE PROCESS STATES.  [wlk_inv] records the
    candidate, the image, the boot supply and the log prefix; a segment
    additionally needs, for the hart it runs, that hart's EMISSION from its
    current row position and the identification of the walk state's process
    with the emission's own.  [wlk_inv'] carries both, for EVERY hart, and
    [wlk_seg_of_cert2]'s frame conclusions ([WeakRvwmoCert3.cert_segment']'s
    own) re-establish them: the acting hart's advance to the emission's next
    state, every other hart untouched.

    The two remaining bookkeeping clauses are the ROW POSITIONS: hart [x]'s
    replayed count is exactly the boundary between its writes the log has
    reached ([wpos_lo]) and those it has not ([wpos_hi]).  Together with
    [grule14] they are what makes "the next write's hart stands at or before
    it, with no write in between" a THEOREM rather than a per-state datum. *)

(** Hart [x]'s row, as a list; [gx_lbl] is its lookup. *)
Definition qrow (G : gexec) (x : agent) : list lbl :=
  default [] (gx_prog G !! x).

Lemma qrow_lbl (G : gexec) (x : agent) (k : nat) :
  gx_lbl G (x, k) = qrow G x !! k.
Proof. rewrite /gx_lbl /qrow /=. by destruct (gx_prog G !! x). Qed.

(** ** 4.5a The row fold, over a segment *)

Lemma row_ws_aux_app (t : nat) (ws : wstate) (r1 r2 : list lbl) :
  row_ws_aux t ws (r1 ++ r2)
  = row_ws_aux (t + length r1)%nat (row_ws_aux t ws r1) r2.
Proof.
  revert t ws. induction r1 as [|lb r1 IH]; intros t ws.
  - by rewrite /= Nat.add_0_r.
  - rewrite /= IH.
    by replace (S t + length r1)%nat with (t + S (length r1))%nat by lia.
Qed.

Lemma row_ws_seg (row : list lbl) (k0 L : nat) :
  (k0 ≤ length row)%nat →
  row_ws_aux k0 (row_ws row k0) (take L (drop k0 row))
  = row_ws row (k0 + L)%nat.
Proof.
  intros Hk. rewrite /row_ws -(take_take_drop row k0 L) row_ws_aux_app.
  by rewrite (length_take_le row k0 Hk).
Qed.

(** ** 4.5b The per-hart emission tail, and the process identification *)

(** "Hart [x]'s emission, from row position [k] on, starts at [p]". *)
Definition wemit (d0 : dev_state) (G : gexec) (x : agent) (k : nat)
    (p : pexv6) : Prop :=
  ∃ (es : list eitem) (pfin : pexv6),
    hemit (λ _, d0) k (row_ws (qrow G x) k) (drop k (qrow G x)) p es pfin ∧
    (** DEVICE-QUIET, which [WeakRvwmoSupply.em_devfree] supplies and
        [WeakRvwmoCert3.cert_segment''] consumes (it is what keeps the PLIC
        arm of [WeakEvProv.pstep_hw] out of a divergent tail). *)
    LDev ∉ es.*1.

(** The walk state's process for a hart IS the emission's, off the taint
    (which is EMPTY at the walk, so this is agreement on every data
    register).  Stated as an implication so that a hart which is not a
    [PHart] at all — the disk — costs nothing. *)
Definition pex_dag (T : list wreg) (p q : pexv6) : Prop :=
  ∀ cpu m rs fn ib, p = PHart cpu m rs fn ib →
    ∃ rs', q = PHart cpu m rs' fn ib ∧ dreg_agree (λ nn, nn ∉ T) rs rs'.

Lemma pex_dag_refl T p : pex_dag T p p.
Proof. intros cpu m rs fn ib ->. exists rs. split; [done|apply dreg_agree_refl]. Qed.


(* ---------------------------------------------------------------------- *)
(** ** 4.5b' THE FUSED RMW's POLICY, POINTWISE

    Moved here from [WeakRvwmoWalk2] §3 and GENERALISED in the witness set,
    so that [wsite_ok'] below no longer has to ask for [lb_rmwfree]: an
    [LRmw] position is SERVED rather than excluded.

    [WeakRvwmoCert3.cpolp] is [wpol]'s twin for the [HEpair] block, and it
    is discharged the same way: the untainted mirror
    ([cert_block_pair_mirror]) plus the RMW admissibility
    ([WeakRvwmoCert3.cert_rmw_ok]), whose only real input is "the RMW's read
    sources are in the log" — which for an RMW is not an extra assumption
    but a consequence of [gatomicity] once the log's next entry is the RMW's
    own write.  [cpolp_of_rmwfree] survives as the RMW-free instance and is
    still what the UNCHAINED path (§4.4) uses. *)

(** [src_in_log_of_pfx] does not fire at an RMW — it is stated at [LLoad].
    The same proof at [lb_rd] covers both. *)
Theorem src_in_log_of_pfx' (G : gexec) (n : nat) (c : cand) (e : geid)
    (l : lbl) (base : Z) (ts : list nat) (vs : list (bv 8)) :
  gload_value G →
  cd_img c = gx_img G →
  wlog_pfx G n (cd_log_end c) →
  gx_lbl G e = Some l →
  lb_rd l = Some (base, ts, vs) →
  length vs = length ts →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ n)%nat) →
  src_in_log c base ts vs.
Proof.
  intros Hlv Himg [Hlen Hpfx] Hl Hrd Hlenv Hle.
  split; [exact Hlenv|]. intros j t v Hj Hv.
  have Hrb : greads_byte G e (WeakAxiomatic.acc_addr base j) t v
    by (exists l, base, ts, vs, j).
  destruct (Hlv _ _ _ _ Hrb) as [Hval _].
  have Ht : (t ≤ n)%nat := Hle j t Hj.
  destruct t as [|t'].
  - by rewrite log_byte_0 Himg.
  - destruct Hval as (w & Hw & Hwb & _).
    rewrite log_byte_S.
    have Hlt : (t' < n)%nat by lia.
    rewrite -(Hpfx t' w Hlt Hw).
    destruct (gmsg G w) as [mm|] eqn:Hm.
    + rewrite /=. by apply (gmsg_byte G w _ v mm).
    + exfalso. destruct Hwb as (l0 & base' & vs' & j' & Hl0 & Hwr & _).
      by rewrite /gmsg Hl0 Hwr in Hm.
Qed.

(** THE RMW SITE DATUM. *)
Definition wrmw_site (G : gexec) (n : nat) (x : agent) (p : nat) (lb : lbl)
    : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  (∀ (base : Z) (ts : list nat) (vs : list (bv 8)),
     lb_rd lb = Some (base, ts, vs) →
     ∀ (j : nat) t, ts !! j = Some t → (t ≤ n)%nat) ∧
  gwix G (x, p) = S n.

(** THE PAIR POLICY AT AN ALIGNED CANDIDATE.  [W] is arbitrary: what the
    old [wwit]-specific statement derived from "an RMW is not a load" is
    now the explicit premise [¬ W (x, gcnt x (cd_tr c0))], which the site
    classification supplies at an RMW position for exactly that reason. *)
Theorem wcpolp_at (G : gexec) (W : geid -> Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (c0 : cand) (ws : wstate) (lb : lbl)
    (l1 l2 : wlabel) (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32)
    (T : list wreg) :
  rvwmo_minus_consistent G ->
  cd_img c0 = gx_img G ->
  wlog_pfx G n (cd_log_end c0) ->
  srvwmo_consistent c0 ->
  cpol_ctx G W x c0 ->
  ~ W (x, gcnt x (cd_tr c0)) ->
  wrmw_site G n x (gcnt x (cd_tr c0)) lb ->
  dreg_agree (fun nn => nn ∉ T) rs1 rs2 ->
  rds_ok (fun nn => nn ∉ T) rds ->
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' ->
  ∃ rs2',
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
    mstep_ok (cand_last_st c0) x lb ∧
    wcls_at G W x c0 lb ∧
    dreg_agree (λ nn, nn ∉ T) rs1' rs2'.
Proof.
  intros Hcons Himg Hpfx Hc Hctx HnW (Hl & Hbnd & Hix) Hag Hrds Hblk.
  pose proof Hcons as (Hwf & _ & Hlv & _).
  destruct (cert_block_pair_mirror (λ nn, nn ∉ T) cpu d0 ws lb l1 l2 rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk Hrds Hag)
    as (rs2' & Hblk2 & Hag2).
  have Hrmw : ¬ lb_rmwfree lb
    := cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' Hblk.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw
                 |aq rl base ts rvs wvs kc]; [by destruct (Hrmw I)..|].
  destruct Hctx as (ev & Hgt & Hub).
  destruct (gshape G Hwf _ _ Hl) as (Hne & Hlenw & Hlenr).
  have Hlenlog : length (cd_log_end c0) = n by (destruct Hpfx as [H _]; exact H).
  have Hsrc : src_in_log c0 base ts rvs.
  { apply (src_in_log_of_pfx' G n c0 (x, gcnt x (cd_tr c0)) _ base ts rvs
            Hlv Himg Hpfx Hl eq_refl Hlenr).
    intros j t Hj. by apply (Hbnd base ts rvs eq_refl j t). }
  exists rs2'. split_and!.
  - exact Hblk2.
  - apply (cert_rmw_ok G c0 ev W x aq rl base ts rvs wvs kc
             Hcons Hgt Hc Hl ltac:(by rewrite Hix Hlenlog));
      [|exact Hsrc].
    intros j t Hj. rewrite Hlenlog. by apply (Hbnd base ts rvs eq_refl j t).
  - apply (wcls_of_pfx G W n x c0 _ Hpfx Hl HnW).
    intros _. exact Hix.
  - exact Hag2.
Qed.

(** ** 4.5c The frozen witness set: its side condition, and the site datum *)

(** (W-2) FOR EVERY HART AT ONCE.  [wub] is stated at one hart and one
    snoc; the chained walk re-establishes the context for whichever hart
    runs next, so it asks for the bound at every hart's own next position.
    [wub] follows ([wubA_wub]). *)
Definition wubA (G : gexec) (W : geid → Prop) : Prop :=
  ∀ (c : cand) (ev : nat → geid) (y : agent),
    ctrace_prefix G c ev W → wit_fence_ub G c ev W (y, gcnt y (cd_tr c)).

Lemma wubA_wub G W x : wubA G W → wub G W x.
Proof.
  intros Hub c0 lb' ev' Hct.
  rewrite -(gcnt_cand_snoc_self c0 x lb'). by apply Hub.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.5c' THE POISONED BLOCK, THE EXIT, AND THE FAULT BOUNDARY

    THE PROBLEM the per-hart taint migration exposes.  [wsupply]'s old
    [wrds_free d0 T] said "NO emitted block, of any hart, at any node, reads
    a carrier in [T]" — false at any real execution for [T ≠ []], so the
    capstone's [∃ W T] was satisfiable only at [T = []], i.e. only for
    witnesses whose value is never used.  The honest replacement is a
    PER-HART, ACCUMULATED taint [tm x : nat → list wreg] (monotone in the
    row position) plus a CASE SPLIT at every block:

      - the block reads NO tainted carrier: the certified run MIRRORS it
        ([WeakRvwmoCert2.cert_block_mirror]) and the two existing routes
        (G's own label at a non-witness, the latest-source read at a
        witness) serve it exactly as before;

      - the block DOES read a tainted carrier — it is POISONED.  The
        address it computes is the certified run's own, so no mirror
        exists.  Its certified label is a load of the MACHINE's footprint
        served by the candidate's latest sources ([pois_ok]), related to
        [G]'s only by [WeakRvwmoCert2.lbl_poisoned], classified by the
        POISONED arm of [WeakRvwmoGlue2.cstep_cls], and the two runs are in
        [csync]'s DIVERGED arm afterwards, with the taint grown by the
        block's tail.

    WHY A WRITE IS NEVER POISONED, and where that is paid for: a store
    whose address or data depends on the witness has a [gd_deps] edge from
    the witness, hence the witness is gmo-below it, hence the witness is
    not ABOVE the segment's exit — so the exit's own read set misses the
    taint.  That argument is DEC-7 dynamic provenance
    ([WeakRvwmoConf.dstep] over the emission's items, the induction
    [WeakRvwmoPinBridge2] runs for the checker) and it is NOT discharged
    here: it is stated as the site obligation [wexit_ut] and listed in §7's
    ledger.  Every other use of the old [wrds_free] is gone. *)

(** THE CERTIFIED LABEL AT A POISONED POSITION: a plain load of the
    machine's own footprint, reading the candidate's LATEST sources.
    [latest_bytes_ok] is what makes it admissible with no floor obligation
    ([WeakRvwmoCert2.cert_read_witness]) — and it is also, read the other
    way, the statement that the address the poisoned block computed is
    MAPPED (its bytes exist in the candidate's image/log). *)
Definition pois_ok (c : cand) (lb2 : lbl) : Prop :=
  ∃ (base : Z) (n : nat),
    lb2 = latest_read_lbl c false base n ∧ latest_bytes_ok c base n.

Lemma pois_ok_mstep (c : cand) (x : agent) (lb2 : lbl) :
  srvwmo_consistent c → pois_ok c lb2 → mstep_ok (cand_last_st c) x lb2.
Proof. intros Hc (base & n & -> & Hb). by apply cert_read_witness. Qed.

Lemma pois_ok_cpois (c : cand) (lb2 : lbl) : pois_ok c lb2 → cpois_lbl c lb2.
Proof. intros (base & n & -> & _). by exists base, n. Qed.

Lemma pois_ok_notw (c : cand) (lb2 : lbl) : pois_ok c lb2 → lb_is_w lb2 = false.
Proof. intros H. exact (cpois_lbl_notw c lb2 (pois_ok_cpois c lb2 H)). Qed.

(** THE CLASSIFICATION AT A POISONED POSITION — [cstep_cls]'s third arm. *)
Theorem wcls_of_pois (G : gexec) (W : geid → Prop) (x : agent) (c0 : cand)
    (lb0 lb' : lbl) :
  gx_lbl G (x, gcnt x (cd_tr c0)) = Some lb0 → lb_is_w lb0 = false →
  cpois_lbl c0 lb' →
  gx_lbl G (x, gcnt x (cd_tr c0)) ≠ Some lb' →
  ¬ (∃ (base : Z) (n : nat) (ts0 : list nat) (vs0 : list (bv 8)),
       gx_lbl G (x, gcnt x (cd_tr c0))
         = Some (WeakAxiomatic.LLoad false base ts0 vs0) ∧
       length ts0 = n ∧ lb' = latest_read_lbl c0 false base n) →
  cstep_pois_ok G x c0 lb' →
  wcls_at G W x c0 lb'.
Proof.
  intros Hl Hw Hpl Hne Hnw Hstp. split_and!.
  - right; right. by split_and!; [by exists lb0|exact Hpl| |].
  - intros Hw'. by rewrite (cpois_lbl_notw c0 lb' Hpl) in Hw'.
  - exact Hstp.
Qed.

(** THE EXIT'S READ-SET FREEDOM (see the comment above): the block of a
    WRITE position reads no carrier the hart's taint holds.  This is the
    only surviving descendant of [wrds_free], and it is asked at WRITE
    positions only. *)
Definition wexit_ut (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (p : nat) : Prop :=
  ∀ (cpu : CPU) (ws : wstate) (lb : lbl) (l1 l2 : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs' : regstate)
    (fn' : ofence) (ib' : oib32),
    Nd p cpu m → lb_is_w lb = true →
    (cblk cpu d0 ws lb l1 rds wrs m rs fn ib m' rs' fn' ib' ∨
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib') →
    rds_ok (λ nn, nn ∉ T) rds.

(** THE FAULT BOUNDARY, NAMED.  A poisoned load's address comes from a
    register the certified run does not agree with the emission on, so
    NOTHING in the model says it translates without an exception; if it
    faults, the Sail step takes the trap path and the certified run is
    executing a DIFFERENT instruction stream (the handler), which the row
    correspondence cannot describe at all.  [poisoned_no_fault] is exactly
    the sentence "it does not fault": from the same node, at the certified
    run's registers, there IS a block whose label is a load
    ([lbl_poisoned]) rather than an exception path.

    IT IS A KERNEL CLAIM, not a graph fact — xv6's kernel pointers are
    kernel-range and the kernel's direct map is identity, which makes it
    plausible, but the argument is [l2_claim]'s kind and it is recorded in
    §7's ledger beside it.  If the instance machinery makes the exception
    path visible, it appears at [WeakEvInst.pnode_step]'s [MemRead] arm as
    an [Arch.abort] answer: the read node still steps (the abort is one of
    its answers) but [hlbl_realizes] does not relate the resulting
    [WeakPromise] label to any [WeakAxiomatic.LLoad], so such a run is NOT
    a [cblk] at all — which is why the boundary shows up here as an
    EXISTENCE claim rather than as an extra disjunct. *)
Definition poisoned_no_fault (d0 : dev_state) (T : list wreg)
    (Nd : nat → CPU → M unit → Prop) (p : nat) : Prop :=
  ∀ (cpu : CPU) (ws : wstate) (lb : lbl) (l : wlabel) (rds : list wreg)
    (wrs : list register) (m : M unit) (rs1 rs2 : regstate) (fn : ofence)
    (ib : oib32) (m' : M unit) (rs1' : regstate) (fn' : ofence)
    (ib' : oib32),
    Nd p cpu m → lb_is_w lb = false →
    ¬ rds_ok (λ nn, nn ∉ T) rds →
    dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb2 : lbl) (l2 : wlabel) (rds2 : list wreg) (wrs2 : list register)
      (m2 : M unit) (rs2' : regstate) (fn2' : ofence) (ib2' : oib32),
      cblk cpu d0 ws lb2 l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn2' ib2' ∧
      lbl_poisoned lb lb2.

(** THE POISONED SITE DATUM: [poisoned_no_fault] together with what the
    candidate must be able to serve ([pois_ok]) and the re-convergence the
    iteration needs, at the GROWN taint [T'].  [T] is the taint at the
    block's own position, [T'] at its successor's — this is where the
    accumulation happens. *)
Definition wpois_site (G : gexec) (W : geid → Prop) (x : agent)
    (d0 : dev_state) (T T' : list wreg)
    (Nd : nat → CPU → M unit → Prop) (p : nat) : Prop :=
  ∀ (c0 : cand) (cpu : CPU) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs1 rs2 : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs1' : regstate)
    (fn' : ofence) (ib' : oib32),
    Nd p cpu m → lb_is_w lb = false →
    gcnt x (cd_tr c0) = p →
    ¬ rds_ok (λ nn, nn ∉ T) rds →
    dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb2 : lbl) (l2 : wlabel) (rds2 : list wreg) (wrs2 : list register)
      (m2 : M unit) (rs2' : regstate) (fn2' : ofence) (ib2' : oib32),
      cblk cpu d0 ws lb2 l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn2' ib2' ∧
      lbl_poisoned lb lb2 ∧
      pois_ok c0 lb2 ∧
      (** THE CLASSIFICATION at the appended poisoned label, which carries
          the FLOOR OBLIGATION [WeakRvwmoGlue2.cstep_pois_ok] — the one
          thing a later TRUE read of this hart needs of it — and the two
          discriminators that put the position on the poisoned arm rather
          than the true or the witness one. *)
      wcls_at G W x c0 lb2 ∧
      csync T' m' rs1' fn' ib' m2 rs2' fn2' ib2'.

(** … and the residual it CONTAINS, extracted: the datum is strictly
    stronger than the fault boundary, so naming the boundary costs nothing
    and makes the debt auditable. *)
Lemma wpois_no_fault (G : gexec) (W : geid → Prop) (x : agent)
    (d0 : dev_state) (T T' : list wreg) (Nd : nat → CPU → M unit → Prop)
    (p : nat) (c0 : cand) :
  gcnt x (cd_tr c0) = p →
  wpois_site G W x d0 T T' Nd p → poisoned_no_fault d0 T Nd p.
Proof.
  intros Hgc H cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hnd Hw Hrds Hag Hblk.
  destruct (H c0 cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
              Hnd Hw Hgc Hrds Hag Hblk)
    as (lb2 & l2 & rds2 & wrs2 & m2 & rs2' & fn2' & ib2' & Hblk2 & Hpo & _).
  by exists lb2, l2, rds2, wrs2, m2, rs2', fn2', ib2'.
Qed.

(** THE READ SET IS DECIDABLE against a taint LIST, which is what makes the
    case split above a tactic rather than a classical assumption. *)
Lemma rds_ok_dec (T rds : list wreg) :
  rds_ok (λ nn, nn ∉ T) rds ∨ ¬ rds_ok (λ nn, nn ∉ T) rds.
Proof.
  destruct (decide (Forall (λ nn, nn ∉ T) rds)) as [Hf|Hf].
  - left. intros n Hn. by eapply Forall_forall in Hf.
  - right. intros H. apply Hf, Forall_forall. exact H.
Qed.

(** THE CLASSIFICATION, AS A SITE DATUM.  Exactly the two routes §4.0c
    serves, at the FROZEN set: a position outside [W] must have its sources
    in the log already (the true route), a position inside it must be a
    genuine witness at this count and carry [wwit_site] (the substituted
    route). *)
Definition wsite_cls (G : gexec) (W : geid → Prop) (d0 : dev_state)
    (tm : nat → list wreg) (Nd : nat → CPU → M unit → Prop) (n : nat)
    (x : agent) (p : nat) : Prop :=
  (¬ W (x, p) ∧ wsrc_le G n (x, p)) ∨
  (W (x, p) ∧ wwit G n (x, p) ∧ wwit_site G d0 (tm (S p)) Nd n x p).

(** [wsite_ok'] gains the two clauses the per-hart taint needs: the EXIT's
    read-set freedom ([wexit_ut], asked at write positions only) and the
    POISONED arm ([wpois_site], asked only when the block's read set
    actually meets the hart's taint at this position).  At [tm ≡ λ _, []]
    both are FREE — [rds_ok (∉ [])] always holds, so [wexit_ut] is
    [not_elem_of_nil] and [wpois_site]'s premise is refutable. *)
Definition wsite_ok' (G : gexec) (W : geid → Prop) (d0 : dev_state)
    (tm : nat → list wreg) (Nd : nat → CPU → M unit → Prop) (n : nat)
    (x : agent) (p : nat) (lb : lbl) : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  (lb_is_w lb = true → gwix G (x, p) = S n) ∧
  (¬ lb_rmwfree lb → wrmw_site G n x p lb) ∧
  wsite_cls G W d0 tm Nd n x p ∧
  wexit_ut d0 (tm p) Nd p ∧
  wpois_site G W x d0 (tm p) (tm (S p)) Nd p.

Definition wQ' (G : gexec) (W : geid → Prop) (d0 : dev_state)
    (tm : nat → list wreg) (Nd : nat → CPU → M unit → Prop) (n : nat)
    (x : agent) (k0 kz : nat) (k : nat) (lb : lbl) : Prop :=
  (k0 ≤ k)%nat ∧ (k ≤ kz)%nat ∧
  wsite_ok' G W d0 tm Nd n x k lb ∧
  (lb_is_w lb = true ↔ k = kz).

Lemma wQ'_rmw_site G W d0 tm Nd n x k0 kz k lb :
  wQ' G W d0 tm Nd n x k0 kz k lb → ¬ lb_rmwfree lb → wrmw_site G n x k lb.
Proof. by intros (_ & _ & (_ & _ & H & _) & _). Qed.

Lemma wQ'_lbl G W d0 tm Nd n x k0 kz k lb :
  wQ' G W d0 tm Nd n x k0 kz k lb → gx_lbl G (x, k) = Some lb.
Proof. by intros (_ & _ & (H & _) & _). Qed.

Lemma wQ'_exit_ut G W d0 tm Nd n x k0 kz k lb :
  wQ' G W d0 tm Nd n x k0 kz k lb → wexit_ut d0 (tm k) Nd k.
Proof. by intros (_ & _ & (_ & _ & _ & _ & H & _) & _). Qed.

(** A WRITE POSITION IS NEVER IN [W] — the site datum's own content. *)
Lemma wsite_cls_notW G W d0 tm Nd n x p lb :
  gx_lbl G (x, p) = Some lb → lb_is_w lb = true →
  wsite_cls G W d0 tm Nd n x p → ¬ W (x, p).
Proof.
  intros Hl Hw [[H _]|[_ [HW _]]]; [exact H|].
  by destruct (wwit_not_w G n (x, p) lb Hl Hw).
Qed.

(** THE WALK'S CARRIED CONTEXT, at the frozen set. *)
(** THE POISONED INVARIANT, hart-generic and [ev]-generic
    ([WeakRvwmoGlue2.pois_ok_hart_ev] makes the second free).  This is what
    the walk carries in place of a universal over candidates — which would
    be FALSE, since [ctrace_prefix] permits a poisoned step at any read
    position of any candidate. *)
Definition wpois_inv (G : gexec) (W : geid → Prop) (c : cand) : Prop :=
  ∀ ev, ctrace_prefix G c ev W → ∀ y, pois_ok_hart G c ev y.

Definition wctx' (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (kz : nat) (k : nat) (c : cand) : Prop :=
  (∃ ev, ctrace_prefix G c ev W) ∧
  wpois_inv G W c ∧
  gcnt x (cd_tr c) = k ∧
  wlog_pfx G (wlogn n kz k) (cd_log_end c).

Lemma wctx'_cpol G W n x kz k c :
  wubA G W → wctx' G W n x kz k c → cpol_ctx G W x c.
Proof.
  intros Hub ((ev & Hct) & Hpd & _ & _). exists ev.
  split_and!; [exact Hct|by apply Hub|by apply Hpd].
Qed.

(** ** 4.5d The policy, at the frozen set *)

Theorem wblk_pol_at' (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (tm : nat → list wreg)
    (Nd : nat → CPU → M unit → Prop) (c0 : cand) (ws : wstate) (lb : lbl)
    (l : wlabel) (rds : list wreg) (wrs : list register) (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (m' : M unit)
    (rs1' : regstate) (fn' : ofence) (ib' : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G W →
  (∀ k, tm k ⊆ tm (S k)) →
  srvwmo_consistent c0 →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G W x c0 →
  wsite_ok' G W d0 tm Nd n x (gcnt x (cd_tr c0)) lb →
  dreg_agree (λ nn, nn ∉ tm (gcnt x (cd_tr c0))) rs1 rs2 →
  Nd (gcnt x (cd_tr c0)) cpu m →
  cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
  ∃ (lb' : lbl) (l' : wlabel) (rds' : list wreg) (wrs' : list register)
    (rs2' : regstate) (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
    cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
    mstep_ok (cand_last_st c0) x lb' ∧
    lbl_reidx_w lb lb' ∧
    wcls_at G W x c0 lb' ∧
    csync (tm (S (gcnt x (cd_tr c0)))) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
    (lb_is_w lb = true →
       clockstep (tm (S (gcnt x (cd_tr c0)))) m' rs1' fn' ib'
         m2' rs2' fn2' ib2').
Proof.
  intros Hcons Hpc Hmono Hc Himg Hpfx Hctx Hsite Hag Hnd Hblk.
  pose proof Hcons as (Hwf & _ & Hlv & _).
  pose proof Hsite as (Hl & Hix & Hrmw & Hcl & Hut & Hpois).
  set (T := tm (gcnt x (cd_tr c0))).
  set (T' := tm (S (gcnt x (cd_tr c0)))).
  have HTT' : T ⊆ T' := Hmono _.
  destruct (rds_ok_dec T rds) as [Hrds|Hnrds]; last first.
  { (* ------------------------ THE POISONED ROUTE --------------------- *)
    have Hw : lb_is_w lb = false.
    { destruct (lb_is_w lb) eqn:Hb; [exfalso|reflexivity].
      apply Hnrds.
      exact (Hut cpu ws lb l l rds wrs m rs1 fn ib m' rs1' fn' ib'
               Hnd Hb (or_introl Hblk)). }
    destruct (Hpois c0 cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
                Hnd Hw eq_refl Hnrds Hag Hblk)
      as (lb2 & l2 & rds2 & wrs2 & m2 & rs2' & fn2' & ib2' &
          Hblk2 & Hlp & Hpok & Hcls2 & Hsync).
    exists lb2, l2, rds2, wrs2, rs2', m2, fn2', ib2'.
    split_and!;
      [exact Hblk2|by apply pois_ok_mstep|by apply lbl_reidx_w_pois
      |exact Hcls2|exact Hsync|by rewrite Hw]. }
  destruct (cert_block_mirror (λ nn, nn ∉ T) cpu d0 ws lb l rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk Hrds Hag)
    as (rs2' & Hblk2 & Hag2').
  have Hag2 : dreg_agree (λ nn, nn ∉ T') rs1' rs2'
    := dreg_agree_taint_mono T T' rs1' rs2' HTT' Hag2'.
  destruct Hcl as [[HnW Hle]|[HW [Hwit Hwsite]]].
  - (* ------------------------- THE TRUE ROUTE ------------------------- *)
    exists lb, l, rds, wrs, rs2', m', fn', ib'.
    split_and!; [exact Hblk2| |apply lbl_reidx_w_refl
                |by apply (wcls_of_pfx G W n x c0 lb)
                |(left; split_and!;
                    [reflexivity|reflexivity|reflexivity|exact Hag2])
                |(intros _; split_and!;
                    [reflexivity|reflexivity|reflexivity|exact Hag2])].
    destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw
                   |aq rl base ts rvs wvs kc].
    + apply (cpol_read G W x c0 aq base ts vs Hcons Hpc Hctx HnW Hl).
      apply (src_in_log_of_pfx G n c0 (x, gcnt x (cd_tr c0)) aq base ts vs
               Hlv Himg Hpfx Hl (gshape G Hwf _ _ Hl) Hle).
    + apply cert_write_ok. exact (gshape G Hwf _ _ Hl).
    + apply cert_fence_ok.
    + (* THE FUSED RMW, served by 4.5b' *)
      destruct Hctx as (ev & Hgt & _).
      destruct (Hrmw ltac:(intros HH; exact HH)) as (Hl2 & Hbnd & Hix2).
      have Hlenlog : length (cd_log_end c0) = n
        by (destruct Hpfx as [Hlg _]; exact Hlg).
      destruct (gshape G Hwf _ _ Hl) as (Hne & Hlenw & Hlenr).
      have Hsrc : src_in_log c0 base ts rvs.
      { apply (src_in_log_of_pfx' G n c0 (x, gcnt x (cd_tr c0)) _ base ts rvs
                Hlv Himg Hpfx Hl eq_refl Hlenr).
        intros j t Hj. by apply (Hbnd base ts rvs eq_refl j t). }
      apply (cert_rmw_ok G c0 ev W x aq rl base ts rvs wvs kc
               Hcons Hgt Hc Hl ltac:(by rewrite Hix2 Hlenlog)); [|exact Hsrc].
      intros j t Hj. rewrite Hlenlog. by apply (Hbnd base ts rvs eq_refl j t).
  - (* ------------------------ THE WITNESS ROUTE ----------------------- *)
    pose proof Hwit as (aq & base & ts & vs & Hl' & _).
    have Hlb : lb = WeakAxiomatic.LLoad aq base ts vs.
    { rewrite Hl' in Hl. by injection Hl as <-. }
    subst lb.
    destruct Hwsite as (Hgs & Hvf).
    destruct (Hgs c0 aq base ts vs Himg Hpfx Hl') as (-> & Hbytes).
    destruct (Hvf cpu ws false base ts vs l rds wrs
                m rs2 fn ib m' rs2' fn' ib'
                (wit_tvs c0 base (length ts)) Hnd Hblk2
                (wit_tvs_length c0 base (length ts)))
      as (l2 & rds2 & wrs2 & m2 & Hblk3 & Hsync).
    rewrite (wit_tvs_lbl c0 false base (length ts)) in Hblk3.
    exists (latest_read_lbl c0 false base (length ts)), l2, rds2, wrs2, rs2',
      m2, fn', ib'.
    split_and!.
    + exact Hblk3.
    + by apply cert_read_witness.
    + right; left. rewrite /latest_read_lbl /=. split_and!;
        [reflexivity|reflexivity|reflexivity| |].
      * by rewrite /lrd_ts length_fmap length_seq.
      * apply lrd_length.
    + by apply (wcls_of_wit G W x c0 base ts vs).
    + exact (csync_regs T' m' m2 rs2' rs1' rs2' fn' ib' Hsync Hag2).
    + intros Hw. by simpl in Hw.
Qed.

Definition wpol' (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (tm : nat → list wreg)
    (Nd : nat → CPU → M unit → Prop) (k0 kz : nat) : Prop :=
  ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    wctx' G W n x kz k c0 →
    wQ' G W d0 tm Nd n x k0 kz k lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ nn, nn ∉ tm k) rs1 rs2 →
    Nd k cpu m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx_w lb lb' ∧
      wcls_at G W x c0 lb' ∧
      csync (tm (S k)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lb_is_w lb = true →
         clockstep (tm (S k)) m' rs1' fn' ib' m2' rs2' fn2' ib2').

Theorem wpol'_of_sites (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (tm : nat → list wreg)
    (Nd : nat → CPU → M unit → Prop) (k0 kz : nat) :
  rvwmo_minus_consistent G →
  W_poloc_closed G W →
  wubA G W →
  (∀ k, tm k ⊆ tm (S k)) →
  wpol' G W n x cpu d0 tm Nd k0 kz.
Proof.
  intros Hcons Hpc Hub Hmono k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1'
    fn' ib' Hc Hctx (Hk0 & Hkz & Hsite & _) Hrelp Hag Hnd Hblk.
  pose proof Hctx as (_ & _ & Hgc & Hpfx).
  have Hcp : cpol_ctx G W x c0 := wctx'_cpol G W n x kz k c0 Hub Hctx.
  have Himg : cd_img c0 = gx_img G.
  { destruct Hcp as (ev & Hgt & _). exact (ctp_img G c0 ev _ Hgt). }
  have Hpfx' : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  rewrite -Hgc.
  apply (wblk_pol_at' G W n x cpu d0 tm Nd c0 ws lb l rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Hpc Hmono Hc Himg Hpfx' Hcp);
    [by rewrite Hgc|by rewrite Hgc|by rewrite Hgc|exact Hblk].
Qed.

(** ** 4.5e The context is preserved, at the frozen set *)
Theorem wctx'_pres (G : gexec) (W : geid → Prop) (d0 : dev_state)
    (tm : nat → list wreg) (Nd : nat → CPU → M unit → Prop) (n : nat)
    (x : agent) (k0 kz : nat) :
  gwf G →
  wubA G W →
  ∀ (k : nat) (c0 : cand) (lb lb' : lbl),
    wctx' G W n x kz k c0 → srvwmo_consistent c0 →
    wQ' G W d0 tm Nd n x k0 kz k lb →
    lbl_reidx_w lb lb' → mstep_ok (cand_last_st c0) x lb' →
    wcls_at G W x c0 lb' →
    wctx' G W n x kz (S k) (cand_snoc c0 (EStep x lb')).
Proof.
  intros Hwf Hub k c0 lb lb' Hctx Hc
         (Hk0 & Hkz & Hsite & Hiff) Hri Hok (Hcl & Hix & Hstp).
  pose proof Hctx as ((ev & Hct) & Hpd & Hgc & Hpfx).
  have Hpfxn : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  have Hlen : length (cd_log_end c0) = n by destruct Hpfxn as [H _].
  have Hgc2 : gcnt x (cd_tr (cand_snoc c0 (EStep x lb'))) = S k
    by rewrite gcnt_cand_snoc_self Hgc.
  split_and!.
  - exists (ev_snoc c0 ev (x, gcnt x (cd_tr c0))).
    by apply (ctrace_prefix_snoc G c0 ev W x lb').
  - (* THE POISONED INVARIANT EXTENDS: for the acting hart by
       [pois_ok_hart_snoc] at the appended label's own obligation, for
       every other hart because its own count has not moved. *)
    intros ev' Hct' y.
    have Hct2 : ctrace_prefix G (cand_snoc c0 (EStep x lb'))
                  (ev_snoc c0 ev (x, gcnt x (cd_tr c0))) W
      := ctrace_prefix_snoc G c0 ev W x lb' Hwf Hct Hcl Hix.
    apply (pois_ok_hart_ev G _ (ev_snoc c0 ev (x, gcnt x (cd_tr c0))) ev' W y
             Hct2 Hct').
    apply pois_ok_hart_snoc; [by apply Hpd|intros _; exact Hstp].
  - exact Hgc2.
  - rewrite cd_log_end_snoc.
    destruct (decide (k = kz)) as [->|Hne].
    + (* THE EXIT WRITE — a store, or (since 4.5b') a FUSED RMW.  The two
         arms differ only in where the written bytes sit in the label, so
         the branch is now stated through [lb_wr]. *)
      have Hw : lb_is_w lb = true by apply Hiff.
      destruct Hsite as (Hl & Hgwix & Hrmw & Hcls & _ & _).
      have HnW : ¬ W (x, gcnt x (cd_tr c0)).
      { rewrite Hgc.
        exact (wsite_cls_notW G W d0 tm Nd n x kz _ Hl Hw Hcls). }
      have Hw' : lb_is_w lb' = true
        by rewrite (lbl_reidx_w_isw lb lb' Hri).
      have Hlbl : gx_lbl G (x, gcnt x (cd_tr c0)) = Some lb'.
      { destruct Hcl as [[_ H]|[[HW _]|(_ & Hpl & _ & _)]];
          [exact H|by destruct (HnW HW)
          |by rewrite (cpois_lbl_notw c0 _ Hpl) in Hw']. }
      destruct (lb_is_w_wr lb' Hw') as (base & vs & Hwr).
      have Hwix : gwix G (x, gcnt x (cd_tr c0)) = S n
        by rewrite (Hix Hw') Hlen.
      have Hmem : (x, gcnt x (cd_tr c0)) ∈ gwrites G.
      { eapply gis_w_gwrites;
          [exact Hwf|by exists lb'|by rewrite /gis_w Hlbl]. }
      have Hat : gwrite_at G (S n) = Some (x, gcnt x (cd_tr c0))
        by rewrite -Hwix; apply gwrite_at_gwix.
      have Hmsg : gmsg G (x, gcnt x (cd_tr c0))
                = Some (WMsg base vs (Some x) (lb_cls lb'))
        by rewrite /gmsg Hlbl Hwr.
      have -> : wlogn n kz (S kz) = S n.
      { rewrite /wlogn (bool_decide_eq_false_2 (S kz ≤ kz)%nat); [done|lia]. }
      have -> : es_msg (EStep x lb') = [WMsg base vs (Some x) (lb_cls lb')]
        by rewrite /es_msg /= Hwr.
      exact (wlog_pfx_snoc G n (cd_log_end c0) _ _ Hpfxn Hat Hmsg).
    + (* A NON-WRITE BLOCK *)
      have Hw : lb_is_w lb = false.
      { destruct (lb_is_w lb) eqn:Hb; [|done].
        exfalso. apply Hne. by apply Hiff. }
      have Hw' : lb_is_w lb' = false by eapply lbl_reidx_w_notw.
      rewrite (es_msg_notw (EStep x lb') Hw') app_nil_r.
      have -> : wlogn n kz (S k) = n.
      { rewrite /wlogn (bool_decide_eq_true_2 (S k ≤ kz)%nat); [done|lia]. }
      exact Hpfxn.
Qed.

(** ** 4.5f The segment, with the CHAINING data exposed

    [wlk_seg_of_cert] at the frozen set, keeping every conclusion
    [WeakRvwmoCert4.seg_step_of_segment] now carries: where the acting
    hart's process ends (the emission's own final state), what its
    release-pending bit becomes, and the frame for every other hart. *)
(** THE PAIR POLICY, AT THE FROZEN SET.  This is what replaces the old
    [cpolp_of_rmwfree] refutation inside [wlk_seg_of_cert2]: an RMW block is
    now SERVED by §4.5b'.  The non-witness premise is free — the site
    classification's witness disjunct names a LOAD. *)
Lemma wcpolp_of_sites (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (tm : nat → list wreg)
    (Nd : nat → CPU → M unit → Prop) (k0 kz : nat) :
  rvwmo_minus_consistent G →
  wubA G W →
  cpolpr x cpu d0 tm (λ k m, Nd k cpu m) (wctx' G W n x kz) (wcls_at G W x)
    (wQ' G W d0 tm Nd n x k0 kz).
Proof.
  intros Hcons Hub k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn'
    ib' Hc Hctx HQ Hrelp Hag Hrds Hnd Hblk.
  have Hrmw : ¬ lb_rmwfree lb
    := cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' Hblk.
  pose proof HQ as (Hk0 & Hkz & Hsite & Hiff).
  pose proof Hsite as (Hl & _ & Hrs & Hcls & _ & _).
  pose proof Hctx as (_ & _ & Hgc & Hpfx).
  have Hcp : cpol_ctx G W x c0 := wctx'_cpol G W n x kz k c0 Hub Hctx.
  have Himg : cd_img c0 = gx_img G.
  { destruct Hcp as (ev & Hgt & _). exact (ctp_img G c0 ev _ Hgt). }
  have Hpfx' : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  have HnW : ¬ W (x, gcnt x (cd_tr c0)).
  { rewrite Hgc. destruct Hcls as [[H _]|[_ [Hw _]]]; [exact H|exfalso].
    destruct Hw as (aq0 & b0 & ts0 & vs0 & Hlw & _).
    rewrite Hlw in Hl. injection Hl as Hl'. rewrite -Hl' in Hrmw.
    exact (Hrmw I). }
  destruct (wcpolp_at G W n x cpu d0 c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m'
              rs1' fn' ib' (tm k) Hcons Himg Hpfx' Hc Hcp HnW
              ltac:(rewrite Hgc; exact (Hrs Hrmw)) Hag Hrds Hblk)
    as (rs2' & Hblk2 & Hok & Hcl & Hag2).
  by exists rs2'.
Qed.

Theorem wlk_seg_of_cert2 (G : gexec) (W : geid → Prop) (n : nat) (x : agent)
    (cpu : CPU) (d0 : dev_state) (tm : nat → list wreg)
    (Nd : nat → CPU → M unit → Prop) (k0 kz : nat) (ws0 : wstate)
    (rowseg : list lbl) (es : list eitem) (pfin : pexv6) (m0 : M unit)
    (rs10 : regstate) (fn0 : ofence) (ib0 : oib32) (St : cyc_state)
    (m20 : M unit) (rs20 : regstate) (fn20 : ofence) (ib20 : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G W →
  wubA G W →
  (∀ k, tm k ⊆ tm (S k)) →
  wnd_ok cpu d0 (wQ' G W d0 tm Nd n x k0 kz) Nd →
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  LDev ∉ es.*1 →
  (∀ i lb, rowseg !! i = Some lb →
     wQ' G W d0 tm Nd n x k0 kz (k0 + i)%nat lb) →
  cst_ok d0 St →
  wctx' G W n x kz k0 (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x
    = Some (PHart cpu m20 rs20 fn20 ib20) →
  Nd k0 cpu m0 →
  csync (tm k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    wctx' G W n x kz (k0 + length rowseg)%nat (cst_c St') ∧
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat ∧
    (∃ (m1 : M unit) (rs11 : regstate) (fn1 : ofence) (ib1 : oib32)
       (m21 : M unit) (rs21 : regstate) (fn21 : ofence) (ib21 : oib32),
       pfin = PHart cpu m1 rs11 fn1 ib1 ∧
       cst_pst St' (cd_end (cst_c St')) !! x
         = Some (PHart cpu m21 rs21 fn21 ib21) ∧
       csync (tm (k0 + length rowseg)%nat) m1 rs11 fn1 ib1
         m21 rs21 fn21 ib21 ∧
       (seg_locked rowseg
          (clockstep (tm k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20) →
          clockstep (tm (k0 + length rowseg)%nat) m1 rs11 fn1 ib1
            m21 rs21 fn21 ib21) ∧
       Nd (k0 + length rowseg)%nat cpu m1) ∧
    w_relp (ms_ws (cand_last_st (cst_c St')) x)
      = w_relp (row_ws_aux k0 ws0 rowseg) ∧
    (∀ y, y ≠ x →
       cst_pst St' (cd_end (cst_c St')) !! y
       = cst_pst St (cd_end (cst_c St)) !! y) ∧
    (∀ y, y ≠ x → w_relp (ms_ws (cand_last_st (cst_c St')) y)
                = w_relp (ms_ws (cand_last_st (cst_c St)) y)).
Proof.
  intros Hcons Hpc Hub Hmono (HNa & HNb & HNbp) Hem Hdev HQ Hok
         Hctx Hp Hnd Hsync Hrelp.
  have Hwf : gwf G by destruct Hcons as (H & _).
  destruct (seg_step_of_segment x cpu d0 tm (wQ' G W d0 tm Nd n x k0 kz)
              (wctx' G W n x kz) (wcls_at G W x) (λ k m, Nd k cpu m)
              Hmono
              (wctx'_pres G W d0 tm Nd n x k0 kz Hwf Hub)
              (λ k lb ws l1 l2 rds wrs m rs fn ib m' rs' fn' ib' HQ0 Hnd0 Hblk,
                 wQ'_exit_ut G W d0 tm Nd n x k0 kz k lb HQ0
                   cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' Hnd0
                   (cblkp_is_w cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs'
                      fn' ib' Hblk)
                   (or_intror Hblk))
              HNa HNb HNbp
              (wpol'_of_sites G W n x cpu d0 tm Nd k0 kz Hcons Hpc Hub
                 Hmono)
              (wcpolp_of_sites G W n x cpu d0 tm Nd k0 kz Hcons Hub)
              k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St m20 rs20 fn20 ib20
              Hem Hdev HQ Hok Hctx Hp Hnd Hsync Hrelp)
    as (St' & tradd & Hstep & Hctx' & Himg & Hpst0 & Hdv0 & Hfin & Hrelpf
        & Hfr & Hfrp).
  exists St', tradd.
  split_and!; [exact Hstep|exact Hctx'|exact Himg|exact Hpst0|exact Hdv0
              |exact Hfin|exact Hrelpf|exact Hfr|exact Hfrp].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.6 THE CHAINED WALK ITSELF

    [wlk_inv'] strengthens [wlk_inv] by the three things §4.5 says a next
    step needs: the frozen set's [ctrace_prefix], every hart's emission
    state (with the walk state's process identified with it), and the ROW
    POSITION BOUNDARY — hart [x]'s replayed count separates its writes the
    log has reached from those it has not.  Everything else the step needs
    is then a fact about [G] alone. *)

Definition wpos_lo (G : gexec) (n : nat) (x : agent) (k : nat) : Prop :=
  ∀ j lb, (j < k)%nat → gx_lbl G (x, j) = Some lb → lb_is_w lb = true →
    (gwix G (x, j) ≤ n)%nat.

Definition wpos_hi (G : gexec) (n : nat) (x : agent) (k : nat) : Prop :=
  ∀ j lb, (k ≤ j)%nat → gx_lbl G (x, j) = Some lb → lb_is_w lb = true →
    (n < gwix G (x, j))%nat.

(** THE INVARIANT CARRIES THE TAINT MAP: each hart's process is identified
    with its emission's off THAT HART's taint at THAT HART's current row
    position — [tm x (gcnt x …)] — not off one global set. *)
Definition wlk_inv' (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (W : geid → Prop) (tm : agent → nat → list wreg)
    (St : cyc_state) (n : nat) : Prop :=
  wlk_inv boot d0 N G St n ∧
  (∃ ev, ctrace_prefix G (cst_c St) ev W) ∧
  wpois_inv G W (cst_c St) ∧
  (∀ x, (x < N)%nat →
     ∃ (p q : pexv6),
       wemit d0 G x (gcnt x (cd_tr (cst_c St))) p ∧
       cst_pst St (cd_end (cst_c St)) !! x = Some q ∧
       pex_dag (tm x (gcnt x (cd_tr (cst_c St)))) p q ∧
       w_relp (ms_ws (cand_last_st (cst_c St)) x)
         = w_relp (row_ws (qrow G x) (gcnt x (cd_tr (cst_c St)))) ∧
       (∀ cpu m rs fn ib, boot x = PHart cpu m rs fn ib →
          ∃ m' rs' fn' ib', p = PHart cpu m' rs' fn' ib') ∧
       (** (N-D) THE NODE IS REACHABLE.  What [wblk_pol_at']'s witness
           datum is discharged against: the emission's own node at this
           row position is [ndreach]-reachable from the hart's booted
           node.  [WeakRvwmoCert3.cert_segment''] hands it back at every
           segment's exit, which is what makes it an INVARIANT. *)
       (∀ cpu m rs fn ib, p = PHart cpu m rs fn ib →
          wnd d0 G boot x (gcnt x (cd_tr (cst_c St))) cpu m)) ∧
  (∀ x, wpos_lo G n x (gcnt x (cd_tr (cst_c St)))) ∧
  (∀ x, wpos_hi G n x (gcnt x (cd_tr (cst_c St)))).

Lemma wlk_inv'_inv boot d0 N G W tm St n :
  wlk_inv' boot d0 N G W tm St n → wlk_inv boot d0 N G St n.
Proof. by intros (H & _). Qed.

(** ONE CHAINED STEP: a certified segment whose OUTPUT STATE carries the
    invariant again.  This is what [wlk_step] could not say — its output
    state was existential and nothing tied it to the next segment. *)
Definition wlk_step' (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (W : geid → Prop) (tm : agent → nat → list wreg)
    (St : cyc_state) (n : nat) : Prop :=
  ∃ (o : segout) (St' : cyc_state),
    seg_step d0 o St St' ∧ wlk_inv' boot d0 N G W tm St' (S n).

Lemma wlk_run' boot d0 N G W tm
    (Hsup : ∀ St n, wlk_inv' boot d0 N G W tm St n →
              (n < length (gwrites G))%nat → wlk_step' boot d0 N G W tm St n)
    (k : nat) :
  ∀ n St, wlk_inv' boot d0 N G W tm St n → (n + k)%nat = length (gwrites G) →
    ∃ l Sf, segs_run d0 l St Sf ∧
            wlk_inv boot d0 N G Sf (length (gwrites G)).
Proof.
  induction k as [|k IH]; intros n St Hinv Hn.
  - exists [], St. split.
    + apply segs_done. by destruct Hinv as ((? & _) & _).
    + replace (length (gwrites G)) with n by lia.
      exact (wlk_inv'_inv boot d0 N G W tm St n Hinv).
  - destruct (Hsup St n Hinv ltac:(lia)) as (o & St' & Hst & Hinv').
    destruct (IH (S n) St' Hinv' ltac:(lia)) as (l & Sf & Hrun & Hfin).
    exists (o :: l), Sf. split; [|exact Hfin]. by eapply segs_more.
Qed.

(** ** 4.6a The START, at the frozen set *)
Theorem wlk_start_inv' boot d0 N G W tm :
  gwf G →
  (∀ x, (x < N)%nat → wemit d0 G x 0%nat (boot x)) →
  wlk_inv' boot d0 N G W tm (wlk_start boot d0 N G) 0%nat.
Proof.
  intros Hwf Hem. split_and!.
  - apply wlk_start_inv.
  - exists (λ _, (0%nat, 0%nat)). apply ctrace_prefix_empty.
  - by intros ev' _ y [|p] s Hs.
  - intros x Hx. exists (boot x), (boot x). split_and!.
    + exact (Hem x Hx).
    + rewrite /wlk_start /= list_lookup_fmap (lookup_seq_lt 0%nat N x Hx) //.
    + apply pex_dag_refl.
    + reflexivity.
    + intros cpu m rs fn ib ->. by eexists _, _, _, _.
    + intros cpu m rs fn ib Hb. by apply (wnd_start d0 G boot x cpu m rs fn ib).
  - intros x j lb Hj Hl Hw. exfalso. move: Hj.
    rewrite /wlk_start /gcnt /=. lia.
  - intros x j lb _ Hl Hw.
    have Hmem : (x, j) ∈ gwrites G
      by (eapply gis_w_gwrites; [exact Hwf|by exists lb|by rewrite /gis_w Hl]).
    destruct (gwix_lookup G (x, j) Hmem) as (i & _ & ->). lia.
Qed.

(** ** 4.6b THE PER-GRAPH DATUM the chained walk consumes

    Every clause is a statement about [G] (and the booted supply) alone:
    there is no walk state in it, no emission, and no identification of a
    process with one — [wlk_inv'] carries all three. *)

(** The site classification, at the position's OWN visit time: [p] is
    replayed by the segment whose exit is [G]'s [(n+1)]-st write exactly
    when that write is [p]'s hart's next one. *)
Definition wsite_supply (boot : agent → pexv6) (d0 : dev_state)
    (G : gexec) (W : geid → Prop) (tm : agent → nat → list wreg) : Prop :=
  ∀ (n : nat) (x : agent) (kz p : nat) (lb : lbl),
    gwrite_at G (S n) = Some (x, kz) →
    (p ≤ kz)%nat →
    (∀ j lbj, (p ≤ j)%nat → (j < kz)%nat → gx_lbl G (x, j) = Some lbj →
       lb_is_w lbj = false) →
    gx_lbl G (x, p) = Some lb →
    (¬ lb_rmwfree lb → wrmw_site G n x p lb) ∧
    wsite_cls G W d0 (tm x) (wnd d0 G boot x) n x p ∧
    (** THE EXIT'S READ-SET FREEDOM and THE POISONED ARM, per position — the
        two clauses that replace the old global [wrds_free]. *)
    wexit_ut d0 (tm x p) (wnd d0 G boot x) p ∧
    wpois_site G W x d0 (tm x p) (tm x (S p)) (wnd d0 G boot x) p.

(** THE ORDER FACT THE WALK NEEDS, AND EXACTLY IT: one hart's writes reach
    the log in PROGRAM ORDER.  [grule14] implies it ([gwrow_gmo_of_rule14]),
    but the walk does NOT need rule 14 — and must not ask for it, since the
    graphs this whole development is about are precisely the ones that
    violate it ([WeakRvwmoCycWit.cyg]'s cycle is built out of rule-14 edges;
    there the fact below holds vacuously, one write per hart). *)
Definition gwrow_gmo (G : gexec) : Prop :=
  ∀ (x : agent) (j k : nat), (j < k)%nat →
    glbl_is G (x, j) lb_is_w → glbl_is G (x, k) lb_is_w →
    (gwix G (x, j) < gwix G (x, k))%nat.

Lemma gwrow_gmo_of_rule14 (G : gexec) :
  gwf G → grule14 G → gwrow_gmo G.
Proof.
  intros Hwf H14 x j k Hjk Hj Hk.
  have Hnd : NoDup (gx_gmo G) by destruct Hwf as (H & _ & _).
  have Hmj : (x, j) ∈ gwrites G.
  { destruct Hj as (l & Hl & Hw).
    eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
  have Hmk : (x, k) ∈ gwrites G.
  { destruct Hk as (l & Hl & Hw).
    eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
  have Hmo : gmo_lt G (x, j) (x, k).
  { apply H14; [|by apply glbl_is_w_gmem|exact Hk].
    destruct Hj as (lj & Hlj & _). destruct Hk as (lk & Hlk & _).
    split_and!; [done|simpl; lia|by exists lj|by exists lk]. }
  destruct Hmo as (_ & _ & Hpos).
  by apply (gwix_gpos_lt G (x, j) (x, k) Hnd Hmj Hmk).
Qed.

Definition wsupply (boot : agent → pexv6) (d0 : dev_state) (G : gexec)
    (W : geid → Prop) (tm : agent → nat → list wreg) (N : nat) : Prop :=
  gwrow_gmo G ∧
  (∀ x k, is_Some (gx_lbl G (x, k)) → (x < N)%nat) ∧
  (∀ x k lb, gx_lbl G (x, k) = Some lb → lb_is_w lb = true →
     ∃ cpu m rs fn ib, boot x = PHart cpu m rs fn ib) ∧
  W_poloc_closed G W ∧
  wubA G W ∧
  (** THE PER-HART TAINT IS ACCUMULATED: it only grows along a hart's row.
      [wrds_free] is GONE — the old global "no emitted block reads a
      tainted carrier" was false at any real execution for a non-empty
      taint (the audit's vacuity), and the two clauses that replace it are
      per-position, inside [wsite_supply]. *)
  (∀ x k, tm x k ⊆ tm x (S k)) ∧
  wsite_supply boot d0 G W tm.

(** ** 4.6c Two frames, and the row split *)

Lemma gcnt_app_ne (tr tradd : list estep) (x y : agent) :
  (∀ s, s ∈ tradd → es_ag s = x) → y ≠ x →
  gcnt y (tr ++ tradd) = gcnt y tr.
Proof.
  intros Hag Hne. rewrite /gcnt list_basics.filter_app length_app.
  have H0 : ∀ l : list estep, (∀ s, s ∈ l → es_ag s = x) →
              filter (λ s, es_ag s = y) l = [].
  { induction l as [|s l IH]; [done|]. intros Hl.
    rewrite filter_cons_False.
    - apply IH. intros s' Hs'. apply Hl. by right.
    - intros Heq. apply Hne. rewrite -Heq. apply Hl. by left. }
  rewrite (H0 tradd Hag) /=. lia.
Qed.

Lemma seg_split_exit (row : list lbl) (k0 kz : nat) (lb : lbl) :
  (k0 ≤ kz)%nat → row !! kz = Some lb →
  take (S kz - k0) (drop k0 row) = take (kz - k0) (drop k0 row) ++ [lb].
Proof.
  intros Hle Hkz.
  have Hs : (S kz - k0)%nat = S (kz - k0)%nat by lia.
  rewrite Hs. apply take_S_r. rewrite lookup_drop.
  by replace (k0 + (kz - k0))%nat with kz by lia.
Qed.

(** A write's index PINS it. *)
Lemma gwix_pin G e n :
  NoDup (gx_gmo G) → e ∈ gwrites G → gwix G e = S n →
  gwrite_at G (S n) = Some e.
Proof. intros Hnd He <-. by apply gwrite_at_gwix. Qed.

(** ** 4.6d THE STEP, DERIVED

    From the invariant, [grule14] and the per-graph datum: which write the
    step is at, where its hart stands, that nothing of that hart's row in
    between is a write, the site data over the stretch, and the emission —
    all of it, with the OUTPUT state carrying the invariant again. *)
Theorem wlk_step'_of_supply (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (W : geid → Prop) (tm : agent → nat → list wreg)
    (St : cyc_state) (n : nat) :
  rvwmo_minus_consistent G →
  wsupply boot d0 G W tm N →
  wlk_inv' boot d0 N G W tm St n →
  (n < length (gwrites G))%nat →
  wlk_step' boot d0 N G W tm St n.
Proof.
  intros Hcons (H14 & HxN & Hbh & Hpc & Hub & Hmono & Hsite) Hinv Hn.
  have Hwf : gwf G by destruct Hcons as (H & _).
  have Hnd : NoDup (gx_gmo G) by destruct Hwf as (H & _ & _).
  pose proof Hinv as (Hbase & (ev0 & Hct0) & Hpi & Hproc & Hlo & Hhi).
  pose proof Hbase as (Hok & Himg & Hpst0 & Hdv0 & Hpfx).
  (* ---- 1. WHICH WRITE, AND WHOSE ---- *)
  destruct (lookup_lt_is_Some_2 (gwrites G) n Hn) as [w Hw].
  have Hat : gwrite_at G (S n) = Some w := Hw.
  destruct w as [x kz].
  destruct (gwrite_at_inv G (S n) (x, kz) Hnd Hat) as (Hmem & Hwix).
  have Hisw : gis_w G (x, kz) = true
    by (apply gwrites_elem_of in Hmem as [_ H]; exact H).
  destruct (gx_lbl G (x, kz)) as [lbz|] eqn:Hlbz;
    [|by rewrite /gis_w Hlbz in Hisw].
  have Hlbzw : lb_is_w lbz = true by rewrite /gis_w Hlbz in Hisw.
  have HxLT : (x < N)%nat by (apply (HxN x kz); by exists lbz).
  pose k0 := gcnt x (cd_tr (cst_c St)).
  (* ---- 2. THE HART STANDS AT OR BEFORE ITS NEXT WRITE ---- *)
  have Hk0 : (k0 ≤ kz)%nat.
  { destruct (decide (k0 ≤ kz)%nat) as [?|Hgt]; [done|exfalso].
    have Hle := Hlo x kz lbz ltac:(lia) Hlbz Hlbzw. lia. }
  (* ---- 3. NOTHING IN BETWEEN IS A WRITE ---- *)
  have Hnwr : ∀ j lbj, (k0 ≤ j)%nat → (j < kz)%nat →
                gx_lbl G (x, j) = Some lbj → lb_is_w lbj = false.
  { intros j lbj Hj1 Hj2 Hlj.
    destruct (lb_is_w lbj) eqn:Hb; [exfalso|done].
    have Hmemj : (x, j) ∈ gwrites G
      by (eapply gis_w_gwrites; [exact Hwf|by exists lbj|by rewrite /gis_w Hlj]).
    have Hgt := Hhi x j lbj Hj1 Hlj Hb.
    have Hlt : (gwix G (x, j) < gwix G (x, kz))%nat
      := H14 x j kz Hj2 (ex_intro _ lbj (conj Hlj Hb))
           (ex_intro _ lbz (conj Hlbz Hlbzw)).
    lia. }
  (* ---- 4. THE ROW STRETCH ---- *)
  have Hkzr : qrow G x !! kz = Some lbz by rewrite -qrow_lbl.
  have Hkzlen : (kz < length (qrow G x))%nat
    by (pose proof (lookup_lt_Some _ _ _ Hkzr); lia).
  have Hrowseg : take (S kz - k0) (drop k0 (qrow G x))
               = take (kz - k0) (drop k0 (qrow G x)) ++ [lbz]
    := seg_split_exit (qrow G x) k0 kz lbz Hk0 Hkzr.
  have Hlenseg : length (take (S kz - k0) (drop k0 (qrow G x)))
               = S (kz - k0)%nat.
  { rewrite length_take length_drop. lia. }
  have Hkzeq : (k0 + length (take (S kz - k0) (drop k0 (qrow G x))))%nat = S kz
    by rewrite Hlenseg; lia.
  (* ---- 5. THE EMISSION AT THE HART'S CURRENT POSITION ---- *)
  destruct (Hproc x HxLT)
    as (p & q & (es & pfin & Hem & Hdevf) & Hq & Hdag & Hrelp & Hph & Hndp).
  destruct (Hbh x kz lbz Hlbz Hlbzw) as (cpu & mb & rsb & fnb & ibb & Hbx).
  destruct (Hph cpu mb rsb fnb ibb Hbx) as (m0 & rs10 & fn0 & ib0 & Hp).
  have Hnd0 : wnd d0 G boot x k0 cpu m0 := Hndp cpu m0 rs10 fn0 ib0 Hp.
  rewrite Hp in Hem. rewrite Hp in Hdag.
  destruct (Hdag cpu m0 rs10 fn0 ib0 eq_refl) as (rs20 & Hq2 & Hag).
  rewrite Hq2 in Hq.
  have Hdd : drop k0 (qrow G x)
           = take (S kz - k0) (drop k0 (qrow G x))
             ++ drop (k0 + length (take (S kz - k0) (drop k0 (qrow G x))))%nat
                  (qrow G x).
  { rewrite -{1}(take_drop (S kz - k0) (drop k0 (qrow G x))) drop_drop Hlenseg.
    replace (k0 + (S kz - k0))%nat with (k0 + S (kz - k0))%nat by lia.
    reflexivity. }
  rewrite Hdd in Hem.
  destruct (hemit_app (λ _, d0) k0 (row_ws (qrow G x) k0)
              (take (S kz - k0) (drop k0 (qrow G x)))
              (drop (k0 + length (take (S kz - k0) (drop k0 (qrow G x))))%nat
                 (qrow G x))
              (PHart cpu m0 rs10 fn0 ib0) es pfin Hem)
    as (pm & es1 & es2 & Hem1 & Hem2 & Hessp).
  have Hdev1 : LDev ∉ es1.*1.
  { intros Hin. apply Hdevf. rewrite Hessp fmap_app.
    apply elem_of_app. by left. }
  have Hdev2 : LDev ∉ es2.*1.
  { intros Hin. apply Hdevf. rewrite Hessp fmap_app.
    apply elem_of_app. by right. }
  have Hws : row_ws_aux k0 (row_ws (qrow G x) k0)
               (take (S kz - k0) (drop k0 (qrow G x)))
           = row_ws (qrow G x)
               (k0 + length (take (S kz - k0) (drop k0 (qrow G x))))%nat.
  { rewrite Hlenseg.
    replace (k0 + S (kz - k0))%nat with (k0 + (S kz - k0))%nat by lia.
    apply row_ws_seg. lia. }
  (* ---- 6. THE SITE DATA ---- *)
  have HQ : ∀ i lb, take (S kz - k0) (drop k0 (qrow G x)) !! i = Some lb →
              wQ' G W d0 (tm x) (wnd d0 G boot x) n x k0 kz
                (k0 + i)%nat lb.
  { intros i lb Hi.
    have Hilt : (i < S (kz - k0))%nat
      by (rewrite -Hlenseg; exact (lookup_lt_Some _ _ _ Hi)).
    have Hik : (k0 + i ≤ kz)%nat by lia.
    have Hl : gx_lbl G (x, (k0 + i)%nat) = Some lb.
    { rewrite qrow_lbl. move: Hi. intros Hi0.
      apply lookup_take_Some in Hi0 as [Hi0 _].
      by rewrite lookup_drop in Hi0. }
    have Hiff : lb_is_w lb = true ↔ (k0 + i)%nat = kz.
    { split.
      - intros Hb. destruct (decide ((k0 + i)%nat = kz)) as [?|Hne]; [done|].
        exfalso. rewrite (Hnwr (k0 + i)%nat lb ltac:(lia) ltac:(lia) Hl) in Hb.
        done.
      - intros Heq. rewrite Heq in Hl. rewrite Hlbz in Hl.
        by injection Hl as <-. }
    destruct (Hsite n x kz (k0 + i)%nat lb Hat Hik
                (λ j lbj Hj1 Hj2 Hlj, Hnwr j lbj ltac:(lia) Hj2 Hlj) Hl)
      as (Hrmw & Hcls & Hut & Hpois).
    split_and!; [lia|lia| |exact Hiff].
    split_and!; [exact Hl| |exact Hrmw|exact Hcls|exact Hut|exact Hpois].
    intros Hb. rewrite (proj1 Hiff Hb). exact Hwix. }
  (* ---- 7. THE SEGMENT ---- *)
  have Hctx : wctx' G W n x kz k0 (cst_c St).
  { split_and!; [by exists ev0|exact Hpi|reflexivity|].
    rewrite /wlogn (bool_decide_eq_true_2 (k0 ≤ kz)%nat Hk0). exact Hpfx. }
  destruct (wlk_seg_of_cert2 G W n x cpu d0 (tm x) (wnd d0 G boot x) k0 kz
              (row_ws (qrow G x) k0)
              (take (S kz - k0) (drop k0 (qrow G x))) es1 pm m0 rs10 fn0 ib0
              St m0 rs20 fn0 ib0 Hcons Hpc Hub (Hmono x)
              (wnd_wnd_ok cpu d0 G boot x
                 (wQ' G W d0 (tm x) (wnd d0 G boot x) n x k0 kz)
                 (λ k lb H,
                    wQ'_lbl G W d0 (tm x) (wnd d0 G boot x) n x k0 kz k lb H))
              Hem1 Hdev1 HQ Hok Hctx Hq Hnd0
              (or_introl (conj eq_refl (conj eq_refl (conj eq_refl Hag))))
              Hrelp)
    as (St' & tradd & Hstep & Hctx' & Himg' & Hpst0' & Hdv0' &
        (m1 & rs11 & fn1 & ib1 & m21 & rs21 & fn21 & ib21 &
         Hpm & Hpx & Hsyncx & Hlockx & Hndx) & Hrelpx & Hfr & Hfrp).
  (* THE SEGMENT'S ROW ENDS IN A WRITE, so its exit is in LOCKSTEP. *)
  destruct (Hlockx ltac:(rewrite Hrowseg; by apply seg_locked_snoc))
    as (Hm21 & Hfn21 & Hib21 & Hagx).
  subst m21 fn21 ib21.
  rewrite Hkzeq in Hagx.
  pose proof Hctx' as ((ev1 & Hct1) & Hpi1 & Hgc1 & Hpfx1).
  rewrite Hkzeq in Hgc1. rewrite Hkzeq in Hpfx1. rewrite Hkzeq in Hndx.
  have HokSt' : cst_ok d0 St' by destruct Hstep as (_ & H & _).
  pose proof Hstep as (_ & _ & _ & Htr & Hagt & _).
  simpl in Htr. simpl in Hagt.
  exists (SegOut x (take (S kz - k0) (drop k0 (qrow G x)))
            (cd_end (cst_c St)) tradd), St'.
  split; [exact Hstep|].
  have HlogS : wlog_pfx G (S n) (cd_log_end (cst_c St')).
  { move: Hpfx1.
    by rewrite /wlogn (bool_decide_eq_false_2 (S kz ≤ kz)%nat ltac:(lia)). }
  (* ---- 8. THE INVARIANT, AGAIN ---- *)
  split_and!.
  - split_and!; [exact HokSt'|by rewrite Himg' Himg|by rewrite Hpst0' Hpst0
                |by rewrite Hdv0' Hdv0|exact HlogS].
  - by exists ev1.
  - exact Hpi1.
  - intros y Hy. destruct (decide (y = x)) as [->|Hne].
    + exists pm, (PHart cpu m1 rs21 fn1 ib1). rewrite Hgc1.
      split_and!.
      * exists es2, pfin. split; [|exact Hdev2].
        rewrite Hws in Hem2. rewrite Hkzeq in Hem2. exact Hem2.
      * exact Hpx.
      * rewrite Hpm. intros cpu' m' rs' fn' ib' [= <- <- <- <- <-].
        exists rs21. split; [reflexivity|exact Hagx].
      * rewrite Hrelpx Hws Hkzeq //.
      * intros cpu' m' rs' fn' ib' Hb. rewrite Hbx in Hb.
        injection Hb as Hc H1 H2 H3 H4. subst cpu'.
        rewrite Hpm. by eexists _, _, _, _.
      * rewrite Hpm. intros cpu' m' rs' fn' ib' [= <- <- <- <- <-]. exact Hndx.
    + have Hgcy : gcnt y (cd_tr (cst_c St')) = gcnt y (cd_tr (cst_c St))
        by rewrite Htr (gcnt_app_ne _ tradd x y Hagt Hne).
      destruct (Hproc y Hy)
        as (py & qy & Hemy & Hqy & Hdagy & Hrelpy & Hphy & Hndy).
      exists py, qy. rewrite Hgcy. split_and!;
        [exact Hemy|by rewrite (Hfr y Hne)|exact Hdagy
        |by rewrite (Hfrp y Hne)|exact Hphy|exact Hndy].
  - (* wpos_lo at [S n] *)
    intros y j lb Hj Hl Hb. destruct (decide (y = x)) as [->|Hne].
    + move: Hj. rewrite Hgc1. intros Hj.
      destruct (decide (j < k0)%nat) as [Hlt|Hge].
      * have Hle := Hlo x j lb Hlt Hl Hb. lia.
      * destruct (decide (j = kz)) as [->|Hne2].
        { rewrite Hlbz in Hl. injection Hl as <-. lia. }
        exfalso. rewrite (Hnwr j lb ltac:(lia) ltac:(lia) Hl) in Hb. done.
    + have Hgcy : gcnt y (cd_tr (cst_c St')) = gcnt y (cd_tr (cst_c St))
        by rewrite Htr (gcnt_app_ne _ tradd x y Hagt Hne).
      move: Hj. rewrite Hgcy. intros Hj.
      have Hle := Hlo y j lb Hj Hl Hb. lia.
  - (* wpos_hi at [S n] *)
    intros y j lb Hj Hl Hb.
    have Hmemj : (y, j) ∈ gwrites G
      by (eapply gis_w_gwrites; [exact Hwf|by exists lb|by rewrite /gis_w Hl]).
    have Hne3 : gwix G (y, j) ≠ S n.
    { intros Heq.
      have Hpin : gwrite_at G (S n) = Some (y, j)
        := gwix_pin G (y, j) n Hnd Hmemj Heq.
      rewrite Hat in Hpin. injection Hpin as Hyx Hj2.
      revert Hj. rewrite -Hyx Hgc1 -Hj2. lia. }
    destruct (decide (y = x)) as [->|Hne].
    + move: Hj. rewrite Hgc1. intros Hj.
      have Hgt := Hhi x j lb ltac:(lia) Hl Hb. lia.
    + have Hgcy : gcnt y (cd_tr (cst_c St')) = gcnt y (cd_tr (cst_c St))
        by rewrite Htr (gcnt_app_ne _ tradd x y Hagt Hne).
      move: Hj. rewrite Hgcy. intros Hj.
      have Hgt := Hhi y j lb Hj Hl Hb. lia.
Qed.


(** ** 4.6e THE EMISSION AT THE START, from the conformance bundle

    The only thing the walk's start asks beyond [wlk_start_inv]: every
    hart's whole-row emission from its boot state, which is
    [WeakRvwmoSupply.gdexec_qconf]'s own [hart_conf] (and, at an index the
    program list does not reach, the empty emission). *)
Lemma wemit_of_qconf (boot : agent → pexv6) (d0 : dev_state) (im : image)
    (nh : nat) (GD : gdexec) (x : agent) :
  gdexec_qconf boot d0 im nh GD → wemit d0 (gd_g GD) x 0%nat (boot x).
Proof.
  intros Hq.
  destruct (gx_prog (gd_g GD) !! x) as [row|] eqn:Hrow.
  - destruct (gdexec_qconf_rows boot d0 im nh GD Hq x row Hrow)
      as (em & Hem & Hdf & _).
    exists (em_items em), (em_fin em). rewrite /qrow Hrow /=.
    split; [exact Hem|exact Hdf].
  - exists [], (boot x). rewrite /qrow Hrow /=.
    split; [apply HEnil|apply not_elem_of_nil].
Qed.

(** ** 4.6f THE WALK, AND ITS THEOREM

    [walk_supply] from the per-graph datum alone: no walk state, no
    emission, no process identification, no alignment — the invariant
    carries all four and [wlk_step'_of_supply] re-establishes them. *)
Definition walk_steps' (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (W : geid → Prop) (tm : agent → nat → list wreg) : Prop :=
  ∀ St n, wlk_inv' boot d0 N G W tm St n → (n < length (gwrites G))%nat →
         wlk_step' boot d0 N G W tm St n.

Theorem walk_supply_of_steps' (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     ∃ (W : geid → Prop) (tm : agent → nat → list wreg),
       walk_steps' boot d0 N (gd_g GD) W tm) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hsup GD cs c0 pst0 z ss Hcons Hq Hcut Hrd0 Hne Hch.
  have Hwf : gwf (gd_g GD) by destruct Hcons as ((H & _ & _) & _ & _).
  destruct (Hsup GD Hcons Hq) as (W & tm & Hsteps).
  destruct (wlk_run' boot d0 N (gd_g GD) W tm Hsteps
              (length (gwrites (gd_g GD))) 0%nat
              (wlk_start boot d0 N (gd_g GD))
              (wlk_start_inv' boot d0 N (gd_g GD) W tm Hwf
                 (λ x _, wemit_of_qconf boot d0 im nh GD x Hq))
              ltac:(lia))
    as (l & Sf & Hrun & Hok & Himg & Hpst & Hdv & Hlog).
  exists l, (wlk_start boot d0 N (gd_g GD)), Sf.
  split_and!; [exact Hrun|exact Himg|exact Hpst|exact Hdv|].
  rewrite -/(cd_end (cst_c Sf)) -/(cd_log_end (cst_c Sf)).
  by apply log_of_of_pfx.
Qed.

(** THE THEOREM.  (R-2), at a residue that is a statement about the GRAPH:
    a frozen witness set, [grule14] (the linearization's own gate —
    [WeakRvwmoTopo] delivers it), and the per-position site data. *)
Theorem walk_supply_of_sites (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     ∃ (W : geid → Prop) (tm : agent → nat → list wreg),
       wsupply boot d0 (gd_g GD) W tm N) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hsup. apply walk_supply_of_steps'. intros GD Hcons Hq.
  destruct (Hsup GD Hcons Hq) as (W & tm & Hsup').
  exists W, tm. intros St n Hinv Hn.
  apply (wlk_step'_of_supply boot d0 N (gd_g GD) W tm St n);
    [by destruct Hcons as (H & _ & _)|exact Hsup'|exact Hinv|exact Hn].
Qed.

(* ====================================================================== *)
(** * 5. THE CAPSTONE SHAPE, RESTATED

    [WeakRvwmoGlue2]'s theorems and [WeakRvwmoCapstone]'s capstone take
    (R-2) as the opaque [walk_supply].  §2–§4 replace it by the per-state
    certification policy, so the same statements hold with (R-2) spelled
    out.  The capstone FILE is not edited: these are corollaries. *)

Theorem cycle_kill_of_l2'''' (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  (* (R-2), spelled out: the certification walk's per-state policy *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf boot d0 (img_z (wgimg σ0)) N GD →
     walk_policy boot d0 N (gd_g GD)) →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  cycle_kill boot d0 (img_z (wgimg σ0)) N.
Proof.
  intros Hfr Hb1 Hb2 Hl2 Hpol Hwp Hwpp.
  eapply (cycle_kill_of_l2'' Σ gen σ0 D Nm P boot d0 N);
    [exact Hfr|exact Hb1|exact Hb2|exact Hl2
    |by apply walk_supply_of_policy|exact Hwp|exact Hwpp].
Qed.

Theorem t2lin_of_l2''' (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf boot d0 (img_z (wgimg σ0)) N GD →
     walk_policy boot d0 N (gd_g GD)) →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 (img_z (wgimg σ0)) N GD →
    ∀ x, ¬ tc (RacyD GD) x x.
Proof.
  intros Hfr Hb1 Hb2 Hl2 Hpol Hwp Hwpp.
  eapply (t2lin_of_l2'' Σ gen σ0 D Nm P boot d0 N);
    [exact Hfr|exact Hb1|exact Hb2|exact Hl2
    |by apply walk_supply_of_policy|exact Hwp|exact Hwpp].
Qed.

(** THE CAPSTONE, with (R-2) replaced by the walk's policy — the shape the
    milestone now has: for every consistent, conformant graph of the booted
    xv6 image, [xv6_srvwmo_safe]'s conclusion verbatim, under (R-1)
    [l2_claim] and the per-state certification policy. *)
Theorem xv6_rvwmo_safe_modulo_walk (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) *)
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (* (R-2), as the walk's per-state policy *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     walk_policy (xboot σ0) (wgdev σ0) (xN σ0) (gd_g GD)) →
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
  intros Hfr Hwp Hwpp Hl2 Hpol.
  apply (xv6_rvwmo_safe_modulo Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  by apply walk_supply_of_policy.
Qed.

(* ====================================================================== *)
(** * 6. AUDIT *)

Print Assumptions wlog_pfx_snoc.
Print Assumptions log_of_of_pfx.
Print Assumptions wlk_inv_step.
Print Assumptions wlk_run.
Print Assumptions wlk_start_inv.
Print Assumptions walk_supply_of_steps.
Print Assumptions hemit_app.
Print Assumptions seg_step_msgs.
Print Assumptions wlk_step_of_seg.
Print Assumptions wnw_of_pfx.
Print Assumptions wsrc_or_wwit.
Print Assumptions wcls_of_pfx.
Print Assumptions wcls_of_wit.
Print Assumptions wblk_pol_at.
Print Assumptions src_in_log_of_pfx.
Print Assumptions wpol_of_sites.
Print Assumptions wctx_pres.
Print Assumptions wlk_seg_of_cert.
Print Assumptions walk_policy_steps.
Print Assumptions walk_supply_of_policy.
Print Assumptions row_ws_seg.
Print Assumptions wubA_wub.
Print Assumptions wblk_pol_at'.
Print Assumptions wpol'_of_sites.
Print Assumptions wctx'_pres.
Print Assumptions wlk_seg_of_cert2.
Print Assumptions wlk_run'.
Print Assumptions wlk_start_inv'.
Print Assumptions gwrow_gmo_of_rule14.
Print Assumptions gcnt_app_ne.
Print Assumptions wlk_step'_of_supply.
Print Assumptions wemit_of_qconf.
Print Assumptions walk_supply_of_steps'.
Print Assumptions pois_ok_mstep.
Print Assumptions wcls_of_pois.
Print Assumptions wpois_no_fault.
Print Assumptions rds_ok_dec.
Print Assumptions walk_supply_of_sites.
Print Assumptions cycle_kill_of_l2''''.
Print Assumptions t2lin_of_l2'''.
Print Assumptions xv6_rvwmo_safe_modulo_walk.

(* ====================================================================== *)
(** * 7. WHAT REMAINS, EXACTLY — THE LEDGER, CLOSED TO TWO ITEMS

    (R-2) is no longer opaque: [walk_supply] IS [walk_policy], the
    per-state certification supply, and the reduction is proved
    ([walk_supply_of_policy]).  What [wlk_seg_of_cert] — the route that
    BUILDS one such step out of [WeakRvwmoCert3.cert_segment'] — still asks
    is exactly two obligations plus one graph-side datum:

    (W-1) THE READ/REGISTER POLICY [wpol] — DISCHARGED (§4.0c,
          [wpol_of_sites]).  The alignment makes it derivable, and since
          the tenth pass's split of [WeakRvwmoCert3.cpol_ctx] it covers
          BOTH read routes: [cpol_read] at a non-witness position (its
          [¬ W] premise is what the split moved out of the context), and
          [WeakRvwmoCert2.cert_read_witness] at a witness one, with the
          block re-timestamped by [WeakRvwmoCert2.cblk_load_retime].  The
          substituted route does NOT diverge the runs — the values are the
          site datum's ([wwit_site]) and only the TIMESTAMPS move — so
          [WeakRvwmoCert3.boundary_reconverge_run] is not among the walk's
          obligations.  What the route costs instead is [wwit_site]: a
          witness's graph label must be plain, its footprint must exist at
          the candidate's latest source, and its VALUES must be the
          candidate's latest bytes.

    (W-2) [wub] — (P-3) [wit_fence_ub], per witness.  Guarded and vacuous
          at a witness with no publishing fence between it and the read
          whose floor it would raise ([WeakRvwmoCert3] §2.1).

    (W-5) THE PER-HART TAINT'S THREE SITE OBLIGATIONS (this session; §4.5c'
          and [wsite_supply]).  [wsupply]'s old [wrds_free d0 T] — "NO
          emitted block, of any hart, at any node, reads a carrier in [T]"
          — is GONE: it is false at any real execution for [T ≠ []], so the
          capstone's [∃ W T] was satisfiable only at [T = []] (the audit's
          vacuity).  What replaces it is a per-hart, ACCUMULATED taint
          [tm x : nat → list wreg], monotone along the row, and three
          obligations that are all per-POSITION:

          - [wexit_ut] — "the block of a WRITE position reads no carrier
            the hart's taint holds".  This is [exit_untainted]: a store or
            RMW whose address or data depended on the witness would have a
            [gd_deps] edge FROM the witness, hence the witness would be
            gmo-BELOW it and so not above the segment's exit.  That
            argument is DEC-7 dynamic provenance ([WeakRvwmoConf.dstep]
            over the emission's items — the induction
            [WeakRvwmoPinBridge2] runs for the checker) and it is NOT
            discharged here; it is stated at the site.  It is the reason
            [lbl_reidx_w_store] is still true, hence the exit message and
            the whole log arithmetic.

          - [wpois_site] — the POISONED arm.  When a NON-write block does
            read a tainted carrier, no mirror exists (the address is the
            certified run's own), and the site must hand back the
            certified block, its [lbl_poisoned] relation to [G]'s label,
            its servability by the candidate ([pois_ok]), its
            classification ([wcls_at], which carries
            [WeakRvwmoGlue2.cstep_pois_ok] — the floor obligation a later
            TRUE read of the same hart owes it) and the re-convergence
            [csync] at the GROWN taint.

          - [poisoned_no_fault] — THE FAULT BOUNDARY, named and contained
            in [wpois_site] ([wpois_no_fault] extracts it).  A poisoned
            load's address comes from a register the certified run does not
            agree with the emission on, so nothing in the model says it
            translates without an exception; if it faults, the Sail step
            takes the trap path and the certified run is executing the
            handler, which the row correspondence cannot describe.  IT IS A
            KERNEL CLAIM OF [l2_claim]'s KIND — xv6's kernel pointers are
            kernel-range and the kernel's direct map is identity, which
            makes it plausible, but it is not a graph fact and it is not
            proved.  It is recorded HERE, in this ledger, beside (R-1).

    THE OLD (W-4) IS GONE.  [wnw_seg] was needed only because the carried
    context asserted that the next position is not a witness; the split
    deleted that clause, so [wctx_pres] no longer asks for it, and a hart
    with witnesses in its row is now a first-class case rather than an
    excluded one ([WeakRvwmoWalk2] §6.2 runs it at the tree's LB graph).
    [wrow_in_log] survives as the datum of the SUBSTITUTION-FREE
    specialisation ([WeakRvwmoProgress.wlk_seg_of_cert']).

    ------------------------------------------------------------------------
    WHAT MOVED, AND WHY (this session):

    (O-E) CLOSED.  [WeakRvwmoCert3.cert_segment'] now STATES the three
          bookkeeping equations ([cd_img c' = cd_img c], [pst' 0 = pst 0],
          [dv' 0 = dv 0]); [WeakRvwmoCert4.seg_step_of_segment] and §4.1
          carry them through, so [walk_policy]'s three clauses are free at
          the route that builds it.

    (W-3) ABSORBED INTO (W-1).  The classification is not derivable from
          [lbl_reidx] — that relation is exactly what LETS the appended
          label's read indices differ — so no graph-side lemma can pin it;
          it is the READ POLICY's output.  [cert_segment'] therefore gained
          a [Cls] parameter which the policy DELIVERS and [Hpres]
          CONSUMES, and [WeakRvwmoGlue2.cpol_Hpres]'s separate [Hcls]
          premise is gone.  Its two log-side halves are proved here:
          [wcls_of_pfx] (the arithmetic: an appended write lands at
          [S (length log)], [wlog_pfx] read forward) and
          [src_in_log_of_pfx] (the read: [src_in_log] from [wlog_pfx] +
          [gload_value] + "every source index is at most the write count").

    (W-4) CLOSED.  The walk's witness set is LOG-DECIDED ([wwit]: a load
          with a graph source above the current write count).  A write
          position is never a witness ([wwit_not_w]), and [wnw_of_pfx]
          discharges [wnw] from [wrow_in_log].

    (O-F) CLOSED.  [cert_segment']'s [HEpair] case is no longer refuted:
          the fused exclusive pair is certified in place, by the pair
          policy [WeakRvwmoCert3.cpolp] together with §3.3a/§3.3b's
          [cblkp_intro] / [cert_block_snoc_pair].  The appended label is
          [G]'s OWN ([lbl_reidx_refl]) because an RMW is never a witness
          ([WeakRvwmoCert3.witness_not_aq]).  The old [HQrmw] refutation
          survives as one instance of the policy
          ([WeakRvwmoCert3.cpolp_of_rmwfree]), so every earlier caller is
          unchanged up to that adapter, and §4.5's
          [WeakRvwmoCert3.cert_block_pair] is what discharges the policy at
          a real site (its [cert_rmw_latest] — the RMW's G-source IS the
          log's latest — is the one semantic point).

    NON-VACUITY is [WeakRvwmoCycWit.v]: a two-hart LB graph with a real
    [RacyD] cycle, [rvwmo_minus_deps_consistent] and [gdexec_qconf], on
    which both [wlk_step]s and the walk's whole conclusion — a [segs_run]
    whose final log IS [log_of] of the graph — are built. *)
