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
          position and (P-4) progress, the latter inside the read policy
          [Hpol'] (that is where [WeakRvwmoCert3.boundary_reconverge_run]
          is applied — after a substituted read the two runs are at
          different nodes and only the EWPs say either reaches a boundary).
          [walk_policy] bundles the per-state supply; [walk_supply_of_policy]
          is the theorem.

      §5  THE CAPSTONE SHAPE, restated: [cycle_kill_of_l2''''],
          [t2lin_of_l2'''] and [xv6_rvwmo_safe_modulo_walk] — the capstone
          with (R-2) replaced by the policy.  The capstone file is NOT
          edited.

      §6  the audit, §7 the ledger.

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
    index 0 — but that theorem does not STATE them and this file may not
    edit it.  They are therefore part of the supply, and recorded as (O-E)
    in §7: a three-line strengthening of [cert_segment']'s conclusion. *)
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

Lemma lbl_reidx_notw lb lb' :
  lbl_reidx lb lb' → lb_is_w lb = false → lb_is_w lb' = false.
Proof.
  destruct lb; destruct lb'; simpl; try done; by intros ->.
Qed.

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
  apply lbl_reidx_store in Hlst. subst lst.
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
    eapply lbl_reidx_notw; [exact Hri|].
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
    [Ctx := cpol_ctx G W x] — and names, at the position each is honestly
    stated, the pieces the certification still owes.

    THE FOUR NAMED OBLIGATIONS, in [cert_segment']'s own vocabulary:

      [wcls]  the STEP CLASSIFICATION.  The read policy's own output: the
              appended label is [G]'s own at a non-witness position, or the
              candidate's latest-source read at a witness one, and an
              appended WRITE lands at its [gwix].  This is what
              [WeakRvwmoGlue2.cpol_Hpres] cannot supply and says so:
              [lbl_reidx] is exactly the relation that lets the read
              indices differ.  It is DATA, decidable from the log — a
              read's source at index [t] is in the log iff [t] is at most
              the current write count, and the walk appends writes in gmo
              order, so the position decides it.

      [wub]   (P-3) [wit_fence_ub] at the next position — a HYPOTHESIS by
              design ([WeakRvwmoCert3] §2.1): a witness raises [w_vrOld]
              byte-agnostically and that reaches a later read's floor only
              through a publishing fence, so the obligation is guarded and
              vacuous at a witness with no such fence.

      [wnw]   the witness set does not name the hart's NEXT position —
              a property of [W], checkable where the cycle fixes it.

      [wpol]  the READ/REGISTER POLICY, carrying (P-4) PROGRESS.  This is
              where [WeakRvwmoCert3.boundary_reconverge_run] is applied:
              at a SUBSTITUTED read the certified run and the emission sit
              at different monad nodes ([WeakEvProv.taint_closure_load]),
              and that either REACHES its instruction boundary is the EWPs'
              content, not a graph-side lemma.  At an unsubstituted read
              the two runs are in lockstep and the clause is
              [WeakEvProv.instr_dagree_ev] plus
              [WeakRvwmoCert3.cpol_read]. *)

Definition wcls (G : gexec) (W : geid → Prop) (x : agent) (Q : lbl → Prop)
    : Prop :=
  ∀ (c0 : cand) (lb lb' : lbl),
    cpol_ctx G W x c0 → srvwmo_consistent c0 → Q lb → lbl_reidx lb lb' →
    mstep_ok (cand_last_st c0) x lb' →
    cstep_cls G W x c0 lb' ∧
    (lb_is_w lb' = true →
       gwix G (x, gcnt x (cd_tr c0)) = S (length (cd_log_end c0))).

Definition wub (G : gexec) (W : geid → Prop) (x : agent) : Prop :=
  ∀ (c0 : cand) (lb' : lbl) (ev' : nat → geid),
    ctrace_prefix G (cand_snoc c0 (EStep x lb')) ev' W →
    wit_fence_ub G (cand_snoc c0 (EStep x lb')) ev' W
      (x, S (gcnt x (cd_tr c0))).

Definition wnw (W : geid → Prop) (x : agent) : Prop :=
  ∀ (c0 : cand), ¬ W (x, S (gcnt x (cd_tr c0))).

Definition wpol (G : gexec) (W : geid → Prop) (x : agent) (cpu : CPU)
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
      lbl_reidx lb lb' ∧
      dreg_agree (λ nn, nn ∉ T) rs1' rs2'.

(** ** 4.1 THE SEGMENT, from the emission and the four obligations

    (P-1) is DISCHARGED here — [WeakRvwmoGlue2.cpol_Hpres] is exactly the
    [Hpres] [cert_segment'] asks for at [Ctx := cpol_ctx G W x] — so the
    only inputs left are the emission block, the invariant at the current
    state, and the four named obligations above. *)
Theorem wlk_seg_of_cert (G : gexec) (W : geid → Prop) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Q : lbl → Prop)
    (HQrmw : ∀ lb, Q lb → lb_rmwfree lb)
    (k0 : nat) (ws0 : wstate) (rowseg : list lbl) (es : list eitem)
    (pfin : pexv6) (m0 : M unit) (rs10 : regstate) (fn0 : ofence)
    (ib0 : oib32) (St : cyc_state) (rs20 : regstate) :
  gwf G →
  wcls G W x Q → wub G W x → wnw W x → wpol G W x cpu d0 T Q →
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  Forall Q rowseg →
  cst_ok d0 St →
  cpol_ctx G W x (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) →
  dreg_agree (λ nn, nn ∉ T) rs10 rs20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    cpol_ctx G W x (cst_c St') ∧
    cd_img (cst_c St') = cd_img (cst_c St).
Proof.
  intros Hwf Hcls Hub Hnw Hpol Hem HQ Hok Hctx Hp Hag Hrelp.
  destruct (seg_step_of_segment x cpu d0 T Q HQrmw (cpol_ctx G W x)
              (cpol_Hpres G W x Q Hwf Hcls Hub Hnw) Hpol
              k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St rs20
              Hem HQ Hok Hctx Hp Hag Hrelp)
    as (St' & tradd & Hstep & Hctx').
  exists St', tradd. split_and!; [exact Hstep|exact Hctx'|].
  destruct Hctx as (ev & Hgt & _ & _). destruct Hctx' as (ev' & Hgt' & _ & _).
  by rewrite (ctp_img _ _ _ _ Hgt') (ctp_img _ _ _ _ Hgt).
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
Print Assumptions wlk_seg_of_cert.
Print Assumptions walk_policy_steps.
Print Assumptions walk_supply_of_policy.
Print Assumptions cycle_kill_of_l2''''.
Print Assumptions t2lin_of_l2'''.
Print Assumptions xv6_rvwmo_safe_modulo_walk.

(* ====================================================================== *)
(** * 7. WHAT REMAINS, EXACTLY

    (R-2) is no longer opaque: [walk_supply] IS [walk_policy], the
    per-state certification supply, and the reduction is proved
    ([walk_supply_of_policy]).  What the policy still owes, at the position
    each obligation is honestly stated:

    (W-1) THE READ/REGISTER POLICY [wpol] — the certification's real
          content, and where (P-4) PROGRESS lives.  At an UNSUBSTITUTED
          read the two runs are in lockstep and the clause is
          [WeakEvProv.instr_dagree_ev] (equal labels, register files still
          agreeing off the taint set) plus [WeakRvwmoCert3.cpol_read] (the
          admissibility, with [floor_ok] discharged).  At a SUBSTITUTED one
          the runs diverge at the read's continuation
          ([WeakEvProv.taint_closure_load]) and re-converge only at the
          next instruction boundary
          ([WeakRvwmoCert3.boundary_reconverge_run]) — and that either run
          REACHES a boundary is the EWPs' content, not a graph-side lemma.
          [WeakEvProv]'s (P-a)–(P-c) are discharged; (P-d), the iteration
          to the boundary, is exactly this.

    (W-2) [wub] — (P-3) [wit_fence_ub], per witness.  Guarded and vacuous
          at a witness with no publishing fence between it and the read
          whose floor it would raise ([WeakRvwmoCert3] §2.1).

    (W-3) [wcls] — the step classification, which is DATA: the walk appends
          writes in gmo order, so at log length [n] a read's graph source
          at index [t] is in the log iff [t ≤ n], and the position decides
          whether the step is [G]'s own label or the candidate's
          latest-source read.  Its second half — an appended WRITE lands at
          its [gwix] — is the same arithmetic read forward.

    (W-4) [wnw] — "[W] does not name the hart's next position", a property
          of the witness SET, checkable where the cycle fixes it
          (§4e: [W] is segment 1's entry plus its poloc-later reads,
          [WeakRvwmoCert3.W_poloc_closed]).

    (O-E) THE THREE BOOKKEEPING EQUATIONS of [wlk_step] (image, [pst 0],
          [dv 0]).  [WeakRvwmoCert3.cert_segment'] establishes all three BY
          CONSTRUCTION — it extends by [cand_snoc]/[pst_snoc]/[dv_snoc],
          none of which touches the image or index 0 — but its conclusion
          does not STATE them, and this file may not edit it (new leaves
          only).  The image half is already free here
          ([wlk_seg_of_cert] reads it off [cpol_ctx]'s [ctp_img]); the two
          supply halves are a two-line addition to [cert_segment']'s
          conclusion.

    (O-F) THE RMW SEGMENT.  [cert_segment'] refutes the [HEpair] block
          through [HQrmw], so a segment whose row contains a fused [LRmw]
          is out of scope; [WeakRvwmoCert3] §4 ([cert_block_pair],
          [cert_rmw_ok]) supplies the missing block and the walk's [Q] can
          be widened once that is threaded through the iteration.

    NON-VACUITY is [WeakRvwmoCycWit.v]: a two-hart LB graph with a real
    [RacyD] cycle, [rvwmo_minus_deps_consistent] and [gdexec_qconf], on
    which both [wlk_step]s and the walk's whole conclusion — a [segs_run]
    whose final log IS [log_of] of the graph — are built. *)
