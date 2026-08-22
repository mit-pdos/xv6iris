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
     gwix G (x, gcnt x (cd_tr c0)) = S (length (cd_log_end c0))).

(** At a NON-witness position the classification IS [G]'s own label, and
    the write clause is [wlog_pfx] read forward: the log has length [n], so
    "the appended write is [G]'s [(n+1)]-st" says exactly [gwix = S n]. *)
Theorem wcls_of_pfx (G : gexec) (n : nat) (x : agent) (c0 : cand) (lb' : lbl) :
  wlog_pfx G n (cd_log_end c0) →
  gx_lbl G (x, gcnt x (cd_tr c0)) = Some lb' →
  ¬ wwit G n (x, gcnt x (cd_tr c0)) →
  (lb_is_w lb' = true → gwix G (x, gcnt x (cd_tr c0)) = S n) →
  wcls_at G (wwit G n) x c0 lb'.
Proof.
  intros [Hlen _] Hl HnW Hix. split.
  - left. by split.
  - intros Hw. by rewrite (Hix Hw) Hlen.
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
      lbl_reidx lb lb' ∧
      wcls_at G W x c0 lb' ∧
      dreg_agree (λ nn, nn ∉ T) rs1' rs2'.

(** THE SITE DATUM: [G]'s label at row position [p], the log-decided
    classification at it, and RMW-freedom. *)
Definition wsite_ok (G : gexec) (n : nat) (x : agent) (p : nat) (lb : lbl)
    : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  wsrc_le G n (x, p) ∧
  (lb_is_w lb = true → gwix G (x, p) = S n) ∧
  lb_rmwfree lb.

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
Definition wQ (G : gexec) (n : nat) (x : agent) (k0 kz : nat)
    (k : nat) (lb : lbl) : Prop :=
  (k0 ≤ k)%nat ∧ (k ≤ kz)%nat ∧
  wsite_ok G n x k lb ∧
  (lb_is_w lb = true ↔ k = kz).

Lemma wQ_rmwfree G n x k0 kz k lb : wQ G n x k0 kz k lb → lb_rmwfree lb.
Proof. by intros (_ & _ & (_ & _ & _ & H) & _). Qed.

(** ** 4.0c THE POLICY AT AN ALIGNED CANDIDATE, AND ITS DISCHARGE *)

Definition wpol (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (k0 kz : nat) : Prop :=
  ∀ (k : nat) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    wctx G n x kz k c0 →
    wQ G n x k0 kz k lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2',
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx lb lb' ∧
      wcls_at G (wwit G n) x c0 lb' ∧
      dreg_agree (λ nn, nn ∉ T) rs1' rs2'.

(** THE THREE [mstep_ok] ROUTES, at an aligned candidate. *)
Theorem wsite_mstep_ok (G : gexec) (n : nat) (x : agent) (c0 : cand)
    (lb : lbl) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G (wwit G n) x c0 →
  wsite_ok G n x (gcnt x (cd_tr c0)) lb →
  mstep_ok (cand_last_st c0) x lb.
Proof.
  intros Hcons Hpc Himg Hpfx Hctx (Hl & Hle & _ & Hrmw).
  pose proof Hcons as (Hwf & _ & Hlv & _).
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc].
  - apply (cpol_read G (wwit G n) x c0 aq base ts vs Hcons Hpc Hctx Hl).
    apply (src_in_log_of_pfx G n c0 (x, gcnt x (cd_tr c0)) aq base ts vs
             Hlv Himg Hpfx Hl (gshape G Hwf _ _ Hl) Hle).
  - apply cert_write_ok. exact (gshape G Hwf _ _ Hl).
  - apply cert_fence_ok.
  - by destruct Hrmw.
Qed.

(** THE POLICY'S BLOCK, at an aligned candidate: the untainted mirror
    ([cert_block_mirror] at the EMPTY taint set) plus the admissibility and
    the classification, with [G]'s own label handed back
    ([lbl_reidx_refl]). *)
Theorem wblk_pol_at (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs1 rs2 : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs1' : regstate)
    (fn' : ofence) (ib' : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G (wwit G n) x c0 →
  wsite_ok G n x (gcnt x (cd_tr c0)) lb →
  dreg_agree (λ nn, nn ∉ []) rs1 rs2 →
  cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
  ∃ (lb' : lbl) (l' : wlabel) (rds' : list wreg) (wrs' : list register)
    (rs2' : regstate),
    cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
    mstep_ok (cand_last_st c0) x lb' ∧
    lbl_reidx lb lb' ∧
    wcls_at G (wwit G n) x c0 lb' ∧
    dreg_agree (λ nn, nn ∉ []) rs1' rs2'.
Proof.
  intros Hcons Hpc Himg Hpfx Hctx Hsite Hag Hblk.
  destruct (cert_block_mirror (λ nn, nn ∉ []) cpu d0 ws lb l rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk
              (λ nn _, not_elem_of_nil nn) Hag) as (rs2' & Hblk2 & Hag2).
  exists lb, l, rds, wrs, rs2'.
  destruct Hctx as (ev & Hgt & Hub & HnW).
  destruct Hsite as (Hl & Hle & Hix & Hrmw).
  split_and!.
  - exact Hblk2.
  - apply (wsite_mstep_ok G n x c0 lb Hcons Hpc Himg Hpfx);
      [by exists ev|by split_and!].
  - apply lbl_reidx_refl.
  - by apply (wcls_of_pfx G n x c0 lb).
  - exact Hag2.
Qed.

(** (W-1), DISCHARGED.  The alignment is what makes it derivable: the site
    data are read off [G] at the position the block sits at, and the
    candidate's own position IS that position. *)
Theorem wpol_of_sites (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (k0 kz : nat) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  wpol G n x cpu d0 [] k0 kz.
Proof.
  intros Hcons Hpc k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hc (Hctx & Hgc & Hpfx) (Hk0 & Hkz & Hsite & _) Hrelp Hag Hblk.
  have Himg : cd_img c0 = gx_img G.
  { destruct Hctx as (ev & Hgt & _ & _). exact (ctp_img G c0 ev _ Hgt). }
  have Hpfx' : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  apply (wblk_pol_at G n x cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Hpc Himg Hpfx' Hctx);
    [by rewrite Hgc|exact Hag|exact Hblk].
Qed.

(** ** 4.0d THE CONTEXT IS PRESERVED — (P-1) at the indexed instance *)
Theorem wctx_pres (G : gexec) (n : nat) (x : agent) (k0 kz : nat) :
  gwf G →
  wub G (wwit G n) x →
  wnw_seg G n x k0 kz →
  ∀ (k : nat) (c0 : cand) (lb lb' : lbl),
    wctx G n x kz k c0 → srvwmo_consistent c0 → wQ G n x k0 kz k lb →
    lbl_reidx lb lb' → mstep_ok (cand_last_st c0) x lb' →
    wcls_at G (wwit G n) x c0 lb' →
    wctx G n x kz (S k) (cand_snoc c0 (EStep x lb')).
Proof.
  intros Hwf Hub Hnw k c0 lb lb' (Hctx & Hgc & Hpfx) Hc
         (Hk0 & Hkz & Hsite & Hiff) Hri Hok (Hcl & Hix).
  have Hpfxn : wlog_pfx G n (cd_log_end c0).
  { move: Hpfx. by rewrite /wlogn (bool_decide_eq_true_2 (k ≤ kz)%nat Hkz). }
  have Hlen : length (cd_log_end c0) = n by destruct Hpfxn as [H _].
  have Hgc2 : gcnt x (cd_tr (cand_snoc c0 (EStep x lb'))) = S k
    by rewrite gcnt_cand_snoc_self Hgc.
  split_and!.
  - eapply cpol_ctx_snoc;
      [exact Hwf|exact Hctx|exact Hcl|exact Hix
      |intros ev' Hev'; exact (Hub c0 lb' ev' Hev')
      |rewrite Hgc; by apply Hnw].
  - exact Hgc2.
  - rewrite cd_log_end_snoc.
    destruct (decide (k = kz)) as [->|Hne].
    + (* THE EXIT STORE: the log grows by G's (n+1)-st write's message *)
      have Hw : lb_is_w lb = true by apply Hiff.
      destruct Hsite as (Hl & Hle & Hgwix & Hrmw).
      destruct lb as [aq0 b0 ts0 vs0|rl base vs kc|pr pw sr sw
                     |aq0 rl0 b0 ts0 rv0 wv0 kc0]; try by simpl in Hw.
      have Hlb' : lb' = WeakAxiomatic.LStore rl base vs kc
        := lbl_reidx_store rl base vs kc lb' Hri.
      subst lb'.
      have HnW : ¬ wwit G n (x, gcnt x (cd_tr c0))
        by rewrite Hgc; apply wsrc_le_not_wwit.
      have Hlbl : gx_lbl G (x, gcnt x (cd_tr c0))
                = Some (WeakAxiomatic.LStore rl base vs kc).
      { destruct Hcl as [[_ H]|[HW _]]; [exact H|by destruct (HnW HW)]. }
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
      have Hw' : lb_is_w lb' = false by eapply lbl_reidx_notw.
      rewrite (es_msg_notw (EStep x lb') Hw') app_nil_r.
      have -> : wlogn n kz (S k) = n.
      { rewrite /wlogn (bool_decide_eq_true_2 (S k ≤ kz)%nat); [done|lia]. }
      exact Hpfxn.
Qed.

(** ** 4.1 THE SEGMENT, from the emission and the REDUCED ledger

    (P-1) is [wctx_pres]; (W-1) is [wpol_of_sites]; (O-F) is
    [WeakRvwmoCert3.cpolp_of_rmwfree] (the site datum is RMW-free).  What is
    left at this interface is (W-2) [wub] and the restricted (W-4)
    [wnw_seg]. *)
Theorem wlk_seg_of_cert (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (k0 kz : nat) (ws0 : wstate) (rowseg : list lbl)
    (es : list eitem) (pfin : pexv6) (m0 : M unit) (rs10 : regstate)
    (fn0 : ofence) (ib0 : oib32) (St : cyc_state) (rs20 : regstate) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  (* (W-2) *)
  wub G (wwit G n) x →
  (* (W-4), restricted to the segment *)
  wnw_seg G n x k0 kz →
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  (∀ i lb, rowseg !! i = Some lb → wQ G n x k0 kz (k0 + i)%nat lb) →
  cst_ok d0 St →
  wctx G n x kz k0 (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) →
  dreg_agree (λ nn, nn ∉ []) rs10 rs20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    wctx G n x kz (k0 + length rowseg)%nat (cst_c St') ∧
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat.
Proof.
  intros Hcons Hpc Hub Hnw Hem HQ Hok Hctx Hp Hag Hrelp.
  have Hwf : gwf G by destruct Hcons as (H & _).
  destruct (seg_step_of_segment x cpu d0 [] (wQ G n x k0 kz)
              (wctx G n x kz) (wcls_at G (wwit G n) x)
              (wctx_pres G n x k0 kz Hwf Hub Hnw)
              (wpol_of_sites G n x cpu d0 k0 kz Hcons Hpc)
              (cpolp_of_rmwfree x cpu d0 [] (wctx G n x kz)
                 (wcls_at G (wwit G n) x) (wQ G n x k0 kz)
                 (λ k lb H, wQ_rmwfree G n x k0 kz k lb H))
              k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St rs20
              Hem HQ Hok Hctx Hp Hag Hrelp)
    as (St' & tradd & Hstep & Hctx' & Himg & Hpst0 & Hdv0).
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
Print Assumptions wcls_of_pfx.
Print Assumptions src_in_log_of_pfx.
Print Assumptions wpol_of_sites.
Print Assumptions wctx_pres.
Print Assumptions wlk_seg_of_cert.
Print Assumptions walk_policy_steps.
Print Assumptions walk_supply_of_policy.
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

    (W-1) THE READ/REGISTER POLICY [wpol] — the certification's real
          content, where (P-4) PROGRESS lives and where (W-3)'s
          CLASSIFICATION now lives too.  At an UNSUBSTITUTED read the two
          runs are in lockstep and the clause is
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

    THE DATUM: [wrow_in_log G x n] — "hart [x]'s reads all draw on writes
    the log has reached".  Decidable from [G] and the write count, with no
    semantic content; it is what makes the segment substitution-free, and
    it discharges the old (W-4).

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
