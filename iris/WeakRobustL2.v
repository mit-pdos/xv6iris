(** * WeakRobustL2.v — L2-M1: THE MACHINE FACTS OF THE LAYER-2 CASE TREE

    [claude-notes/design/weak-memory-layer2.md] designs Layer 2 as a
    DIRECT acyclicity theorem: at a minimal [gdep2] cycle every agent is
    visited in ONE program-order segment [h_j .. f_j], and the measure
    walk closes as soon as each segment satisfies S1 ("the entry
    timestamp is below the exit fulfil's").  §3 splits the segments into
    six cases; this file discharges the ones that are TRACE FACTS — true
    of every well-formed bundle, with no site knowledge, no pf-realness
    and no ownership discipline:

    - **C3, the DEPENDENT EXIT** ([fcov_of_dep_chain] and its two
      shapes).  The D2/D3 machine tracks RVWMO's syntactic dependencies:
      a load banks its result view in [w_ldv] ([DLdRes], scoped to one
      instruction by [LInstr]), [LRegW rd srcs] assigns
      [w_regv[rd] := V(srcs)], [LCtrl srcs] raises [w_vcap], and a
      fulfil's EXT view [fulfil_vext] joins [w_vcap] and the operand
      views of its own [asrc]/[vsrc].  Chain those and the exit fulfil's
      EXT view already covers the entry timestamp — which is [fcov], the
      relativized coverage [WeakRobustMain.edges_split_cyc] asks for.
      This is the case that covers every xv6 store control-dependent on
      a branch that read the entry message ([while (started == 0)],
      [if (holding(lk)) panic], every critical-section store after a
      lock spin).

    - **THE CO-CHAIN ON AN RMW-ONLY BYTE** ([rmw_reads_pred],
      [excl_window_pred]).  On a byte all of whose writers are [LRmw]
      events (A4's [WeakRobustDisc.rmw_written]) every RMW reads the
      write IMMEDIATELY BELOW its own — [excl_ok] kills the foreign
      writes in the window and the read's own [readable] floor kills the
      agent's own.  This is the structural half of the CS-window
      argument.

    - **THE CS WINDOWS** ([cs_windows_ordered]).  Two agents' windows on
      a lock word are ORDERED in gmo, and the later window's acquire
      reads at or above the earlier window's release.  FINDING (recorded
      in the design's §4): the DISJOINTNESS of the windows is NOT a
      machine fact — [excl_ok] makes the RMW itself atomic, not the
      critical section, and a co-order that interleaves two windows is
      perfectly consistent with every machine rule (mutual exclusion is
      a statement about the lock word's VALUES, which Layer 1 never
      inspects).  So disjointness enters as the explicitly named premise
      [win_excl] — SF-1's real content — and everything else is proved.

    - **THE LOCK-MEDIATED READ** ([cs_read_covered]).  Under the window
      order, a plain critical-section read of a message written inside
      the previous window is COVERED: the reader's own acquire is an
      [aq] RMW that read at or above the writer's release
      ([WeakRobustDisc.disciplined_covered]).  And the OTHER order is
      contradictory ([cs_read_before_absurd], via
      [WeakRobustDisc.release_lt]) — which is the design's "a plain CS
      read is ALWAYS covered or contradictory".

    - **THE A/D CAS STRUCTURAL FACT** ([no_gdep2_back_to_po_pred]).  A
      cycle cannot re-enter an agent's own earlier event from a later
      one within that agent, because [gpo] is a strict order on indices.
      One line, but the design cites it by name.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph WeakRobust WeakRobustProv
                            WeakRobustAcyc WeakRobustLin WeakRobustOrd
                            WeakRobustSer WeakRobustAcyc2 WeakRobustSim
                            WeakRobustMain WeakRobustDisc.

Local Open Scope Z_scope.

(* ================================================================== *)
(** ** 1. THE D2 COMPONENTS ALONG ONE STEP

    [w_regv] and [w_ldv] are the two [wstate] fields that are NOT
    monotone ([WeakMem]'s D2 finding: [LInstr] resets the load bank and
    [LRegW] OVERWRITES a register view), so [ws_le] says nothing about
    them and every fact below has to be established per label. *)

(** The VALUE-dependency operand list of a memory label — [lb_asrc]'s
    twin (the address list already has a name in [WeakRobustGraph]). *)
Definition lb_vsrc (l : wlabel) : list dsrc :=
  match l with
  | LStore _ _ _ _ vsrc => vsrc
  | LRmw _ _ _ _ _ _ vsrc => vsrc
  | LExStore _ _ _ _ vsrc => vsrc
  | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
  | LCtrl _ | LInstr | LExLoad _ _ _ _ => []
  end.

Lemma srcs_view_ge ws s srcs :
  s ∈ srcs → (dsrc_view ws s ≤ srcs_view ws srcs)%nat.
Proof.
  induction srcs as [|x l IH]; [by intros ?%elem_of_nil|].
  rewrite srcs_view_cons.
  intros [->|Hin]%elem_of_cons; [lia|]. have := IH Hin. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** *** [w_regv] is untouched by everything but [LRegW] *)

Lemma load_post_at_regv ws aq vpre a t :
  w_regv (load_post_at ws aq vpre a t) = w_regv ws.
Proof. done. Qed.

Lemma load_post_fold_regv aq vpre ats ws :
  w_regv (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_regv ws.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws; [done|].
  by rewrite /= IH load_post_at_regv.
Qed.

Lemma load_post_run_d_regv ws aq vaddr base ts :
  w_regv (load_post_run_d ws aq vaddr base ts) = w_regv ws.
Proof.
  rewrite /load_post_run_d /ctrl_post /= /load_post_bytes_d.
  apply load_post_fold_regv.
Qed.

(** THE RMW SPLIT (S2): the exclusive read is the load through a [w_res]
    write, which none of these three components sees. *)
Lemma exload_post_run_d_regv ws aq vaddr base ts :
  w_regv (exload_post_run_d ws aq vaddr base ts) = w_regv ws.
Proof. rewrite /exload_post_run_d /ws_res_set /=. apply load_post_run_d_regv. Qed.

Lemma store_post_d_regv ws rl vf a t :
  w_regv (store_post_d ws rl vf a t) = w_regv ws.
Proof. done. Qed.

Lemma store_post_fold_d_regv rl vf as_ t ws :
  w_regv (foldl (λ w a, store_post_d w rl vf a t) ws as_) = w_regv ws.
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [done|].
  by rewrite /= IH store_post_d_regv.
Qed.

Lemma store_post_run_d_regv ws rl vaddr vdata base n t :
  w_regv (store_post_run_d ws rl vaddr vdata base n t) = w_regv ws.
Proof.
  rewrite /store_post_run_d /ctrl_post /= /store_post_bytes_d.
  apply store_post_fold_d_regv.
Qed.

Lemma fence_post_regv ws pr pw sr sw :
  w_regv (fence_post ws pr pw sr sw) = w_regv ws.
Proof. done. Qed.

Lemma ctrl_post_regv ws v : w_regv (ctrl_post ws v) = w_regv ws.
Proof. done. Qed.

Lemma instr_post_regv ws : w_regv (instr_post ws) = w_regv ws.
Proof. done. Qed.

(* ------------------------------------------------------------------ *)
(** *** [w_ldv] only grows, except at [LInstr] *)

Lemma load_post_at_ldv_ge ws aq vpre a t :
  (w_ldv ws ≤ w_ldv (load_post_at ws aq vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma load_post_at_ldv_read ws aq vpre a t :
  fwd_view ws aq a t = t → (t ≤ w_ldv (load_post_at ws aq vpre a t))%nat.
Proof. intros H. rewrite /load_post_at /= H. lia. Qed.

Lemma load_post_fold_ldv_ge aq vpre ats ws :
  (w_ldv ws
   ≤ w_ldv (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws; [simpl; lia|].
  etrans; [apply load_post_at_ldv_ge|apply IH].
Qed.

Lemma load_post_fold_ldv aq vpre ats ws a t :
  (a, t) ∈ ats → fwd_view ws aq a t = t →
  (t ≤ w_ldv (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin Hfv.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin].
  - simpl. etrans; [by apply (load_post_at_ldv_read ws aq vpre a t)|].
    apply (load_post_fold_ldv_ge aq vpre l (load_post_at ws aq vpre a t)).
  - apply IH; [exact Hin|]. by rewrite /fwd_view load_post_at_fwd.
Qed.

Lemma load_post_run_d_ldv_ge ws aq vaddr base ts :
  (w_ldv ws ≤ w_ldv (load_post_run_d ws aq vaddr base ts))%nat.
Proof.
  rewrite /load_post_run_d ctrl_post_ldv /load_post_bytes_d.
  apply load_post_fold_ldv_ge.
Qed.

Lemma exload_post_run_d_ldv_ge ws aq vaddr base ts :
  (w_ldv ws ≤ w_ldv (exload_post_run_d ws aq vaddr base ts))%nat.
Proof.
  rewrite /exload_post_run_d /ws_res_set /=. apply load_post_run_d_ldv_ge.
Qed.

Lemma load_post_run_d_ldv ws aq vaddr base ts (j : nat) t :
  ts !! j = Some t → fwd_view ws aq (base + Z.of_nat j) t = t →
  (t ≤ w_ldv (load_post_run_d ws aq vaddr base ts))%nat.
Proof.
  intros Ht Hfv. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run_d ctrl_post_ldv /load_post_bytes_d.
  apply (load_post_fold_ldv _ _ _ _ (base + Z.of_nat j) t); [|exact Hfv].
  apply elem_of_list_lookup_2 with j.
  rewrite /load_run_ats lookup_zip_with
          (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Lemma exload_post_run_d_ldv ws aq vaddr base ts (j : nat) t :
  ts !! j = Some t → fwd_view ws aq (base + Z.of_nat j) t = t →
  (t ≤ w_ldv (exload_post_run_d ws aq vaddr base ts))%nat.
Proof.
  intros Ht Hfv. rewrite /exload_post_run_d /ws_res_set /=.
  exact (load_post_run_d_ldv ws aq vaddr base ts j t Ht Hfv).
Qed.

Lemma store_post_d_ldv ws rl vf a t :
  w_ldv (store_post_d ws rl vf a t) = w_ldv ws.
Proof. done. Qed.

Lemma store_post_fold_d_ldv rl vf as_ t ws :
  w_ldv (foldl (λ w a, store_post_d w rl vf a t) ws as_) = w_ldv ws.
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [done|].
  by rewrite /= IH store_post_d_ldv.
Qed.

Lemma store_post_run_d_ldv ws rl vaddr vdata base n t :
  w_ldv (store_post_run_d ws rl vaddr vdata base n t) = w_ldv ws.
Proof.
  rewrite /store_post_run_d ctrl_post_ldv /store_post_bytes_d.
  apply store_post_fold_d_ldv.
Qed.

Lemma fence_post_ldv ws pr pw sr sw :
  w_ldv (fence_post ws pr pw sr sw) = w_ldv ws.
Proof. done. Qed.

Lemma regw_post_ldv ws rd v : w_ldv (regw_post ws rd v) = w_ldv ws.
Proof. done. Qed.

Lemma instr_post_ldv ws : w_ldv (instr_post ws) = 0%nat.
Proof. done. Qed.

(** [writes_in] widens with its upper bound. *)
Lemma writes_in_le log a lo hi hi' :
  (hi ≤ hi')%nat → writes_in log a lo hi → writes_in log a lo hi'.
Proof. intros Hle (t & ? & ? & m & ? & ?). exists t. split_and!; [lia|lia|]. by exists m. Qed.

(* ------------------------------------------------------------------ *)
(** *** [fulfil_vext] dominates [w_vcap] and the operand views

    [WeakPromise.fulfil_vpre] is a max over [w_vcap] (RVWMO ppo 11 —
    that is what makes a CONTROL dependency an ordering) and
    [fulfil_vpre_d] joins the label's own operand views on top (ppo
    9/10).  [WeakRobustAcyc.fulfil_vext_vwNew] is the [w_vwNew] shadow
    of the same statement. *)

Lemma fulfil_vpre_d_vcap ws rl vd : (w_vcap ws ≤ fulfil_vpre_d ws rl vd)%nat.
Proof. rewrite /fulfil_vpre_d /fulfil_vpre. lia. Qed.

Lemma fulfil_vext_vcap ws l v :
  fulfil_vext ws l = Some v → (w_vcap ws ≤ v)%nat.
Proof.
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
    simpl; try done.
  - intros [= <-]. apply fulfil_vpre_d_vcap.
  - intros [= <-].
    etrans; [apply ws_le_vcap, load_post_run_d_le|apply fulfil_vpre_d_vcap].
  (* [LExStore]: [LStore]'s arm verbatim (RMW split S1) *)
  - intros [= <-]. apply fulfil_vpre_d_vcap.
Qed.

Lemma fulfil_vext_srcs ws l v s :
  fulfil_vext ws l = Some v → (s ∈ lb_asrc l ∨ s ∈ lb_vsrc l) →
  (dsrc_view ws s ≤ v)%nat.
Proof.
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
    simpl; try (by intros _ [?%elem_of_nil|?%elem_of_nil]); try done.
  - intros [= <-] Hin. etrans; [|apply fulfil_vpre_d_vd].
    destruct Hin as [Hin|Hin]; have := srcs_view_ge ws s _ Hin; lia.
  - intros [= <-] Hin. etrans; [|apply fulfil_vpre_d_vd].
    destruct Hin as [Hin|Hin]; have := srcs_view_ge ws s _ Hin; lia.
  (* [LExStore]: [LStore]'s arm verbatim (RMW split S1) *)
  - intros [= <-] Hin. etrans; [|apply fulfil_vpre_d_vd].
    destruct Hin as [Hin|Hin]; have := srcs_view_ge ws s _ Hin; lia.
Qed.

(* ================================================================== *)
(** ** 2. THE [astep_ok] LAYER

    One case per LABEL, in the style of [WeakRobustGraph]'s and
    [WeakRobustAcyc]'s [astep_ok_*] blocks. *)

Section astep.
  Context {P : Type}.
  Implicit Types ag : wpagent P.

  (** A step that is not an [LRegW] TO [rd] leaves [rd]'s view alone. *)
  Lemma astep_ok_regv_ne img log i ag l f D rd :
    astep_ok img log i ag l f D →
    (∀ srcs, l ≠ LRegW rd srcs) →
    regv (f (pa_ws ag)) rd = regv (pa_ws ag) rd.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [-> _] _.
    - intros (_ & -> & _) _. by rewrite /regv load_post_run_d_regv.
    - intros (ts & kc & _ & _ & _ & -> & _) _. by rewrite /regv store_post_run_d_regv.
    - intros (ts & kc & _ & _ & _ & _ & _ & _ & -> & _) _.
      by rewrite /regv store_post_run_d_regv load_post_run_d_regv.
    - intros [-> _] _. by rewrite /regv fence_post_regv.
    - by intros [-> _] _.
    - intros [-> _] Hne. apply regv_regw_post_ne. intros ->. by apply (Hne wsrc).
    - intros [-> _] _. by rewrite /regv ctrl_post_regv.
    - intros [-> _] _. by rewrite /regv instr_post_regv.
    (* THE RMW SPLIT (S2): the reservation wrapper is transparent to
       [w_regv] / [w_ldv] / every view. *)
    - intros (_ & -> & _) _. by rewrite /regv exload_post_run_d_regv.
    - intros (ts & kc & R & _ & _ & _ & _ & _ & _ & _ & -> & _) _.
      by rewrite /regv store_post_run_d_regv.
  Qed.

  (** …and an [LRegW rd srcs] assigns it [V(srcs)] exactly. *)
  Lemma astep_ok_regw_eq img log i ag rd srcs f D :
    astep_ok img log i ag (LRegW rd srcs) f D →
    regv (f (pa_ws ag)) rd = srcs_view (pa_ws ag) srcs.
  Proof. intros [-> _]. apply regv_regw_post_eq. Qed.

  (** [w_ldv] only grows, except at the instruction boundary [LInstr]. *)
  Lemma astep_ok_ldv_ge img log i ag l f D :
    astep_ok img log i ag l f D → l ≠ LInstr →
    (w_ldv (pa_ws ag) ≤ w_ldv (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [-> _] _.
    - intros (_ & -> & _) _. apply load_post_run_d_ldv_ge.
    - intros (ts & kc & _ & _ & _ & -> & _) _. by rewrite store_post_run_d_ldv.
    - intros (ts & kc & _ & _ & _ & _ & _ & _ & -> & _) _.
      rewrite store_post_run_d_ldv. apply load_post_run_d_ldv_ge.
    - intros [-> _] _. by rewrite fence_post_ldv.
    - by intros [-> _] _.
    - intros [-> _] _. by rewrite regw_post_ldv.
    - intros [-> _] _. by rewrite ctrl_post_ldv.
    - by intros _ Hne.
    (* THE RMW SPLIT (S2) *)
    - intros (_ & -> & _) _. apply exload_post_run_d_ldv_ge.
    - intros (ts & kc & R & _ & _ & _ & _ & _ & _ & _ & -> & _) _.
      by rewrite store_post_run_d_ldv.
  Qed.

  (** THE LOAD BANKS ITS RESULT VIEW: an UNFORWARDED read of [ts] leaves
      [w_ldv] at least [ts] — [DLdRes]'s whole content (PARM's
      [res := (val, view_post)]). *)
  Lemma astep_ok_read_ldv img log i ag l f D a ts :
    astep_ok img log i ag l f D →
    fwd_view (pa_ws ag) (lb_aq l) a ts = ts →
    (a, ts) ∈ lb_reads l →
    (ts ≤ w_ldv (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - intros _ _ Hin%elem_of_nil. done.
    - intros (_ & -> & _) Hfv [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      by apply (load_post_run_d_ldv (pa_ws ag) aq
                  (srcs_view (pa_ws ag) asrc) base (tvs.*1) j ts Hts).
    - intros _ _ Hin%elem_of_nil. done.
    - intros (tsf & kc & _ & _ & _ & _ & _ & _ & -> & _) Hfv
             [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      rewrite store_post_run_d_ldv.
      by apply (load_post_run_d_ldv (pa_ws ag) aq
                  (srcs_view (pa_ws ag) asrc) base (tvs.*1) j ts Hts).
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
    (* THE RMW SPLIT (S2) *)
    - intros (_ & -> & _) Hfv [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : ((xtvs.*1)) !! j = Some ts by rewrite list_lookup_fmap Hj.
      by apply (exload_post_run_d_ldv (pa_ws ag) xaq
                  (srcs_view (pa_ws ag) xasrc) xbase (xtvs.*1) j ts Hts).
    - intros _ _ Hin%elem_of_nil. done.
  Qed.

  (** [LCtrl srcs] raises [w_vcap] to [V(srcs)] (PARM's
      [Local.control]). *)
  Lemma astep_ok_ctrl_vcap img log i ag srcs f D :
    astep_ok img log i ag (LCtrl srcs) f D →
    (srcs_view (pa_ws ag) srcs ≤ w_vcap (f (pa_ws ag)))%nat.
  Proof. intros [-> _]. rewrite /ctrl_post /=. lia. Qed.

  (** THE READ'S OWN COHERENCE FLOOR: [readable]'s second conjunct,
      pulled down to the agent's [coh] (the pre-view only widens the
      forbidden interval). *)
  Lemma astep_ok_read_nowrites img log i ag l f D a ts :
    astep_ok img log i ag l f D → (a, ts) ∈ lb_reads l →
    ¬ writes_in log a ts (coh (pa_ws ag) a).
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - intros _ Hin%elem_of_nil. done.
    - intros (Hr & _ & _) [j [v [Hj ->]]]%elem_of_tvs_reads Hw.
      destruct (Hr j ts v Hj) as (_ & (_ & Hnw) & _). apply Hnw.
      eapply writes_in_le; [|exact Hw]. lia.
    - intros _ Hin%elem_of_nil. done.
    - intros (tsf & kc & _ & _ & _ & Hr & _) [j [v [Hj ->]]]%elem_of_tvs_reads Hw.
      destruct (Hr j ts v Hj) as (_ & (_ & Hnw) & _). apply Hnw.
      eapply writes_in_le; [|exact Hw]. lia.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    (* THE RMW SPLIT (S2) *)
    - intros (Hr & _ & _) [j [v [Hj ->]]]%elem_of_tvs_reads Hw.
      destruct (Hr j ts v Hj) as (_ & (_ & Hnw) & _). apply Hnw.
      eapply writes_in_le; [|exact Hw]. lia.
    - intros _ Hin%elem_of_nil. done.
  Qed.

  (** THE RMW WRITES WHAT IT READS: the read half's byte [a] is a byte of
      the write half's run ([length tvs = length data] at a common
      [base], an [astep_ok] conjunct), so the fulfilled timestamp lands
      in [coh a].  This is the coherence half of "an rmw's read and write
      cover the same bytes", stated without touching [msg_byte]. *)
  Lemma astep_ok_read_fulfil_coh img log i ag l f ts a tr :
    astep_ok img log i ag l f (Some ts) → (a, tr) ∈ lb_reads l →
    (ts ≤ coh (f (pa_ws ag)) a)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
    - intros (tsf & kc & Hlen & _ & _ & _ & _ & _ & -> & Heq)
             [j [v [Hj ->]]]%elem_of_tvs_reads.
      injection Heq as Heq. subst tsf. simpl.
      apply store_post_run_d_coh. rewrite -Hlen. by eapply lookup_lt_Some.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    (* THE RMW SPLIT (S2): VACUOUS on both halves (design §7) *)
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
  Qed.

End astep.

(* ================================================================== *)
(** ** 3. THE TRACE LAYER

    Same section shape as [WeakRobustDisc]'s [Section disc]: the two
    hypotheses S1 takes ([ptraces_wf], [ptraces_fwd_own]) and nothing
    else. *)

Section l2.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (TS : ptraces P D).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hfo : ptraces_fwd_own TS).

  Implicit Types T : atrace P D.
  Implicit Types e : gev.

  Local Notation Img := (pt_img TS).
  Local Notation Log := (pt_log TS).

  (** An event exists at every position strictly below one that has an
      agent record. *)
  Lemma ev_at_lt i T k k' ag' :
    pt_trs TS !! i = Some T → at_ags T !! k' = Some ag' → (k < k')%nat →
    ∃ ev, at_evs T !! k = Some ev.
  Proof.
    intros HT Hag' Hlt.
    have [Hlen _] : atrace_wf pstep Img Log i T by apply Hwf.
    apply lookup_lt_is_Some_2.
    apply lookup_lt_Some in Hag'. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** C3: THE DEPENDENT EXIT

      The three carriers the D2 machine threads a timestamp through:
      the load bank [w_ldv] ([DLdRes]), a register view [regv]
      ([DReg r]), and the control view [w_vcap]. *)

  Definition ldcarry T (k : nat) (ts : nat) : Prop :=
    ∃ ag, at_ags T !! k = Some ag ∧ (ts ≤ w_ldv (pa_ws ag))%nat.

  Definition rcarry T (k : nat) (r : wreg) (ts : nat) : Prop :=
    ∃ ag, at_ags T !! k = Some ag ∧ (ts ≤ regv (pa_ws ag) r)%nat.

  Definition vcapat T (k : nat) (ts : nat) : Prop :=
    ∃ ag, at_ags T !! k = Some ag ∧ (ts ≤ w_vcap (pa_ws ag))%nat.

  (** THE TWO "NO INTERVENING …" SIDE CONDITIONS.  Both are TRACE FACTS
      (a statement about the labels in a window of one agent's trace),
      and both are FORCED: [w_ldv] is reset by [LInstr] at every
      instruction start and [regv r] is OVERWRITTEN by an [LRegW r _]
      — neither component is monotone (the D2 finding), so the window
      has to be named. *)
  Definition no_instr T (k1 k2 : nat) : Prop :=
    ∀ n ev, (k1 ≤ n)%nat → (n < k2)%nat → at_evs T !! n = Some ev →
      ae_lb ev ≠ LInstr.

  Definition no_regw T (k1 k2 : nat) (r : wreg) : Prop :=
    ∀ n ev srcs, (k1 ≤ n)%nat → (n < k2)%nat → at_evs T !! n = Some ev →
      ae_lb ev ≠ LRegW r srcs.

  (* ---- the three carriers propagate ---- *)

  Lemma ldcarry_S i T k ts ev :
    pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
    ae_lb ev ≠ LInstr → ldcarry T k ts → ldcarry T (S k) ts.
  Proof.
    intros HT Hev Hne (ag & Hag & Hge).
    destruct (step_at pstep TS Hwf i T k ev HT Hev)
      as (ag1 & ag' & f & Hag1 & Hag' & Hok & Hws).
    have Heq : ag1 = ag by congruence. subst ag1.
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    etrans; [exact Hge|]. by eapply astep_ok_ldv_ge.
  Qed.

  Lemma ldcarry_mono i T k1 k2 ts ag2 :
    pt_trs TS !! i = Some T → (k1 ≤ k2)%nat →
    at_ags T !! k2 = Some ag2 →
    no_instr T k1 k2 → ldcarry T k1 ts → ldcarry T k2 ts.
  Proof.
    intros HT Hle Hag2 Hni Hc.
    have Hgen : ∀ n, (k1 + n ≤ k2)%nat → ldcarry T (k1 + n)%nat ts.
    { induction n as [|n IH]; intros Hn; [by rewrite Nat.add_0_r|].
      have Hprev := IH ltac:(lia).
      destruct (ev_at_lt i T (k1 + n)%nat k2 ag2 HT Hag2 ltac:(lia))
        as (ev & Hev).
      have Hstep := ldcarry_S i T (k1 + n)%nat ts ev HT Hev
                      (Hni (k1 + n)%nat ev ltac:(lia) ltac:(lia) Hev) Hprev.
      by rewrite Nat.add_succ_r. }
    have Hx := Hgen (k2 - k1)%nat ltac:(lia).
    by replace (k1 + (k2 - k1))%nat with k2 in Hx by lia.
  Qed.

  Lemma rcarry_S i T k r ts ev :
    pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
    (∀ srcs, ae_lb ev ≠ LRegW r srcs) →
    rcarry T k r ts → rcarry T (S k) r ts.
  Proof.
    intros HT Hev Hne (ag & Hag & Hge).
    destruct (step_at pstep TS Hwf i T k ev HT Hev)
      as (ag1 & ag' & f & Hag1 & Hag' & Hok & Hws).
    have Heq : ag1 = ag by congruence. subst ag1.
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    rewrite (astep_ok_regv_ne Img Log i ag (ae_lb ev) f (ae_ts ev) r Hok Hne).
    exact Hge.
  Qed.

  Lemma rcarry_mono i T k1 k2 r ts ag2 :
    pt_trs TS !! i = Some T → (k1 ≤ k2)%nat →
    at_ags T !! k2 = Some ag2 →
    no_regw T k1 k2 r → rcarry T k1 r ts → rcarry T k2 r ts.
  Proof.
    intros HT Hle Hag2 Hnw Hc.
    have Hgen : ∀ n, (k1 + n ≤ k2)%nat → rcarry T (k1 + n)%nat r ts.
    { induction n as [|n IH]; intros Hn; [by rewrite Nat.add_0_r|].
      have Hprev := IH ltac:(lia).
      destruct (ev_at_lt i T (k1 + n)%nat k2 ag2 HT Hag2 ltac:(lia))
        as (ev & Hev).
      have Hstep := rcarry_S i T (k1 + n)%nat r ts ev HT Hev
                      (λ srcs, Hnw (k1 + n)%nat ev srcs ltac:(lia) ltac:(lia) Hev)
                      Hprev.
      by rewrite Nat.add_succ_r. }
    have Hx := Hgen (k2 - k1)%nat ltac:(lia).
    by replace (k1 + (k2 - k1))%nat with k2 in Hx by lia.
  Qed.

  (** [w_vcap] IS in [ws_le], so it needs no window at all. *)
  Lemma vcapat_mono i T k1 k2 ts ag2 :
    pt_trs TS !! i = Some T → (k1 ≤ k2)%nat →
    at_ags T !! k2 = Some ag2 → vcapat T k1 ts → vcapat T k2 ts.
  Proof.
    intros HT Hle Hag2 (ag & Hag & Hge).
    exists ag2. split; [exact Hag2|].
    have Hmono := ws_mono pstep TS Hwf i T k1 k2 ag ag2 HT Hle Hag Hag2.
    have := ws_le_vcap _ _ Hmono. lia.
  Qed.

  (* ---- the three links ---- *)

  (** (1) THE LOAD BANKS ITS RESULT.  [read_unforwarded] is the same
      side condition [WeakRobustDisc.disciplined_covered] takes, and
      [WeakRobustDisc.foreign_ts_unforwarded] discharges it for any
      foreign message. *)
  Lemma ldcarry_of_read i T kr evr a ts :
    pt_trs TS !! i = Some T →
    at_evs T !! kr = Some evr →
    (a, ts) ∈ lb_reads (ae_lb evr) →
    read_unforwarded Log i (ae_lb evr) ts →
    ldcarry T (S kr) ts.
  Proof.
    intros HT Hev Hin Hunf.
    destruct (step_at pstep TS Hwf i T kr evr HT Hev)
      as (ag & ag' & f & Hag & Hag' & Hok & Hws).
    have Hfv : fwd_view (pa_ws ag) (lb_aq (ae_lb evr)) a ts = ts.
    { eapply fwd_own_read_unforwarded; [|exact Hunf].
      by eapply (Hfo i T kr ag HT Hag). }
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    by eapply (astep_ok_read_ldv Img Log i ag (ae_lb evr) f (ae_ts evr) a ts).
  Qed.

  (** (2) [LRegW rd srcs] WITH [DLdRes ∈ srcs]: the load's result view
      moves into a register. *)
  Lemma rcarry_of_ldres i T k1 ev1 rd srcs ts :
    pt_trs TS !! i = Some T →
    at_evs T !! k1 = Some ev1 → ae_lb ev1 = LRegW rd srcs → DLdRes ∈ srcs →
    ldcarry T k1 ts → rcarry T (S k1) rd ts.
  Proof.
    intros HT Hev Hlb Hin (ag & Hag & Hge).
    destruct (step_at pstep TS Hwf i T k1 ev1 HT Hev)
      as (ag1 & ag' & f & Hag1 & Hag' & Hok & Hws).
    have Heq : ag1 = ag by congruence. subst ag1.
    rewrite Hlb in Hok.
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    rewrite (astep_ok_regw_eq Img Log i ag rd srcs f (ae_ts ev1) Hok).
    have := srcs_view_ge (pa_ws ag) DLdRes srcs Hin. simpl. lia.
  Qed.

  (** (3) [LRegW rd srcs] WITH [DReg r ∈ srcs]: the register-to-register
      hop. *)
  Lemma rcarry_of_regw i T k2 ev rd srcs r ts :
    pt_trs TS !! i = Some T →
    at_evs T !! k2 = Some ev → ae_lb ev = LRegW rd srcs → DReg r ∈ srcs →
    rcarry T k2 r ts → rcarry T (S k2) rd ts.
  Proof.
    intros HT Hev Hlb Hin (ag & Hag & Hge).
    destruct (step_at pstep TS Hwf i T k2 ev HT Hev)
      as (ag1 & ag' & f & Hag1 & Hag' & Hok & Hws).
    have Heq : ag1 = ag by congruence. subst ag1.
    rewrite Hlb in Hok.
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    rewrite (astep_ok_regw_eq Img Log i ag rd srcs f (ae_ts ev) Hok).
    have := srcs_view_ge (pa_ws ag) (DReg r) srcs Hin. simpl. lia.
  Qed.

  (** (4) [LCtrl srcs] WITH [DReg r ∈ srcs]: the branch resolves and the
      capture view rises (RVWMO ppo 11). *)
  Lemma vcapat_of_ctrl i T kc evc srcs r ts :
    pt_trs TS !! i = Some T →
    at_evs T !! kc = Some evc → ae_lb evc = LCtrl srcs → DReg r ∈ srcs →
    rcarry T kc r ts → vcapat T (S kc) ts.
  Proof.
    intros HT Hev Hlb Hin (ag & Hag & Hge).
    destruct (step_at pstep TS Hwf i T kc evc HT Hev)
      as (ag1 & ag' & f & Hag1 & Hag' & Hok & Hws).
    have Heq : ag1 = ag by congruence. subst ag1.
    rewrite Hlb in Hok.
    exists ag'. split; [exact Hag'|]. rewrite Hws.
    have Hc := astep_ok_ctrl_vcap Img Log i ag srcs f (ae_ts evc) Hok.
    have := srcs_view_ge (pa_ws ag) (DReg r) srcs Hin. simpl. lia.
  Qed.

  (* ---- the two exits ---- *)

  (** THE CONTROL EXIT, packaged as [fcov]: [w_vcap] is monotone and
      [fulfil_vext] dominates it. *)
  Lemma fcov_of_vcap i T kc k' ev' ts :
    pt_trs TS !! i = Some T → vcapat T kc ts → (kc ≤ k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    fcov T k' ts.
  Proof.
    intros HT Hv Hle Hev' Hsome.
    destruct (step_at pstep TS Hwf i T k' ev' HT Hev')
      as (ag' & agn & f' & Hag' & _ & Hok' & _).
    destruct Hsome as [ts' Hts']. rewrite Hts' in Hok'.
    destruct (astep_ok_fulfil_vext Img Log i ag' (ae_lb ev') f' ts' Hok')
      as (v & Hv' & _).
    destruct (vcapat_mono i T kc k' ts ag' HT Hle Hag' Hv) as (ag2 & Hag2 & Hge).
    have Heq : ag2 = ag' by congruence. subst ag2.
    exists ag', ev', v. split_and!; [exact Hag'|exact Hev'|exact Hv'|].
    have := fulfil_vext_vcap (pa_ws ag') (ae_lb ev') v Hv'. lia.
  Qed.

  Theorem fcov_of_ctrl_dep i T kc k' evc ev' srcs r ts :
    pt_trs TS !! i = Some T →
    at_evs T !! kc = Some evc → ae_lb evc = LCtrl srcs → DReg r ∈ srcs →
    rcarry T kc r ts →
    (kc < k')%nat → at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    fcov T k' ts.
  Proof.
    intros HT Hev Hlb Hin Hc Hlt Hev' Hsome.
    eapply (fcov_of_vcap i T (S kc) k' ev' ts HT);
      [by eapply vcapat_of_ctrl|lia|exact Hev'|exact Hsome].
  Qed.

  (** THE DATA/ADDRESS EXIT: the fulfilling label NAMES the chain's
      register in its own [asrc]/[vsrc] (RVWMO ppo 9/10). *)
  Theorem fcov_of_data_dep i T k' ev' r ts :
    pt_trs TS !! i = Some T → rcarry T k' r ts →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    (DReg r ∈ lb_asrc (ae_lb ev') ∨ DReg r ∈ lb_vsrc (ae_lb ev')) →
    fcov T k' ts.
  Proof.
    intros HT (ag & Hag & Hge) Hev' Hsome Hin.
    destruct (step_at pstep TS Hwf i T k' ev' HT Hev')
      as (ag' & agn & f' & Hag' & _ & Hok' & _).
    have Heq : ag' = ag by congruence. subst ag'.
    destruct Hsome as [ts' Hts']. rewrite Hts' in Hok'.
    destruct (astep_ok_fulfil_vext Img Log i ag (ae_lb ev') f' ts' Hok')
      as (v & Hv & _).
    exists ag, ev', v. split_and!; [exact Hag|exact Hev'|exact Hv|].
    have := fulfil_vext_srcs (pa_ws ag) (ae_lb ev') v (DReg r) Hv Hin.
    simpl. lia.
  Qed.

  (* ---- the register chain ---- *)

  Fixpoint rchain T (k : nat) (r : wreg) (hs : list (nat * wreg)) : Prop :=
    match hs with
    | [] => True
    | h :: hs' =>
        (k ≤ h.1)%nat ∧ no_regw T k h.1 r ∧
        (∃ ev srcs, at_evs T !! h.1 = Some ev ∧
                    ae_lb ev = LRegW h.2 srcs ∧ DReg r ∈ srcs) ∧
        rchain T (S h.1) h.2 hs'
    end.

  Fixpoint rchain_end (k : nat) (r : wreg) (hs : list (nat * wreg))
      : nat * wreg :=
    match hs with
    | [] => (k, r)
    | h :: hs' => rchain_end (S h.1) h.2 hs'
    end.

  Lemma rchain_le T k r hs :
    rchain T k r hs → (k ≤ (rchain_end k r hs).1)%nat.
  Proof.
    revert k r. induction hs as [|h hs IH]; intros k r; simpl; [lia|].
    intros (Hle & _ & _ & Hch). have := IH (S h.1) h.2 Hch. lia.
  Qed.

  (** THE CHAIN LEMMA.  Note the explicit NO-OVERWRITE side condition
      inside [rchain]: [regv] is not monotone (the D2 finding), so the
      view has to be tracked PER REGISTER between the writes. *)
  Theorem regv_of_dep_chain i T k r ts hs :
    pt_trs TS !! i = Some T →
    rcarry T k r ts → rchain T k r hs →
    rcarry T (rchain_end k r hs).1 (rchain_end k r hs).2 ts.
  Proof.
    revert k r. induction hs as [|h hs IH]; intros k r HT Hc Hch; [exact Hc|].
    destruct Hch as (Hle & Hnw & (ev & srcs & Hev & Hlb & Hin) & Hch').
    simpl. apply (IH (S h.1) h.2 HT); [|exact Hch'].
    eapply (rcarry_of_regw i T h.1 ev h.2 srcs r ts HT Hev Hlb Hin).
    destruct (ag_at pstep TS Hwf i T h.1 ev HT Hev) as (agh & Hagh).
    by eapply (rcarry_mono i T k h.1 r ts agh HT Hle Hagh Hnw).
  Qed.

  (** ================= C3, ASSEMBLED =================

      The load at [kr] reads [ts]; the load-result register write sits at
      [k0] in the SAME INSTRUCTION (no [LInstr] between — this is what
      scopes [DLdRes]); a register chain [hs] carries the view on; and
      the exit is either a branch ([LCtrl]) whose capture view then
      dominates every later fulfil, or the fulfil's own operand list.
      Either way the exit fulfil at [k'] is [fcov T k' ts], which is
      exactly what [WeakRobustMain.edges_split_cyc] asks of a segment. *)
  Theorem fcov_of_dep_chain i T kr evr a ts k0 ev0 rd0 srcs0 hs
      kc rend evc ctrl k' ev' :
    pt_trs TS !! i = Some T →
    (** the entry read *)
    at_evs T !! kr = Some evr → (a, ts) ∈ lb_reads (ae_lb evr) →
    read_unforwarded Log i (ae_lb evr) ts →
    (** the load-result register write, IN THE SAME INSTRUCTION *)
    (S kr ≤ k0)%nat → no_instr T (S kr) k0 →
    at_evs T !! k0 = Some ev0 → ae_lb ev0 = LRegW rd0 srcs0 →
    DLdRes ∈ srcs0 →
    (** the register-to-register chain *)
    rchain T (S k0) rd0 hs →
    rchain_end (S k0) rd0 hs = (kc, rend) →
    (** the branch *)
    at_evs T !! kc = Some evc → ae_lb evc = LCtrl ctrl → DReg rend ∈ ctrl →
    (** the exit fulfil *)
    (kc < k')%nat → at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    fcov T k' ts.
  Proof.
    intros HT Hevr Hin Hunf Hle0 Hni Hev0 Hlb0 Hld Hch Hend
           Hevc Hlbc Hinc Hlt Hev' Hsome.
    (* (1) the load banks its result *)
    have Hld1 : ldcarry T (S kr) ts by eapply ldcarry_of_read.
    (* (2) …which survives to [k0] (no [LInstr] in between) *)
    destruct (ag_at pstep TS Hwf i T k0 ev0 HT Hev0) as (ag0 & Hag0).
    have Hld0 : ldcarry T k0 ts
      by eapply (ldcarry_mono i T (S kr) k0 ts ag0).
    (* (3) …and moves into [rd0] *)
    have Hr0 : rcarry T (S k0) rd0 ts by eapply rcarry_of_ldres.
    (* (4) …down the register chain *)
    have Hrc := regv_of_dep_chain i T (S k0) rd0 ts hs HT Hr0 Hch.
    rewrite Hend /= in Hrc.
    (* (5) …into [w_vcap] at the branch, and so into every later EXT *)
    by eapply (fcov_of_ctrl_dep i T kc k' evc ev' ctrl rend ts).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** C1/C2: THE SEGMENT INEQUALITY FROM THE ENTRY'S OWN DISCIPLINE

      [h] is the segment head — the cross-rf entry, reading [ts] from a
      FOREIGN fulfil [esrc] — and [kf] the segment's exit fulfil.  If the
      entry read is [aq] (C2) or a [pr ∧ sw] fence sits between it and
      [kd ≤ kf] (C1), then [ts < ts_f]: S1 for that segment, with no
      coverage bookkeeping at all.  This is [WeakRobustDisc]'s
      [acquire_release_lt] restated in the segment's coordinates (the
      agent record at [kd] is DERIVED from the exit fulfil's existence
      rather than supplied). *)
  Theorem S1_of_disciplined i esrc T h kd kf ts ts_f a :
    esrc.1 ≠ i → pt_trs TS !! i = Some T →
    gev_reads TS (i, h) a ts → gev_ts TS esrc = Some ts →
    disciplined T h kd → (h < kd)%nat → (kd ≤ kf)%nat →
    gev_ts TS (i, kf) = Some ts_f →
    (ts < ts_f)%nat.
  Proof.
    intros Hne HT Hrd Hsrc Hdisc H1 H2 Hf.
    destruct (gev_ts_at TS i T kf ts_f HT Hf) as (evf & Hevf & _).
    have [Hlen _] : atrace_wf pstep Img Log i T by apply Hwf.
    have [agd Hagd] : is_Some (at_ags T !! kd).
    { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hevf. lia. }
    by eapply (acquire_release_lt pstep TS Hwf Hfo i esrc T h kd kf ts ts_f a
                 agd).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE CO-CHAIN ON AN RMW-ONLY BYTE

      [WeakRobustDisc.rmw_written] (A4) says every writer of a lock word
      is an [LRmw].  The structural consequence is that the writes of
      that byte form a chain in timestamp order in which every RMW reads
      the write IMMEDIATELY BELOW its own: the [excl_ok] conjunct of
      [astep_ok]'s [LRmw] arm kills the FOREIGN writes inside the window
      ([WeakRobustSer.gev_read_fulfil]), and the read's own [readable]
      floor plus the rmw's own coherence gain kill the agent's own. *)

  (** Two writes of one byte by one agent are ordered by trace index —
      the [coh] bracket of [WeakRobustSer.writes_b_coh]. *)
  Lemma writes_b_po_lt L i k1 k2 t1 t2 :
    writes_b TS L (i, k1) t1 → writes_b TS L (i, k2) t2 →
    (k1 < k2)%nat → (t1 < t2)%nat.
  Proof.
    intros H1 H2 Hlt.
    destruct (proj1 (gev_wf_bounds TS (i, k1)) (writes_b_wf TS L (i, k1) t1 H1))
      as (T & HT & _). simpl in HT.
    have HT2 : pt_trs TS !! (i, k2).1 = Some T by simpl.
    destruct (writes_b_coh pstep TS L (i, k1) t1 T Hwf HT H1)
      as (ag1 & agn1 & _ & Hagn1 & _ & Hhi1).
    destruct (writes_b_coh pstep TS L (i, k2) t2 T Hwf HT2 H2)
      as (ag2 & agn2 & Hag2 & _ & Hlo2 & _).
    simpl in Hagn1, Hag2.
    have Hmono := ws_mono pstep TS Hwf i T (S k1) k2 agn1 ag2 HT
                    ltac:(lia) Hagn1 Hag2.
    have := ws_le_coh _ _ L Hmono. lia.
  Qed.

  (** THE PREDECESSOR FACT: nothing writes [L] strictly between what an
      rmw READ on [L] and what it FULFILLED. *)
  Theorem rmw_reads_pred L e tr t e' t' :
    gev_reads TS e L tr → gev_ts TS e = Some t →
    writes_b TS L e' t' → ¬ ((tr < t')%nat ∧ (t' < t)%nat).
  Proof.
    intros Hrd Hts Hw' (Hlo & Hhi).
    destruct (writes_b_author pstep TS L e' t' Hwf Hw')
      as (m' & Hm' & Hb' & Htid').
    destruct (decide (e'.1 = e.1)) as [Hag|Hne]; last first.
    { (* FOREIGN write: [excl_ok]'s window. *)
      destruct (gev_read_fulfil pstep TS e L tr t Hwf Hrd Hts) as (_ & Hnw).
      apply Hnw. exists t'. split_and!; [lia|lia|].
      exists m'. split_and!; [exact Hm'|exact Hb'|].
      rewrite Htid'. by intros [= ?]. }
    (* OWN write.  Get [e]'s own step first. *)
    have Hwfe : gev_wf TS e by eapply gev_reads_wf.
    destruct Hwfe as [ev Hev].
    destruct (gev_step pstep TS e ev Hwf Hev)
      as (T & age & agne & st' & f & HT & Hage & Hagne & _ & Hok & Hwse).
    have Hrd' : (L, tr) ∈ lb_reads (ae_lb ev).
    { destruct Hrd as (l & Hl & Hin).
      rewrite /gev_lb Hev /= in Hl. by simplify_eq. }
    have Htse : ae_ts ev = Some t by rewrite /gev_ts Hev /= in Hts.
    rewrite Htse in Hok.
    have HT' : pt_trs TS !! e'.1 = Some T by rewrite Hag.
    destruct (writes_b_coh pstep TS L e' t' T Hwf HT' Hw')
      as (agp & agn & Hagp & Hagn & Hlo' & Hhi').
    destruct (Nat.lt_trichotomy e'.2 e.2) as [Hk|[Hk|Hk]].
    - (* [e'] is po-BEFORE the read: its write already sits in [coh], and
         [readable] forbids reading strictly below [coh]. *)
      have Hmono := ws_mono pstep TS Hwf e'.1 T (S e'.2) e.2 agn age
                      HT' ltac:(lia) Hagn Hage.
      have Hcoh := ws_le_coh _ _ L Hmono.
      eapply (astep_ok_read_nowrites (pt_img TS) (pt_log TS) e.1 age
                (ae_lb ev) f (Some t) L tr Hok Hrd').
      exists t'. split_and!; [lia|lia|].
      exists m'. split; [exact Hm'|exact Hb'].
    - (* the SAME event: it would fulfil two timestamps *)
      have He : e' = e.
      { destruct e as [x y], e' as [x' y']. simpl in Hag, Hk. by subst. }
      subst e'. destruct Hw' as (Hts' & _). rewrite Hts in Hts'.
      simplify_eq. lia.
    - (* [e'] is po-AFTER: the rmw's own write half already raised [coh]
         to [t], and [e']'s fulfil demands [coh < t' < t]. *)
      have Hcohe : (t ≤ coh (pa_ws agne) L)%nat.
      { rewrite Hwse.
        by eapply (astep_ok_read_fulfil_coh (pt_img TS) (pt_log TS) e.1 age
                     (ae_lb ev) f t L tr). }
      have Hmono := ws_mono pstep TS Hwf e'.1 T (S e.2) e'.2 agne agp
                      HT' ltac:(lia) Hagne Hagp.
      have := ws_le_coh _ _ L Hmono. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE CRITICAL-SECTION WINDOWS

      A window of agent [i] on the lock word [L]: an ACQUIRE at trace
      index [ka] that reads [L] at [t_a] and fulfils [t_w], and a
      RELEASE at [kr > ka] that fulfils [t_r].  (In xv6 both are
      [amoswap.w] — the release is [__sync_lock_release], i.e. an rmw
      too — which is what makes A4's [rmw_written] hold of the lock
      word at all.) *)
  Definition cs_window (L : Z) (i ka kr t_a t_w t_r : nat) : Prop :=
    gev_reads TS (i, ka) L t_a ∧ writes_b TS L (i, ka) t_w ∧
    (ka < kr)%nat ∧ writes_b TS L (i, kr) t_r.

  Lemma cs_window_lt L i ka kr t_a t_w t_r :
    cs_window L i ka kr t_a t_w t_r → (t_w < t_r)%nat.
  Proof.
    intros (_ & Hw & Hlt & Hr). by eapply (writes_b_po_lt L i ka kr).
  Qed.

  (** THE MUTUAL-EXCLUSION PREMISE.

      **FINDING (Layer-2 design §4, corrected).**  The DISJOINTNESS of
      two agents' critical sections is NOT a machine fact.  [excl_ok]
      makes the RMW ITSELF atomic (no foreign write between its read and
      its write); it says nothing about the interval between an agent's
      acquire and its release, and a coherence order that interleaves two
      windows violates no rule of the machine.  Mutual exclusion is a
      statement about the lock word's VALUES, which Layer 1 never
      inspects — it is exactly SF-1, and it enters here as a named
      hypothesis. *)
  Definition win_excl (L : Z) (i t_w t_r : nat) : Prop :=
    ∀ e t, writes_b TS L e t → e.1 ≠ i → ¬ ((t_w < t)%nat ∧ (t < t_r)%nat).

  (** …and GIVEN it, the windows are ORDERED, and the later window's
      ACQUIRE reads at or above the earlier window's RELEASE — which is
      the inequality the lock-mediated-read lemma consumes. *)
  Theorem cs_windows_ordered L i j ka_i kr_i ta_i tw_i tr_i
                                 ka_j kr_j ta_j tw_j tr_j :
    i ≠ j →
    cs_window L i ka_i kr_i ta_i tw_i tr_i →
    cs_window L j ka_j kr_j ta_j tw_j tr_j →
    win_excl L i tw_i tr_i → win_excl L j tw_j tr_j →
    (tr_i ≤ ta_j)%nat ∨ (tr_j ≤ ta_i)%nat.
  Proof.
    intros Hij Hwi Hwj Hei Hej.
    have Hlti := cs_window_lt L i ka_i kr_i ta_i tw_i tr_i Hwi.
    have Hltj := cs_window_lt L j ka_j kr_j ta_j tw_j tr_j Hwj.
    destruct Hwi as (Hrdi & Hwwi & Hkli & Hwri).
    destruct Hwj as (Hrdj & Hwwj & Hklj & Hwrj).
    (* two writes with the same timestamp have the same author *)
    have Hauth : ∀ (e1 e2 : gev) t, writes_b TS L e1 t → writes_b TS L e2 t →
                   e1.1 = e2.1.
    { intros e1 e2 t Hx Hy.
      destruct (writes_b_author pstep TS L e1 t Hwf Hx) as (m1 & Hm1 & _ & Ht1).
      destruct (writes_b_author pstep TS L e2 t Hwf Hy) as (m2 & Hm2 & _ & Ht2).
      have Hm : m1 = m2 by congruence. subst m2. congruence. }
    have Hne_ts : ∀ (e1 e2 : gev) t1 t2, writes_b TS L e1 t1 →
                    writes_b TS L e2 t2 → e1.1 ≠ e2.1 → t1 ≠ t2.
    { intros e1 e2 t1 t2 Hx Hy Hne ->. apply Hne. by eapply Hauth. }
    have Hij' : ((i, ka_i) : gev).1 ≠ ((j, ka_j) : gev).1 := Hij.
    destruct (Nat.lt_trichotomy tw_i tw_j) as [Hlt|[Heq|Hgt]].
    - (* [i]'s window opens first: [j]'s acquire write cannot land inside
         it, so [i]'s release precedes it — and nothing writes [L]
         between [j]'s read and [j]'s write. *)
      left.
      have Hnin : ¬ ((tw_i < tw_j)%nat ∧ (tw_j < tr_i)%nat)
        by eapply (Hei (j, ka_j) tw_j Hwwj ltac:(simpl; lia)).
      have Hge : (tr_i ≤ tw_j)%nat by lia.
      have Hnee : tr_i ≠ tw_j
        by eapply (Hne_ts (i, kr_i) (j, ka_j) tr_i tw_j Hwri Hwwj
                     ltac:(simpl; lia)).
      have Hpred := rmw_reads_pred L (j, ka_j) ta_j tw_j (i, kr_i) tr_i
                      Hrdj (proj1 Hwwj) Hwri.
      lia.
    - by destruct (Hne_ts (i, ka_i) (j, ka_j) tw_i tw_j Hwwi Hwwj Hij' Heq).
    - right.
      have Hnin : ¬ ((tw_j < tw_i)%nat ∧ (tw_i < tr_j)%nat)
        by eapply (Hej (i, ka_i) tw_i Hwwi ltac:(simpl; lia)).
      have Hge : (tr_j ≤ tw_i)%nat by lia.
      have Hnee : tr_j ≠ tw_i
        by eapply (Hne_ts (j, kr_j) (i, ka_i) tr_j tw_i Hwrj Hwwi
                     ltac:(simpl; lia)).
      have Hpred := rmw_reads_pred L (i, ka_i) ta_i tw_i (j, kr_j) tr_j
                      Hrdi (proj1 Hwwi) Hwrj.
      lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE LOCK-MEDIATED READ IS NOT AN EARLY READ

      Under the window order, a PLAIN critical-section read of a message
      written inside the PREVIOUS window is COVERED: the reader's own
      acquire is an [aq] rmw that read at or above the writer's release
      ([WeakRobustDisc.disciplined_covered], A1).  Nothing here is about
      pf-realness; it is the trace half the design's §4 asks for. *)
  Theorem cs_read_covered L j Tj esrc ka_j h ta_j ts_m agh evaj :
    esrc.1 ≠ j →
    pt_trs TS !! j = Some Tj →
    at_evs Tj !! ka_j = Some evaj → lb_aq (ae_lb evaj) = true →
    gev_reads TS (j, ka_j) L ta_j →
    gev_ts TS esrc = Some ta_j →
    (** the message read sits at or below what [j]'s acquire acquired —
        supplied by [cs_windows_ordered] ([ts_m < tr_i ≤ ta_j]) *)
    (ts_m ≤ ta_j)%nat →
    (ka_j < h)%nat → at_ags Tj !! h = Some agh →
    covered Tj h ts_m.
  Proof.
    intros Hne HT Hev Haq Hrd Hsrc Hle Hlt Hagh.
    eapply covered_mono_ts; [|exact Hle].
    eapply (acquire_covered pstep TS Hwf Hfo j esrc Tj ka_j h L ta_j agh);
      [exact Hne|exact HT|exact Hrd|exact Hsrc| |exact Hlt|exact Hagh].
    left. by exists evaj.
  Qed.

  (** THE COMPOSITE, in the design's own terms: [i]'s message [ts_m] is
      written INSIDE [i]'s window, [j] reads it inside [j]'s window, and
      [j]'s window is the LATER one — then the read is covered at every
      position from [j]'s acquire on. *)
  Corollary cs_read_covered_window L i j Tj esrc
      ka_i kr_i ta_i tw_i tr_i ka_j kr_j ta_j tw_j tr_j h ts_m agh evaj :
    i ≠ j →
    cs_window L i ka_i kr_i ta_i tw_i tr_i →
    cs_window L j ka_j kr_j ta_j tw_j tr_j →
    win_excl L i tw_i tr_i → win_excl L j tw_j tr_j →
    (** [j]'s window is the later one *)
    (ta_i < tr_j)%nat →
    (** [ts_m] is written inside [i]'s window *)
    (ta_i < ts_m)%nat → (ts_m < tr_i)%nat →
    (** [j]'s acquire, and [j]'s plain read after it *)
    pt_trs TS !! j = Some Tj →
    at_evs Tj !! ka_j = Some evaj → lb_aq (ae_lb evaj) = true →
    esrc.1 ≠ j → gev_ts TS esrc = Some ta_j →
    (ka_j < h)%nat → at_ags Tj !! h = Some agh →
    covered Tj h ts_m.
  Proof.
    intros Hij Hwi Hwj Hei Hej Hlate Hlo Hhi HT Hev Haq Hne Hsrc Hlt Hagh.
    have Hord := cs_windows_ordered L i j ka_i kr_i ta_i tw_i tr_i
                   ka_j kr_j ta_j tw_j tr_j Hij Hwi Hwj Hei Hej.
    have Hrdj : gev_reads TS (j, ka_j) L ta_j by destruct Hwj as (? & _).
    eapply (cs_read_covered L j Tj esrc ka_j h ta_j ts_m agh evaj);
      [exact Hne|exact HT|exact Hev|exact Haq|exact Hrdj|exact Hsrc| |
       exact Hlt|exact Hagh].
    destruct Hord as [Hord|Hord]; lia.
  Qed.

  (** …AND THE OTHER ORDER IS CONTRADICTORY.  If [j]'s window came
      BEFORE [i]'s, [j]'s plain read of [ts_m] is separated from [j]'s
      own release by a [pr ∧ sw] fence (or is itself [aq]), so
      [ts_m < tr_j]; but the window order gives [tr_j ≤ ta_i] and
      [ts_m] was written inside [i]'s window, i.e. [ta_i < ts_m].  This
      is the design's "[ts_m < t_r(j) < t_a(i) < ts_m]". *)
  Theorem cs_read_before_absurd j Tj h kr_j ts_m ta_i tr_j evh a :
    pt_trs TS !! j = Some Tj →
    at_evs Tj !! h = Some evh → (a, ts_m) ∈ lb_reads (ae_lb evh) →
    read_unforwarded Log j (ae_lb evh) ts_m →
    disciplined Tj h kr_j → (h < kr_j)%nat →
    gev_ts TS (j, kr_j) = Some tr_j →
    (tr_j ≤ ta_i)%nat → (ta_i < ts_m)%nat →
    False.
  Proof.
    intros HT Hev Hin Hunf Hdisc Hlt Hts Hle Hlo.
    destruct (gev_ts_at TS j Tj kr_j tr_j HT Hts) as (evr & Hevr & _).
    destruct (ag_at pstep TS Hwf j Tj kr_j evr HT Hevr) as (agr & Hagr).
    have Hcov : covered Tj kr_j ts_m
      by eapply (disciplined_covered pstep TS Hwf Hfo j Tj h kr_j evh a ts_m agr).
    have := covered_fulfil_lt pstep TS Hwf j Tj kr_j kr_j ts_m tr_j HT Hcov
              ltac:(lia) Hts.
    lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE A/D CAS STRUCTURAL FACT

      The walker's CAS [c] is po-before every data access [d] of the same
      agent in the same instruction.  A cycle through the message [c]
      published and back into [c] via [d] would need a [gdep2] path from
      [d] to [c] WITHIN that agent — impossible, because [gpo] is a
      strict order on the trace index and a path that leaves the agent
      and comes back re-enters at some index, never below.  The
      one-liner the design cites: [c] cannot be reached from a po-later
      event of its own agent without closing a cycle. *)
  Lemma gpo_no_return c d : c.1 = d.1 → (c.2 < d.2)%nat → ¬ gpo TS d c.
  Proof. intros _ Hlt (_ & Hlt' & _). lia. Qed.

  Theorem no_gdep2_back_to_po_pred c d :
    gdep2_acyclic TS →
    c.1 = d.1 → (c.2 < d.2)%nat → gev_wf TS c → gev_wf TS d →
    ¬ tc (gdep2 TS) d c.
  Proof.
    intros Hacyc Hag Hlt Hc Hd Hpath.
    apply (Hacyc c). eapply tc_l; [|exact Hpath].
    apply gpo_gdep2. by split_and!.
  Qed.

End l2.
