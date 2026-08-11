(** * WeakVarCert.v — CONFINEMENT FOR A VARIANT-TOLERANT WINDOW (6a)

    WHAT THIS IS FOR.  [WeakCert]'s confinement theorem turns ONE confined
    [exec_eff] run into [WeakBridge.wstep_ok], and it can do that only because
    every non-self-pinning read in the trace is [pinned_read]: pinnedness is
    what collapses the oracle's timestamp to the canonical one, so the single
    SC run determines the weak run.  The page-table walk's LEAF slot is not
    pinnable — the hardware walker writes A/D bits back, from any hart, lazily
    — so that route is closed for every S-mode instruction.

    [WeakRacy.wstep_ok_racy] is the peel that tolerates such a window: it
    quantifies over the admissible timestamps and values instead of naming the
    canonical one, and (since slice 1) it filters the values by
    [WeakRacy.wadm_filter]'s [Φ], which for the walk is "every admissible word
    is an A/D variant of the canonical leaf" —
    [WeakKpt.wtlb_res_pt_translateAddr_at]'s collapse conjunct.  What is
    missing is a PRODUCER: something that discharges [wstep_ok_racy] for a
    real instruction the way [WeakCert.wstep_eff_confined_pin] discharges
    [wstep_ok].

    THIS FILE IS THE POST-RACY HALF OF THAT PRODUCER.  Once the racy read is
    behind, [wstep_ok_racy] at phase [false] is [wstep_ok] plus one extra
    demand: every remaining access is DISJOINT from the window (which is what
    lets [WeakRacy.exec_of_wrun_win] carry the patched memory through
    unchanged).  So the evidence is exactly [WeakCert]'s — one confined run,
    with its trace pinned — plus [trace_disj].

    ONE PREMISE IS NOT [WeakCert]'s, AND THE DIFFERENCE IS THE WHOLE POINT.
    [WeakCert] compares the confined memory against the flat one
    ([mm ⊆ wflat …]).  After a racy read that is FALSE: the run continues on a
    memory whose window holds the word the read returned, not the coherent
    one.  So the comparison is against the PATCHED flat memory,
    [write_bytes (wflat …) ra rn wp] — [WeakRacy.wpatch_st]'s memory — and the
    two arms that consumed the old premise now go through
    [WeakRacy.read_bytes_patch_disj] and [WeakRacy.write_bytes_patch_comm]
    instead.  Both need only DISJOINTNESS, which is what [trace_disj] carries;
    the patch value [wp] itself is never inspected.

    THE PHASE-[true] HALF (§4) takes a FAMILY of confined runs, one per
    [Φ]-satisfying window value, at the memory PATCHED with that value, and
    produces [wstep_ok_racy … true].  Its racy arm hands each [(ts, w)] to §2
    at [wp := w] — that is the designed seam between the two halves — and the
    three difficulties the worklist records are visible in its statement:

      - the successor's views come from the read TIMESTAMP, not its value, so
        the racy arm still quantifies over [ts]; the family does NOT, because
        [ts] moves only [wm_ws], which no [exec_eff] fact mentions;
      - SC lockstep is lost, so the premise is a family at the PATCHED
        memories rather than one [exec_eff] fact — and the confined run at
        [w] READS [w] back ([WeakRacy.write_bytes_lookup_at]), which is what
        makes the family the right shape rather than merely a sound one;
      - the TRACE varies with the value, so it is existentially quantified
        per member (which is also why [WeakCert.wP_eff_pin], whose trace is a
        parameter, is the wrong home for a walking instruction). *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakExec.
Require Import WeakBridge.
Require Import WeakCert.
Require Import WeakRacy.
Require Import RiscvLang RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. A trace that stays off the window

    [WeakCert.trace_pin]'s sibling: the same "read it off the effect list"
    shape, and the same three transports, for the disjointness
    [wstep_ok_racy]'s phase-[false] arms demand.  A BARRIER entry touches no
    address, so it is exempt by construction. *)

Definition trace_disj (ra : Arch.pa) (rn : N) (es : list weff) : Prop :=
  (forall (ak : akinfo) (pa : Arch.pa) (n : N),
     WEread ak pa n ∈ es -> racc_disj ra rn pa n) /\
  (forall (ak : akinfo) (pa : Arch.pa) (n : N) (v : bv (8 * n)),
     WEwrite ak pa n v ∈ es -> racc_disj ra rn pa n).

Lemma trace_disj_tail ra rn e es :
  trace_disj ra rn (e :: es) -> trace_disj ra rn es.
Proof.
  intros [Hr Hw]. split.
  - intros ak pa n Hin. apply (Hr ak pa n), elem_of_cons. by right.
  - intros ak pa n v Hin. apply (Hw ak pa n v), elem_of_cons. by right.
Qed.

Lemma trace_disj_read ra rn ak pa n es :
  trace_disj ra rn (WEread ak pa n :: es) -> racc_disj ra rn pa n.
Proof. intros [Hr _]. apply (Hr ak pa n), elem_of_cons. by left. Qed.

Lemma trace_disj_write ra rn ak pa n v es :
  trace_disj ra rn (WEwrite ak pa n v :: es) -> racc_disj ra rn pa n.
Proof. intros [_ Hw]. apply (Hw ak pa n v), elem_of_cons. by left. Qed.

(* ====================================================================== *)
(** ** 2. THE POST-RACY PEEL

    [WeakCert.wstep_eff_confined_pin] with the [wstep_ok] conclusion replaced
    by [wstep_ok_racy … false] and the agreement half dropped — the agreement
    is what needs the read's timestamp to be canonical, which is exactly what
    a racy step gives up (see the worklist).  Arm for arm the proof is
    [WeakCert]'s; the only new work is threading [trace_disj] and producing
    the extra conjunct at the two RAM arms. *)

Lemma wstep_ok_racy_false_of_confined (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop)
    (wp : bv (8 * rn)) {X} (m : M X) :
  acc_wf ra rn ->
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa)
         (x : X) (t' : mstate) (es : list weff),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    trace_pin s es ->
    trace_disj ra rn es ->
    dom mm ⊆ W ->
    mm ⊆ write_bytes (wflat (wm_img s) (wm_log s)) ra rn wp ->
    dom (mem t') ⊆ W ->
    exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t', es) ->
    wstep_ok_racy tid ra rn rak Φ false m s.
Proof.
  intros Hracc.
  induction m as [y|T oc k IH];
    intros s mm W x t' es Hwf HW0 Hpes Hdes Hdom Hsub Hdom' Hex.
  - exact I.
  - pose proof (exec_eff_exec _ _ _ _ _ Hex) as Hexc.
    destruct oc; simpl in Hex, Hexc |- *; try discriminate;
      try (exact (IH _ s mm W x t' es Hwf HW0 Hpes Hdes Hdom Hsub Hdom' Hex)).
    + (* RegWrite *)
      assert (Hp2 : trace_pin (wset_reg s reg regval) es)
        by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
      exact (IH tt (wset_reg s reg regval) mm W x t' es Hwf HW0 Hp2 Hdes
                Hdom Hsub Hdom' Hex).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d0]|] eqn:Hdr; [|discriminate].
        assert (Hp2 : trace_pin (wset_dev s d0) es)
          by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
        pose proof (IH _ (wset_dev s d0) mm W x t' es Hwf HW0 Hp2 Hdes
                      Hdom Hsub Hdom' Hex) as Hok.
        intros w d' Hdr'. simplify_eq. exact Hok.
      * destruct (read_bytes mm _ _) as [w0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff (k (inl (w0, None))) (MState (wm_regs s) mm (wm_dev s)))
          as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.ReadReq.pa t) j ∈ W)
          by (intros j Hj; apply Hdom, (read_bytes_dom mm _ _ w0 Hrb j Hj)).
        assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        assert (Hpinf : ak_pins (classify (Interface.ReadReq.access_kind t))
                          = false ->
                  forall j : nat, (j < N.to_nat n)%nat ->
                    pinned_read s (acc_addr (Interface.ReadReq.pa t) j)).
        { intros Hnp j Hj.
          apply (Hpes (classify (Interface.ReadReq.access_kind t))
                   (Interface.ReadReq.pa t) n);
            [apply elem_of_cons; by left|exact Hnp|exact Hj]. }
        assert (Hdisj : racc_disj ra rn (Interface.ReadReq.pa t) n)
          by exact (trace_disj_read ra rn _ _ _ es0 Hdes).
        assert (Hwrb : wread_bytes s (classify (Interface.ReadReq.access_kind t))
                         (Interface.ReadReq.pa t) n
                         (coh_ts s (Interface.ReadReq.pa t) n) = Some w0).
        { rewrite (wread_bytes_read_bytes s
                     (classify (Interface.ReadReq.access_kind t))
                     (Interface.ReadReq.pa t) n Hwf Hacc).
          (* off the window the patch is invisible, so the confined read IS
             the flat one *)
          rewrite -(read_bytes_patch_disj (wflat (wm_img s) (wm_log s)) ra rn wp
                      (Interface.ReadReq.pa t) n Hracc Hacc Hdisj).
          exact (read_bytes_mono mm _ _ _ w0 Hsub Hrb). }
        assert (Hp2 : trace_pin
                        (wread_post s
                           (classify (Interface.ReadReq.access_kind t))
                           (Interface.ReadReq.pa t)
                           (coh_ts s (Interface.ReadReq.pa t) n)) es0).
        { apply (trace_pin_mono s);
            [by rewrite wread_post_log|apply wread_post_ws_le
            |exact (trace_pin_tail s _ es0 Hpes)]. }
        assert (Hsub2 : mm ⊆ write_bytes
                  (wflat (wm_img (wread_post s
                                   (classify (Interface.ReadReq.access_kind t))
                                   (Interface.ReadReq.pa t)
                                   (coh_ts s (Interface.ReadReq.pa t) n)))
                        (wm_log (wread_post s
                                   (classify (Interface.ReadReq.access_kind t))
                                   (Interface.ReadReq.pa t)
                                   (coh_ts s (Interface.ReadReq.pa t) n))))
                  ra rn wp)
          by (by rewrite wread_post_img wread_post_log).
        assert (Hee2 : exec_eff (k (inl (w0, None)))
                  (MState (wm_regs (wread_post s
                                      (classify (Interface.ReadReq.access_kind t))
                                      (Interface.ReadReq.pa t)
                                      (coh_ts s (Interface.ReadReq.pa t) n))) mm
                          (wm_dev (wread_post s
                                      (classify (Interface.ReadReq.access_kind t))
                                      (Interface.ReadReq.pa t)
                                      (coh_ts s (Interface.ReadReq.pa t) n))))
                  = Some (x0, t0, es0))
          by (by rewrite wread_post_regs wread_post_dev).
        split; [exact Hacc|]. left. split_and!.
        -- exact Hdisj.
        -- exact Hpinf.
        -- intros w Hw. rewrite Hwrb in Hw. injection Hw as <-.
           exact (IH _ _ mm W x0 t0 es0 (wlog_wf_read_post _ _ _ _ Hwf) HW0 Hp2
                     (trace_disj_tail ra rn _ es0 Hdes) Hdom Hsub2 Hdom' Hee2).
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d0|] eqn:Hdw; [|discriminate].
        assert (Hp2 : trace_pin (wset_dev s d0) es)
          by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
        pose proof (IH _ (wset_dev s d0) mm W x t' es Hwf HW0 Hp2 Hdes
                      Hdom Hsub Hdom' Hex) as Hok.
        intros d' Hdw'. simplify_eq. exact Hok.
      * destruct (exec_eff (k (inl None))
                    (MState (wm_regs s)
                       (write_bytes mm (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) (wm_dev s)))
          as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.WriteReq.pa t) j ∈ W).
        { intros j Hj. apply Hdom'.
          apply (exec_dom_mono _ _ _ _ Hexc). simpl. by apply write_bytes_dom. }
        assert (Hacc : acc_wf (Interface.WriteReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        assert (Hp2 : trace_pin
                        (wwrite_post tid s
                           (classify (Interface.WriteReq.access_kind t))
                           (Interface.WriteReq.pa t) n
                           (Interface.WriteReq.value t)) es0)
          by (apply trace_pin_write; exact (trace_pin_tail s _ es0 Hpes)).
        assert (Hdom2 : dom (write_bytes mm (Interface.WriteReq.pa t) n
                               (Interface.WriteReq.value t)) ⊆ W)
          by (etrans; [apply (exec_dom_mono _ _ _ _ Hexc)|exact Hdom']).
        assert (Hdisjw : racc_disj ra rn (Interface.WriteReq.pa t) n)
          by exact (trace_disj_write ra rn _ _ _ _ es0 Hdes).
        assert (Hsub2 : write_bytes mm (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)
                        ⊆ write_bytes
                            (wflat (wm_img (wwrite_post tid s
                                   (classify (Interface.WriteReq.access_kind t))
                                   (Interface.WriteReq.pa t) n
                                   (Interface.WriteReq.value t)))
                                (wm_log (wwrite_post tid s
                                   (classify (Interface.WriteReq.access_kind t))
                                   (Interface.WriteReq.pa t) n
                                   (Interface.WriteReq.value t))))
                            ra rn wp).
        { rewrite (wflat_write tid s (classify (Interface.WriteReq.access_kind t))
                     (Interface.WriteReq.pa t) n (Interface.WriteReq.value t)).
          rewrite -(write_bytes_patch_comm (wflat (wm_img s) (wm_log s)) ra rn wp
                      (Interface.WriteReq.pa t) n (Interface.WriteReq.value t)
                      Hracc Hacc Hdisjw).
          by apply write_bytes_mono. }
        split_and!.
        -- reflexivity.
        -- exact Hacc.
        -- exact Hdisjw.
        -- exact (IH _ _ _ W x0 t0 es0
                    (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) HW0 Hp2
                    (trace_disj_tail ra rn _ es0 Hdes) Hdom2 Hsub2 Hdom' Hee).
    + (* Barrier *)
      destruct (exec_eff (k tt) (MState (wm_regs s) mm (wm_dev s)))
        as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      assert (Hp2 : trace_pin (wset_ws s (barrier_post (wm_ws s) b)) es0).
      { apply (trace_pin_mono s);
          [reflexivity|apply barrier_post_le
          |exact (trace_pin_tail s _ es0 Hpes)]. }
      exact (IH tt (wset_ws s (barrier_post (wm_ws s) b)) mm W x0 t0 es0
                Hwf HW0 Hp2 (trace_disj_tail ra rn _ es0 Hdes)
                Hdom Hsub Hdom' Hee).
Qed.

(** The [wmem_restrict] instance, which is the shape a certificate carries
    ([WeakCert.wstep_conf_eff_pin] and its twins all take [W] and restrict). *)
(** The instance the phase-[true] half will hand it: the confined memory is
    the restriction PATCHED at the window with the word the racy read
    returned — [WeakRacy.wpatch_st]'s memory, restricted. *)
Lemma wstep_ok_racy_false_of_window (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (wp : bv (8 * rn)) {X} (m : M X)
    (s : wmstate) (W : gset Arch.pa) (x : X) (t' : mstate) (es : list weff) :
  acc_wf ra rn ->
  wlog_wf (wm_log s) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (* the window itself is part of the confined footprint *)
  (forall j : nat, (j < N.to_nat rn)%nat -> pa_add ra j ∈ W) ->
  trace_pin s es ->
  trace_disj ra rn es ->
  dom (mem t') ⊆ W ->
  exec_eff m (MState (wm_regs s)
                (write_bytes (wmem_restrict s W) ra rn wp) (wm_dev s))
    = Some (x, t', es) ->
  wstep_ok_racy tid ra rn rak Φ false m s.
Proof.
  intros Hracc Hwf HW0 Hwin Hpes Hdes Hdom' Hex.
  apply (wstep_ok_racy_false_of_confined tid ra rn rak Φ wp m Hracc s
           (write_bytes (wmem_restrict s W) ra rn wp) W x t' es Hwf HW0 Hpes
           Hdes); [| |exact Hdom'|exact Hex].
  - apply write_bytes_dom_sub; [apply wmem_restrict_dom|exact Hwin].
  - by apply write_bytes_mono, wmem_restrict_sub.
Qed.

(* ====================================================================== *)
(** ** 3. THE PRE-RACY TRACE: what replaces [trace_pin] and [trace_disj]

    NEITHER §2 premise survives into the phase-[true] half, and both fail for
    the same reason: the racy read is ITSELF an entry of the trace, and it is
    neither pinned nor disjoint from the window.

    Not pinned, because that is exactly what makes it racy — the walker's leaf
    takes A/D writebacks from any hart, so no hart's index covers its latest
    write.  And it is not exempt by access kind either: [WeakInterp.classify]
    hands a walker read [AkInfo false false false] (the model emits
    [Read_plain] for the walk — see [WeakInterp]'s finding (1)), i.e.
    [ak_pins = false], which is precisely the case [WeakCert.trace_pin]
    obliges.  Not disjoint, because it IS the window.

    So each premise is weakened at that one entry, and the two weakenings have
    different characters — which is why they stay two premises rather than one
    bundle.  [trace_pin_off] is order-insensitive, like its parent, and is the
    only state-dependent one (it needs the same [pinned_read] transports).
    [trace_racy] is ORDERED and purely structural: what the window read
    separates is a PHASE, not a set. *)

(** PINNEDNESS, DEMANDED ONLY OFF THE WINDOW.  A read of the window is exempt
    wherever it occurs, which costs nothing: [trace_racy] below already admits
    at most one such read and forbids any after the phase flips. *)
Definition trace_pin_off (s : wmstate) (ra : Arch.pa) (rn : N)
    (es : list weff) : Prop :=
  forall (ak : akinfo) (pa : Arch.pa) (n : N),
    WEread ak pa n ∈ es -> ak_pins ak = false -> racc_disj ra rn pa n ->
    forall j : nat, (j < N.to_nat n)%nat -> pinned_read s (acc_addr pa j).

(** A caller that HAS whole-window pinnedness loses nothing by the weakening. *)
Lemma trace_pin_off_of_pin s ra rn es :
  trace_pin s es -> trace_pin_off s ra rn es.
Proof. intros Hp ak pa n Hin Hnp _ j Hj. exact (Hp ak pa n Hin Hnp j Hj). Qed.

(** ... and off the window the two premises together ARE [trace_pin] again,
    which is how the TAIL of a racy trace is handed to §2. *)
Lemma trace_pin_of_off s ra rn es :
  trace_disj ra rn es -> trace_pin_off s ra rn es -> trace_pin s es.
Proof.
  intros [Hr _] Hp ak pa n Hin Hnp j Hj.
  exact (Hp ak pa n Hin Hnp (Hr ak pa n Hin) j Hj).
Qed.

(** The three transports, [trace_pin]'s verbatim. *)
Lemma trace_pin_off_mono (s s' : wmstate) ra rn es :
  wm_log s' = wm_log s -> ws_le (wm_ws s) (wm_ws s') ->
  trace_pin_off s ra rn es -> trace_pin_off s' ra rn es.
Proof.
  intros Hl Hle Hp ak pa n Hin Hnp Hd j Hj.
  exact (pinned_read_mono s s' _ Hl Hle (Hp ak pa n Hin Hnp Hd j Hj)).
Qed.

Lemma trace_pin_off_tail s ra rn e es :
  trace_pin_off s ra rn (e :: es) -> trace_pin_off s ra rn es.
Proof. intros Hp ak pa n Hin. apply (Hp ak pa n), elem_of_cons. by right. Qed.

Lemma trace_pin_off_head s ra rn ak pa n es :
  trace_pin_off s ra rn (WEread ak pa n :: es) ->
  ak_pins ak = false -> racc_disj ra rn pa n ->
  forall j : nat, (j < N.to_nat n)%nat -> pinned_read s (acc_addr pa j).
Proof. intros Hp. apply (Hp ak pa n), elem_of_cons. by left. Qed.

(** THE ORDERED HALF.  Before the racy read every read is disjoint from the
    window and there is no RAM WRITE AT ALL — not "no overlapping write":
    [wstep_ok_racy]'s write arm demands [b = false], so a RAM write before the
    racy read makes the conclusion FALSE, not merely unprovable.  At the racy
    read the phase flips and the rest is §1's [trace_disj] verbatim, which is
    what §2 consumes.  A trace with no window read at all is admitted: the run
    simply never took the racy read, and then the whole family is one run.

    The two disjuncts are made EXCLUSIVE by the caller's [0 < rn] (a
    non-empty window is not disjoint from itself, [racc_disj_irrefl]), and
    that exclusivity is load-bearing: at a read arm the induction must pick
    ONE of [wstep_ok_racy]'s arms while holding a whole FAMILY of traces, so
    which disjunct a member took has to be decided by the read's address and
    width alone — data that is fixed by the monad and cannot vary with the
    patch value. *)
Fixpoint trace_racy (rak : akinfo) (ra : Arch.pa) (rn : N) (es : list weff)
    : Prop :=
  match es with
  | [] => True
  | WEread ak pa n :: es' =>
      (racc_disj ra rn pa n /\ trace_racy rak ra rn es')
      \/ (ak = rak /\ pa = ra /\ n = rn /\ trace_disj ra rn es')
  | WEwrite _ _ _ _ :: _ => False
  | WEbar _ :: es' => trace_racy rak ra rn es'
  end.

Lemma racc_disj_irrefl (ra : Arch.pa) (rn : N) :
  (0 < rn)%N -> ~ racc_disj ra rn ra rn.
Proof. rewrite /racc_disj => Hrn [H|H]; lia. Qed.

(** The two eliminations, one per disjunct, each keyed on the read's own
    footprint rather than on the trace. *)
Lemma trace_racy_disj_tail rak ra rn ak pa n es :
  (0 < rn)%N -> racc_disj ra rn pa n ->
  trace_racy rak ra rn (WEread ak pa n :: es) -> trace_racy rak ra rn es.
Proof.
  intros Hrn Hd [[_ Hr]|(_ & Hpa & Hn & _)]; [exact Hr|].
  subst pa n. by destruct (racc_disj_irrefl ra rn Hrn Hd).
Qed.

Lemma trace_racy_win_tail rak ra rn ak pa n es :
  (0 < rn)%N -> ~ racc_disj ra rn pa n ->
  trace_racy rak ra rn (WEread ak pa n :: es) ->
  ak = rak /\ pa = ra /\ n = rn /\ trace_disj ra rn es.
Proof. intros Hrn Hnd [[Hd _]|H]; [by destruct (Hnd Hd)|exact H]. Qed.

(* ====================================================================== *)
(** ** 4. THE PHASE-[true] PEEL

    From a FAMILY of confined runs — one per [Φ]-satisfying window value, at
    the confined memory PATCHED with that value — to [wstep_ok_racy … true].

    WHY A FAMILY AT PATCHED MEMORIES IS THE RIGHT SHAPE, not just a sound one:
    the confined run at [w] READS [w] back at the window
    ([WeakRacy.write_bytes_lookup_at] + [read_bytes_of_bytes]), so the member
    indexed by [w] is exactly the SC run that the racy read at value [w]
    continues, and the handoff to §2 at [wp := w] is an application with no
    reconciliation step.  Off the window the patch is invisible
    ([read_bytes_patch_disj]), so every member takes the same pre-racy path —
    which is what lets ONE member (the witness below) decide the shape of the
    arms the induction has not reached yet.

    WHY [Φ] MUST BE INHABITED.  Every pre-racy obligation — the access's
    wrap-freedom, its pinnedness, and which of the read arms it is — is read
    off a RUN, and with no [Φ]-satisfying value there is no run at all.  The
    premise is one witness, and [wadm_filter_inhabited] below produces it from
    what the rule's caller already holds.

    THE FAMILY IS INDEXED BY [Φ] ALONE, not by [Φ] and admissibility: [Φ] is
    the admissibility SURROGATE ([WeakRacy.wadm_filter] is exactly "every
    admissible word satisfies [Φ]"), so an extra [wadm] hypothesis on each
    member would narrow nothing a caller can use. *)

Lemma wstep_ok_racy_true_of_confined (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) {X} (m : M X) :
  acc_wf ra rn ->
  (0 < rn)%N ->
  (exists w0 : bv (8 * rn), Φ (fun j : nat => nth_byte w0 j)) ->
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    (* the window itself is part of the confined footprint *)
    (forall j : nat, (j < N.to_nat rn)%nat -> pa_add ra j ∈ W) ->
    dom mm ⊆ W ->
    mm ⊆ wflat (wm_img s) (wm_log s) ->
    (* THE FAMILY: one confined run per [Φ]-satisfying window value *)
    (forall w : bv (8 * rn), Φ (fun j : nat => nth_byte w j) ->
       exists (x : X) (t' : mstate) (es : list weff),
         exec_eff m (MState (wm_regs s) (write_bytes mm ra rn w) (wm_dev s))
           = Some (x, t', es) /\
         dom (mem t') ⊆ W /\
         trace_pin_off s ra rn es /\
         trace_racy rak ra rn es) ->
    wstep_ok_racy tid ra rn rak Φ true m s.
Proof.
  intros Hracc Hrn [w0 HΦ0].
  (* the patched memory holds the patch word AT the window — this is what
     makes the member indexed by [w] return [w] at the racy read *)
  assert (Hrdw : forall (u : bv (8 * rn)) (mp : gmap Arch.pa (bv 8)),
            read_bytes (write_bytes mp ra rn u) ra rn = Some u).
  { intros u mp. apply read_bytes_of_bytes. intros j Hj.
    exact (write_bytes_lookup_at mp ra rn u j Hracc Hj). }
  induction m as [y|T oc k IH]; intros s mm W Hwf HW0 Hwin Hdom Hsub Hfam.
  - exact I.
  - (* the WITNESS run, which decides every arm the family cannot *)
    destruct (Hfam w0 HΦ0) as (x0 & t0 & es0 & Hex0 & Hd0 & Hp0 & Hr0).
    destruct oc; simpl in Hex0, Hfam |- *; try discriminate;
      try (exact (IH _ s mm W Hwf HW0 Hwin Hdom Hsub Hfam)).
    + (* RegWrite: only [trace_pin_off] moves, and only by [ws_le] *)
      apply (IH tt (wset_reg s reg regval) mm W Hwf HW0 Hwin Hdom Hsub).
      intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
      exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
      apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * (* device: no effect emitted, and the answer does not depend on the
           patch (the device is not memory) *)
        destruct (dev_read _ _ _) as [[wd dd]|] eqn:Hdr;
          rewrite ?Hd ?Hdr /= in Hex0; [|discriminate].
        intros wv d' Hdr'. rewrite ?Hdr in Hdr'. simplify_eq.
        apply (IH _ (wset_dev s d') mm W Hwf HW0 Hwin Hdom Hsub).
        intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
        rewrite ?Hd ?Hdr /= in Hex1.
        exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
        apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
      * (* RAM: the witness run fixes the footprint ... *)
        destruct (read_bytes (write_bytes mm ra rn w0) (Interface.ReadReq.pa t) n)
          as [v0|] eqn:Hrb0; rewrite ?Hd ?Hrb0 /= in Hex0; [|discriminate].
        assert (Hdomp : dom (write_bytes mm ra rn w0) ⊆ W)
          by (apply write_bytes_dom_sub; [exact Hdom|exact Hwin]).
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.ReadReq.pa t) j ∈ W)
          by (intros j Hj; apply Hdomp, (read_bytes_dom _ _ _ v0 Hrb0 j Hj)).
        assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        destruct (exec_eff (k (inl (v0, None)))
                    (MState (wm_regs s) (write_bytes mm ra rn w0) (wm_dev s)))
          as [[[x1 t1] es1]|] eqn:Hee0; rewrite ?Hee0 /= in Hex0; [|discriminate].
        injection Hex0 as <- <- <-.
        split; [exact Hacc|].
        (* ... and its ADDRESS decides which arm this is, for every member at
           once: the footprint is fixed by the monad, not by the patch *)
        assert (Hdec : racc_disj ra rn (Interface.ReadReq.pa t) n \/
                       ~ racc_disj ra rn (Interface.ReadReq.pa t) n)
          by (rewrite /racc_disj; lia).
        destruct Hdec as [Hdisj|Hndisj].
        -- (* AWAY FROM THE WINDOW: [wstep_ok]'s own arm, at every member *)
           left.
           assert (Hrbmm : read_bytes mm (Interface.ReadReq.pa t) n = Some v0).
           { rewrite -(read_bytes_patch_disj mm ra rn w0 _ n Hracc Hacc Hdisj).
             exact Hrb0. }
           assert (Hrbu : forall u : bv (8 * rn),
                     read_bytes (write_bytes mm ra rn u)
                       (Interface.ReadReq.pa t) n = Some v0)
             by (intros u; rewrite (read_bytes_patch_disj mm ra rn u _ n
                                      Hracc Hacc Hdisj); exact Hrbmm).
           assert (Hwrb : wread_bytes s
                            (classify (Interface.ReadReq.access_kind t))
                            (Interface.ReadReq.pa t) n
                            (coh_ts s (Interface.ReadReq.pa t) n) = Some v0).
           { rewrite (wread_bytes_read_bytes s _ _ n Hwf Hacc).
             exact (read_bytes_mono mm _ _ _ v0 Hsub Hrbmm). }
           split_and!.
           ++ exact Hdisj.
           ++ intros Hnp j Hj.
              exact (trace_pin_off_head s ra rn _ _ _ es1 Hp0 Hnp Hdisj j Hj).
           ++ intros w Hw. rewrite Hwrb in Hw. injection Hw as <-.
              apply (IH _ (wread_post s
                             (classify (Interface.ReadReq.access_kind t))
                             (Interface.ReadReq.pa t)
                             (coh_ts s (Interface.ReadReq.pa t) n)) mm W
                       (wlog_wf_read_post _ _ _ _ Hwf) HW0 Hwin Hdom
                       ltac:(by rewrite wread_post_img wread_post_log)).
              intros u Hu.
              destruct (Hfam u Hu) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
              rewrite ?Hd ?(Hrbu u) /= in Hex2.
              destruct (exec_eff (k (inl (v0, None)))
                          (MState (wm_regs s) (write_bytes mm ra rn u) (wm_dev s)))
                as [[[x3 t3] es3]|] eqn:Hee2;
                rewrite ?Hee2 /= in Hex2; [|discriminate].
              injection Hex2 as <- <- <-.
              exists x3, t3, es3. split_and!.
              ** by rewrite wread_post_regs wread_post_dev.
              ** exact Hd2.
              ** apply (trace_pin_off_mono s);
                   [apply wread_post_log|apply wread_post_ws_le|].
                 exact (trace_pin_off_tail s ra rn _ es3 Hp2).
              ** exact (trace_racy_disj_tail rak ra rn _ _ n es3 Hrn Hdisj Hr2).
        -- (* THE RACY READ, handed to §2 at [wp := w].  The family is NOT
              indexed by [ts], and does not have to be: [wread_post] moves only
              [wm_ws], which no [exec_eff] fact mentions, and both trace
              premises transport UP the view order ([trace_pin_mono]) — so ONE
              member serves the whole [ts]-fibre.  Note [Hread] (the read is
              admissible at [ts]) is never used: the family is indexed by [Φ]
              alone, [Φ] being the admissibility surrogate. *)
           right.
           destruct (trace_racy_win_tail rak ra rn _ _ n es1 Hrn Hndisj Hr0)
             as (Hak & Hpa & Hn & _).
           subst n. rewrite Hpa Hak.
           split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
           intros ts w Hread HΦw.
           destruct (Hfam w HΦw) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
           rewrite ?Hd ?Hpa ?(Hrdw w mm) /= in Hex2.
           destruct (exec_eff (k (inl (w, None)))
                       (MState (wm_regs s) (write_bytes mm ra rn w) (wm_dev s)))
             as [[[x3 t3] es3]|] eqn:Hee2;
             rewrite ?Hee2 /= in Hex2; [|discriminate].
           injection Hex2 as <- <- <-.
           destruct (trace_racy_win_tail rak ra rn _ ra rn es3 Hrn
                       (racc_disj_irrefl ra rn Hrn) Hr2) as (_ & _ & _ & Hdes3).
           apply (wstep_ok_racy_false_of_confined tid ra rn rak Φ w _ Hracc
                    (wread_post s rak ra ts) (write_bytes mm ra rn w) W
                    x3 t3 es3 (wlog_wf_read_post _ _ _ _ Hwf) HW0).
           ++ (* the tail is disjoint, so off-window pinnedness IS pinnedness *)
              apply (trace_pin_mono s);
                [apply wread_post_log|apply wread_post_ws_le|].
              apply (trace_pin_of_off s ra rn es3 Hdes3).
              exact (trace_pin_off_tail s ra rn _ es3 Hp2).
           ++ exact Hdes3.
           ++ exact (write_bytes_dom_sub mm ra rn w W Hdom Hwin).
           ++ rewrite wread_post_img wread_post_log.
              by apply write_bytes_mono.
           ++ exact Hd2.
           ++ by rewrite wread_post_regs wread_post_dev.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * (* a device write emits no effect, so the phase is untouched *)
        destruct (dev_write _ _ _ _) as [dd|] eqn:Hdw;
          rewrite ?Hd ?Hdw /= in Hex0; [|discriminate].
        intros d' Hdw'. rewrite ?Hdw in Hdw'. simplify_eq.
        apply (IH _ (wset_dev s d') mm W Hwf HW0 Hwin Hdom Hsub).
        intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
        rewrite ?Hd ?Hdw /= in Hex1.
        exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
        apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
      * (* A RAM WRITE BEFORE THE RACY READ IS NOT MERELY UNPROVABLE, IT IS
           REFUTED: [wstep_ok_racy]'s write arm demands [b = false].  So the
           premise has to exclude it, and [trace_racy] is where it does. *)
        exfalso.
        destruct (exec_eff (k (inl None))
                    (MState (wm_regs s)
                       (write_bytes (write_bytes mm ra rn w0)
                          (Interface.WriteReq.pa t) n (Interface.WriteReq.value t))
                       (wm_dev s)))
          as [[[x1 t1] es1]|] eqn:Hee0;
          rewrite ?Hd ?Hee0 /= in Hex0; [|discriminate].
        injection Hex0 as <- <- <-. exact Hr0.
    + (* Barrier: no address, so the phase is untouched here too *)
      destruct (exec_eff (k tt) (MState (wm_regs s) (write_bytes mm ra rn w0)
                                   (wm_dev s)))
        as [[[x1 t1] es1]|] eqn:Hee0; rewrite ?Hee0 /= in Hex0; [|discriminate].
      injection Hex0 as <- <- <-.
      apply (IH tt (wset_ws s (barrier_post (wm_ws s) b)) mm W Hwf HW0 Hwin
               Hdom Hsub).
      intros u Hu. destruct (Hfam u Hu) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
      destruct (exec_eff (k tt) (MState (wm_regs s) (write_bytes mm ra rn u)
                                   (wm_dev s)))
        as [[[x3 t3] es3]|] eqn:Hee2; rewrite ?Hee2 /= in Hex2; [|discriminate].
      injection Hex2 as <- <- <-.
      exists x3, t3, es3. split_and!.
      * exact Hee2.
      * exact Hd2.
      * apply (trace_pin_off_mono s);
          [reflexivity|apply barrier_post_le|].
        exact (trace_pin_off_tail s ra rn _ es3 Hp2).
      * exact Hr2.
Qed.

(** The [wmem_restrict] instance, the shape a certificate carries — §2's
    [wstep_ok_racy_false_of_window] on this side of the racy read. *)
Lemma wstep_ok_racy_true_of_window (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) {X} (m : M X)
    (s : wmstate) (W : gset Arch.pa) :
  acc_wf ra rn ->
  (0 < rn)%N ->
  (exists w0 : bv (8 * rn), Φ (fun j : nat => nth_byte w0 j)) ->
  wlog_wf (wm_log s) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall j : nat, (j < N.to_nat rn)%nat -> pa_add ra j ∈ W) ->
  (forall w : bv (8 * rn), Φ (fun j : nat => nth_byte w j) ->
     exists (x : X) (t' : mstate) (es : list weff),
       exec_eff m (MState (wm_regs s)
                     (write_bytes (wmem_restrict s W) ra rn w) (wm_dev s))
         = Some (x, t', es) /\
       dom (mem t') ⊆ W /\
       trace_pin_off s ra rn es /\
       trace_racy rak ra rn es) ->
  wstep_ok_racy tid ra rn rak Φ true m s.
Proof.
  intros Hracc Hrn HΦ Hwf HW0 Hwin Hfam.
  exact (wstep_ok_racy_true_of_confined tid ra rn rak Φ m Hracc Hrn HΦ s
           (wmem_restrict s W) W Hwf HW0 Hwin (wmem_restrict_dom s W)
           (wmem_restrict_sub s W) Hfam).
Qed.

(** THE INHABITATION PREMISE, from what the rule's caller already holds.
    [WeakRacy.wp_wracy_load] demands [wadm_filter] and the readability of the
    window at its canonical timestamps; the canonical word is admissible, so
    the filter accepts it.  (This is [WeakRacy.wexec_of_exec_racy]'s move at
    its racy arm, extracted.) *)
Lemma wadm_filter_inhabited (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (rn : N) (Φ : (nat -> bv 8) -> Prop) :
  wadm_filter s rak ra rn Φ ->
  is_Some (wread_bytes s rak ra rn (coh_ts s ra rn)) ->
  exists w0 : bv (8 * rn), Φ (fun j : nat => nth_byte w0 j).
Proof.
  intros HΦ [w Hw]. exists w. apply HΦ.
  exact (wadm_of_wread_ok _ _ _ _ _ _ (wread_bytes_spec _ _ _ _ _ _ Hw)).
Qed.

(* The whole file is over [exec_eff] and the peel; no [riscv_step], hence no
   platform axioms. *)
Print Assumptions wstep_ok_racy_false_of_confined.
Print Assumptions wstep_ok_racy_true_of_confined.
