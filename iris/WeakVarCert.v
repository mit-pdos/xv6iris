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

    WHAT IS NOT HERE YET is the phase-[true] half: from a FAMILY of confined
    runs, one per [Φ]-admissible window value, produce
    [wstep_ok_racy … true].  That is the next slice, and the three
    difficulties it has to face are recorded in the worklist (the successor's
    views depend on the read TIMESTAMP, not its value; SC lockstep is lost, so
    the premise must be a family at patched memories; and the TRACE ITSELF
    varies with the value read, which is why [WeakCert.wP_eff_pin] — whose
    trace is a parameter — is the wrong home). *)
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

(* The whole file is over [exec_eff] and the peel; no [riscv_step], hence no
   platform axioms. *)
Print Assumptions wstep_ok_racy_false_of_confined.
