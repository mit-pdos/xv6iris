(** * WeakCert.v — discharging the step certificate ([wstep_cert], M3b item 2)

    M3a left the per-instruction peel [WeakBridge.wstep_ok] as an open,
    caller-supplied obligation, with the estimate that obtaining it means
    walking [riscv_step] / [try_step] / [run_hart_active] / [fetch] / decode /
    [execute] exactly as [RiscvExec.exec_riscv_step_hart_active] and
    [SmodeCore.exec_hart_active_progress_base_gen] do for [exec] — "and of the
    same size".

    THAT ESTIMATE IS WRONG, AND THIS FILE IS WHY.  The peel does not have to be
    walked at all: it can be CERTIFIED BY RUNNING THE SC INTERPRETER ON A
    CONFINED MEMORY.

    ===================== THE IDEA, IN ONE PARAGRAPH =====================

    [wstep_ok] collects, per RAM access of the run: wrap-freedom of the range,
    and — where the access kind does not already force the latest read —
    pinnedness of the read footprint.  Its content is therefore entirely
    "WHICH BYTES does this step touch".  Now: [RiscvExec.exec]'s RAM read arm
    FAILS (returns [None]) on a byte the memory map does not contain.  So if
    [exec] succeeds from a state whose memory is a SMALL map [mm] — say, just
    the four text bytes at the pc plus the four bytes of the data word — then
    every read the run performs is inside [dom mm], because a read anywhere
    else would have returned [None].  Writes are confined the same way, by the
    domain of the FINAL memory (memory only ever grows along a run).  And since
    [mm] agrees with the real (flat) memory on its domain, the run at [mm] and
    the run at the real memory are the SAME run.

    So: pinnedness of a fixed window [W], plus ONE [exec] fact re-instantiated
    at the confined state, gives [wstep_ok] for the whole step — no model
    walking, no [execR] mirror, no fetch mirror, nothing per-instruction.
    [wstep_ok_confined] (§4) is that theorem, and [wcert_ok] (§5) is it
    packaged as the [WeakInstr.wstep_cert] half it discharges.

    ===================== WHAT IT DOES *NOT* GIVE ========================

    [wstep_cert] has a second component [Q], the instruction's WEAK-MEMORY
    EFFECT (that the [.aq] really raised the scalar floor, that the fence
    really moved the index).  That one is NOT visible in [exec] — the SC
    interpreter ignores access kinds and barriers entirely — so no semantic
    argument over [exec] can produce it, and it stays a per-instruction
    obligation about the ISA, of the same nature as a decode fact.  §5 splits
    [wstep_cert] along exactly that line ([wcert_ok] ∗ the [Q] premise), so a
    leaf pays only for the effect of the ONE access it cares about. *)
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
Require Import WeakBridge.
Require Import RiscvLang RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The two memory primitives under map inclusion

    [read_bytes] only ever LOOKS at the bytes of its range, and [write_bytes]
    only ever INSERTS them; both facts are needed in the "small map ⊆ real
    memory" direction, which is what identifies the confined run with the real
    one. *)

Lemma mapM_lookup_mono (mm mm2 : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (l : list nat) (bs : list (bv 8)) :
  mm ⊆ mm2 ->
  mapM (fun j : nat => mm !! pa_add pa j) l = Some bs ->
  mapM (fun j : nat => mm2 !! pa_add pa j) l = Some bs.
Proof.
  intros Hsub Hm. apply mapM_Some. apply mapM_Some in Hm.
  eapply Forall2_impl; [exact Hm|]. intros j b Hj.
  exact (lookup_weaken _ _ _ _ Hj Hsub).
Qed.

Lemma read_bytes_mono (mm mm2 : gmap Arch.pa (bv 8)) pa n w :
  mm ⊆ mm2 -> read_bytes mm pa n = Some w -> read_bytes mm2 pa n = Some w.
Proof.
  rewrite /read_bytes => Hsub Hr.
  destruct (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)))
    as [bs|] eqn:Hm; [|discriminate].
  by rewrite (mapM_lookup_mono mm mm2 pa _ bs Hsub Hm).
Qed.

(** Every byte of a successful read is IN the map — this is what confines the
    read footprint to [dom mm]. *)
Lemma read_bytes_dom (mm : gmap Arch.pa (bv 8)) pa n w :
  read_bytes mm pa n = Some w ->
  forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ dom mm.
Proof.
  intros Hr j Hj. apply elem_of_dom.
  exists (nth_byte w j). apply (read_bytes_spec mm pa n w Hr). lia.
Qed.

Lemma write_bytes_mono {wd : N} (mm mm2 : gmap Arch.pa (bv 8)) pa n (v : bv wd) :
  mm ⊆ mm2 -> write_bytes mm pa n v ⊆ write_bytes mm2 pa n v.
Proof.
  intros Hsub. rewrite /write_bytes.
  induction (seq 0 (N.to_nat n)) as [|j l IH]; [exact Hsub|].
  simpl. by apply insert_mono.
Qed.

Lemma write_bytes_dom_mono {wd : N} (mm : gmap Arch.pa (bv 8)) pa n (v : bv wd) :
  dom mm ⊆ dom (write_bytes mm pa n v).
Proof.
  rewrite /write_bytes. induction (seq 0 (N.to_nat n)) as [|j l IH]; [done|].
  simpl. rewrite dom_insert. set_solver.
Qed.

Lemma write_bytes_dom {wd : N} (mm : gmap Arch.pa (bv 8)) pa n (v : bv wd) :
  forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ dom (write_bytes mm pa n v).
Proof.
  rewrite /write_bytes => j Hj.
  assert (Hin : j ∈ seq 0 (N.to_nat n)) by (apply elem_of_seq; lia).
  revert Hin. generalize (seq 0 (N.to_nat n)) as l. intros l.
  induction l as [|j0 l IH]; [by intros ?%elem_of_nil|].
  intros [->|Hin]%elem_of_cons; simpl; rewrite dom_insert; set_solver.
Qed.

(** MEMORY ONLY GROWS along an [exec] run — so a write's footprint is inside
    the FINAL memory's domain, which is the confinement handle for the write
    arm (a write, unlike a read, cannot fail and so confines nothing itself). *)
Lemma exec_dom_mono {X} (m : M X) :
  forall s x s', exec m s = Some (x, s') -> dom (mem s) ⊆ dom (mem s').
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hex.
  - simpl in Hex. by injection Hex as <- <-.
  - destruct oc; simpl in Hex; try discriminate;
      try (exact (IH _ _ _ _ Hex)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * etrans; [|exact (IH _ _ _ _ Hex)]. apply write_bytes_dom_mono.
Qed.

(* ====================================================================== *)
(** ** 2. Pinnedness survives the run

    [pinned_read] is "the hart's own index covers the latest write to this
    byte".  Every arm of the weak interpreter preserves it: a read, a barrier
    and a register/device effect only RAISE views, and the hart's own write
    raises [coh] at exactly the bytes whose [latest_ts] it raises. *)

Lemma pinned_read_mono (s s' : wmstate) (a : Z) :
  wm_log s' = wm_log s -> ws_le (wm_ws s) (wm_ws s') ->
  pinned_read s a -> pinned_read s' a.
Proof.
  intros Hlog Hle Hp. destruct Hle as (Hcoh & _ & _ & Hnew & _ & _).
  rewrite /pinned_read Hlog. rewrite /pinned_read in Hp.
  pose proof (Hcoh a). lia.
Qed.

(** The write case: [t ≤ coh] at every byte the window store touches. *)
Lemma store_post_bytes_coh (ws : wstate) (rl : bool) (l : list Z) (t : nat) (a : Z) :
  a ∈ l -> (t ≤ coh (store_post_bytes ws rl l t) a)%nat.
Proof.
  revert ws. induction l as [|a0 l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [Heq|Hin].
  - (* [a] is written by the head; later stores only raise [coh a] *)
    subst a0.
    change (store_post_bytes ws rl (a :: l) t)
      with (store_post_bytes (store_post ws rl a t) rl l t).
    pose proof (proj1 (store_post_bytes_le (store_post ws rl a t) rl l t) a) as Hle.
    pose proof (store_post_coh ws rl a t) as Hc. lia.
  - change (store_post_bytes ws rl (a0 :: l) t)
      with (store_post_bytes (store_post ws rl a0 t) rl l t).
    exact (IH _ Hin).
Qed.

Lemma store_post_run_coh (ws : wstate) (rl : bool) (base : Z) (n : nat)
    (t : nat) (j : nat) :
  (j < n)%nat -> (t ≤ coh (store_post_run ws rl base n t) (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite /store_post_run. apply store_post_bytes_coh.
  apply elem_of_list_fmap. exists j. split; [reflexivity|].
  apply elem_of_seq. lia.
Qed.

Lemma pinned_read_write tid (s : wmstate) ak (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (a : Z) :
  pinned_read s a -> pinned_read (wwrite_post tid s ak pa n v) a.
Proof.
  rewrite /pinned_read /wwrite_post /= => Hp.
  rewrite latest_ts_app.
  destruct (msg_writesb (wwrite_msg tid pa n v) a) eqn:Hw.
  - (* the new message writes [a]: it is in the window, and the store raised
       [coh a] to exactly the new top *)
    apply msg_writesb_true in Hw as [b Hb].
    rewrite /msg_byte /wwrite_msg /= in Hb.
    destruct (bool_decide (pa_z pa ≤ a)) eqn:Hle; [|discriminate].
    apply bool_decide_eq_true in Hle.
    assert (Hlt : (Z.to_nat (a - pa_z pa) < N.to_nat n)%nat).
    { apply lookup_lt_Some in Hb. by rewrite length_map length_seq in Hb. }
    assert (Ha : a = pa_z pa + Z.of_nat (Z.to_nat (a - pa_z pa))) by lia.
    pose proof (store_post_run_coh (wm_ws s) (ak_sync ak) (pa_z pa)
                  (N.to_nat n) (S (length (wm_log s)))
                  (Z.to_nat (a - pa_z pa)) Hlt) as Hc.
    rewrite -Ha in Hc.
    etrans; [exact Hc|apply Nat.le_max_r].
  - (* the message does not write [a]: [latest_ts] is unchanged, views grew *)
    destruct (store_post_run_le (wm_ws s) (ak_sync ak) (pa_z pa)
                (N.to_nat n) (S (length (wm_log s))))
      as (Hcoh & _ & _ & Hnew & _ & _).
    etrans; [exact Hp|]. apply Nat.max_le_compat; [exact Hnew|apply Hcoh].
Qed.

(* ====================================================================== *)
(** ** 3. Wrap-freedom out of the window

    [acc_wf] says the access range does not wrap the address space.  It is
    free from the window: a wrapping range passes through address 0, and the
    window a kernel step touches does not contain it. *)

Lemma pa_z_z_pa (z : Z) : pa_z (z_pa z) = z `mod` 18446744073709551616.
Proof.
  rewrite /pa_z pa_uint_unsigned /z_pa bv_unsigned_mword_of_int /bv_wrap.
  by assert (bv_modulus (SailStdpp.MachineWord.MachineWord.Z_idx
                (if 64 =? 32 then 34 else 64)%Z) = 18446744073709551616)
    as -> by (vm_compute; reflexivity).
Qed.

Lemma pa_z_range (a : Arch.pa) : 0 <= pa_z a < 18446744073709551616.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  assert (Hm : bv_modulus (SailStdpp.MachineWord.MachineWord.Z_idx
                 (if 64 =? 32 then 34 else 64)%Z) = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr. rewrite /pa_z pa_uint_unsigned. exact Hr.
Qed.

Lemma pa_z_add_wrap (pa : Arch.pa) (j : nat) :
  pa_z (pa_add pa j) = (pa_z pa + Z.of_nat j) `mod` 18446744073709551616.
Proof. by rewrite -(z_pa_acc_addr pa j) pa_z_z_pa /acc_addr. Qed.

Lemma acc_wf_window (W : gset Arch.pa) (pa : Arch.pa) (n : N) :
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ W) ->
  acc_wf pa n.
Proof.
  intros HW Hin. rewrite /acc_wf.
  destruct (Z.le_gt_cases (pa_z pa + Z.of_N n) 18446744073709551616) as [?|Hgt];
    [assumption|exfalso].
  pose proof (pa_z_range pa) as [Hlo Hhi].
  assert (HN : Z.of_nat (N.to_nat n) = Z.of_N n) by lia.
  set (j0 := Z.to_nat (18446744073709551616 - pa_z pa)).
  assert (Hj0 : Z.of_nat j0 = 18446744073709551616 - pa_z pa)
    by (rewrite /j0 Z2Nat.id; lia).
  assert (Hjn : (j0 < N.to_nat n)%nat) by lia.
  apply (HW _ (Hin j0 Hjn)).
  rewrite pa_z_add_wrap Hj0.
  replace (pa_z pa + (18446744073709551616 - pa_z pa))
    with 18446744073709551616 by lia.
  apply Z_mod_same_full.
Qed.

(* ====================================================================== *)
(** ** 4. THE CONFINED-EXEC CERTIFICATE

    Read the premises as: the window [W] is pinned for this hart and does not
    contain the null address; the confined map [mm] lives in the window and
    agrees with the real memory; the SC interpreter RUNS TO COMPLETION on it;
    and it never writes outside the window.  Conclusion: the whole step's peel.

    The induction is [WeakBridge]'s own ([exec_of_wexec_pinned]'s shape) with
    the confined map threaded alongside the weak state; the three arms that do
    any work are:
      - RAM read: [read_bytes mm] returned [Some], so the footprint is inside
        [dom mm ⊆ W], which gives [acc_wf] and pinnedness; and the canonical
        weak read returns the same word ([wread_bytes_read_bytes] plus
        [read_bytes_mono]), so the two runs stay in lockstep;
      - RAM write: the footprint is inside the FINAL memory's domain
        ([exec_dom_mono]), hence in [W], which gives [acc_wf];
      - [Choose]: [exec] is stuck there, so the [False] arm — i.e. the whole
        [wexec_covers] side of the merge — is discharged by the [exec] fact
        itself. *)

Lemma wstep_ok_confined (tid : option nat) {X} (m : M X) :
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa)
         (x : X) (t' : mstate),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    (forall a, a ∈ W -> pinned_read s (pa_z a)) ->
    dom mm ⊆ W ->
    mm ⊆ wflat (wm_img s) (wm_log s) ->
    dom (mem t') ⊆ W ->
    exec m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t') ->
    wstep_ok tid m s.
Proof.
  induction m as [y|T oc k IH];
    intros s mm W x t' Hwf HW0 HWp Hdom Hsub Hdom' Hex.
  - exact I.
  - destruct oc; simpl in Hex |- *; try discriminate; try exact I;
      try (exact (IH _ s mm W x t' Hwf HW0 HWp Hdom Hsub Hdom' Hex)).
    + (* RegWrite *)
      apply (IH tt (wset_reg s reg regval) mm W x t' Hwf HW0);
        [|exact Hdom|exact Hsub|exact Hdom'|exact Hex].
      intros a Ha. apply (pinned_read_mono s _ (pa_z a));
        [reflexivity|reflexivity|by apply HWp].
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d0]|] eqn:Hdr; [|discriminate].
        intros w d' Hdr'. rewrite Hdr' in Hdr. simplify_eq.
        apply (IH _ (wset_dev s _) mm W x t' Hwf HW0);
          [|exact Hdom|exact Hsub|exact Hdom'|exact Hex].
        intros a Ha. apply (pinned_read_mono s _ (pa_z a));
          [reflexivity|reflexivity|by apply HWp].
      * destruct (read_bytes mm _ _) as [w0|] eqn:Hrb; [|discriminate].
        (* the footprint is inside the window *)
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.ReadReq.pa t) j ∈ W)
          by (intros j Hj; apply Hdom, (read_bytes_dom mm _ _ w0 Hrb j Hj)).
        assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        split_and!.
        -- exact Hacc.
        -- intros _ j Hj.
           rewrite -(acc_wf_byte _ _ j Hacc Hj). by apply HWp, Hin.
        -- intros w Hw.
           (* the canonical weak read IS the confined one *)
           rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hw.
           rewrite (read_bytes_mono mm _ _ _ w0 Hsub Hrb) in Hw.
           injection Hw as <-.
           apply (IH _ (wread_post s (classify (Interface.ReadReq.access_kind t))
                          (Interface.ReadReq.pa t)
                          (coh_ts s (Interface.ReadReq.pa t) _))
                    mm W x t' (wlog_wf_read_post _ _ _ _ Hwf) HW0).
           ++ intros a Ha. apply (pinned_read_mono s _ (pa_z a));
                [by rewrite wread_post_log|apply wread_post_ws_le|by apply HWp].
           ++ exact Hdom.
           ++ by rewrite wread_post_img wread_post_log.
           ++ exact Hdom'.
           ++ by rewrite wread_post_regs wread_post_dev.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d0|] eqn:Hdw; [|discriminate].
        intros d' Hdw'. rewrite Hdw' in Hdw. simplify_eq.
        apply (IH _ (wset_dev s _) mm W x t' Hwf HW0);
          [|exact Hdom|exact Hsub|exact Hdom'|exact Hex].
        intros a Ha. apply (pinned_read_mono s _ (pa_z a));
          [reflexivity|reflexivity|by apply HWp].
      * (* the written footprint is inside the final memory, hence in [W] *)
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.WriteReq.pa t) j ∈ W).
        { intros j Hj. apply Hdom'.
          apply (exec_dom_mono _ _ _ _ Hex). simpl. by apply write_bytes_dom. }
        assert (Hacc : acc_wf (Interface.WriteReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        split; [exact Hacc|].
        apply (IH _ (wwrite_post tid s
                       (classify (Interface.WriteReq.access_kind t))
                       (Interface.WriteReq.pa t) n (Interface.WriteReq.value t))
                 (write_bytes mm (Interface.WriteReq.pa t) n
                       (Interface.WriteReq.value t)) W x t'
                 (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) HW0).
        -- intros a Ha. by apply pinned_read_write, HWp.
        -- (* dom of the written map ⊆ dom of the final memory ⊆ W *)
           etrans; [apply (exec_dom_mono _ _ _ _ Hex)|exact Hdom'].
        -- rewrite (wflat_write tid s (classify (Interface.WriteReq.access_kind t))
                      (Interface.WriteReq.pa t) n (Interface.WriteReq.value t)).
           by apply write_bytes_mono.
        -- exact Hdom'.
        -- exact Hex.
    + (* Barrier *)
      apply (IH tt (wset_ws s (barrier_post (wm_ws s) _)) mm W x t' Hwf HW0);
        [|exact Hdom|exact Hsub|exact Hdom'|exact Hex].
      intros a Ha. apply (pinned_read_mono s _ (pa_z a));
        [reflexivity|apply barrier_post_le|by apply HWp].
Qed.

(* ====================================================================== *)
(** ** 5. Packaged as the certificate

    [WeakInstr.wstep_cert cid pc P Q] is what a leaf rule ([wp_winstr]) takes.
    Its hypotheses are [PC = pc], the text window's pinnedness and [P σ]; its
    two conclusions are the peel [wstep_ok] and the instruction's weak-memory
    effect [Q].  §4 discharges the FIRST for every instruction at once, with
    [P] instantiated at [wP_conf] — "the log is well-formed and there is a
    confined witness".

    THE CONFINED MAP IS NOT SOMETHING THE LEAF HAS TO BUILD: take the real
    memory RESTRICTED to the window ([wmem_restrict]).  Its inclusion and its
    domain are then free, and the [exec] fact over it is the leaf's OWN SC
    library lemma, whose memory premises are of the shape
    "[∀ j < 4, mem !! pa_add ea j = Some (nth_byte w j)]" and hold of the
    restriction by [wmem_restrict_lookup].  That instantiation — the same
    lemma, at a second state — IS the whole per-instruction cost. *)

Definition wmem_restrict (s : wmstate) (W : gset Arch.pa) : gmap Arch.pa (bv 8) :=
  base.filter (fun kv : Arch.pa * bv 8 => kv.1 ∈ W) (wflat (wm_img s) (wm_log s)).

Lemma wmem_restrict_sub s W : wmem_restrict s W ⊆ wflat (wm_img s) (wm_log s).
Proof.
  apply map_subseteq_spec. intros a b Hb.
  by apply map_lookup_filter_Some in Hb as [? _].
Qed.

Lemma wmem_restrict_dom s W : dom (wmem_restrict s W) ⊆ W.
Proof.
  intros a [b Hb]%elem_of_dom.
  by apply map_lookup_filter_Some in Hb as [_ ?].
Qed.

Lemma wmem_restrict_lookup s W a b :
  a ∈ W -> wflat (wm_img s) (wm_log s) !! a = Some b ->
  wmem_restrict s W !! a = Some b.
Proof. intros HW Hlk. by apply map_lookup_filter_Some. Qed.

(** THE CONFINED WITNESS, as a predicate on the hart's state. *)
Definition wstep_conf (s : wmstate) : Prop :=
  exists W : gset Arch.pa,
    (forall a, a ∈ W -> pa_z a <> 0) /\
    (forall a, a ∈ W -> pinned_read s (pa_z a)) /\
    (forall tick : bool, exists t' : mstate,
       exec (riscv_step tick) (MState (wm_regs s) (wmem_restrict s W) (wm_dev s))
         = Some (tt, t') /\ dom (mem t') ⊆ W).

Definition wP_conf : wmstate -> Prop :=
  fun s => wlog_wf (wm_log s) /\ wstep_conf s.

Lemma wstep_ok_conf (tid : option nat) (s : wmstate) (tick : bool) :
  wP_conf s -> wstep_ok tid (riscv_step tick) s.
Proof.
  intros (Hwf & W & HW0 & HWp & Hex).
  destruct (Hex tick) as (t' & Ht' & Hdom').
  exact (wstep_ok_confined tid (riscv_step tick) s (wmem_restrict s W) W tt t'
           Hwf HW0 HWp (wmem_restrict_dom s W) (wmem_restrict_sub s W)
           Hdom' Ht').
Qed.

Require Import WeakInstr.

(** THE CERTIFICATE, wstep_ok half discharged for EVERY instruction at once.
    [Q] — the weak-memory effect — is the only thing left to supply, and only
    the sync instructions have one worth stating ([WeakInstr.wQ_amo_aq],
    [wQ_fence], [wQ_store]); a plain load or an ALU instruction takes
    [wQ_none] and then the certificate is UNCONDITIONAL. *)
Lemma wstep_cert_conf (cid : nat) (pc : SailStdpp.Values.mword 64)
    (Q : wmstate -> wstate -> Prop) :
  (forall (s : wmstate) (tick : bool),
     register_lookup PC (wm_regs s) = pc -> wP_conf s ->
     forall χ s' χ', wexec (Some cid) (riscv_step tick) χ s = Some (tt, s', χ') ->
       Q s (wm_ws s')) ->
  wstep_cert cid pc wP_conf Q.
Proof.
  intros HQ s tick Hpc Hacc Htext HP. split.
  - by apply wstep_ok_conf.
  - intros χ s' χ' Hex. exact (HQ s tick Hpc HP χ s' χ' Hex).
Qed.

Lemma wstep_cert_conf_none (cid : nat) (pc : SailStdpp.Values.mword 64) :
  wstep_cert cid pc wP_conf wQ_none.
Proof. apply wstep_cert_conf. intros. exact I. Qed.

(** ... and the [P]-weakening a leaf uses to fold its own resource-derived
    predicate into the certificate: anything that IMPLIES the confined witness
    certifies the step ([WeakInstr.wstep_cert_mono] is contravariant in [P]). *)
Lemma wstep_cert_of_conf (cid : nat) (pc : SailStdpp.Values.mword 64)
    (P : wmstate -> Prop) (Q : wmstate -> wstate -> Prop) :
  (forall s, P s -> wP_conf s) ->
  (forall (s : wmstate) (tick : bool),
     register_lookup PC (wm_regs s) = pc -> P s ->
     forall χ s' χ', wexec (Some cid) (riscv_step tick) χ s = Some (tt, s', χ') ->
       Q s (wm_ws s')) ->
  wstep_cert cid pc P Q.
Proof.
  intros HP HQ s tick Hpc Hacc Htext HPs. split.
  - by apply wstep_ok_conf, HP.
  - intros χ s' χ' Hex. exact (HQ s tick Hpc HPs χ s' χ' Hex).
Qed.

(* ======================================================================
   WHAT AN INSTRUCTION COSTS AT M4, given the above.

   Everything a leaf must produce for the peel is [wP_conf σ], i.e.:

     (a) [wlog_wf (wm_log σ)]        — a conjunct of [wmstate_interp];
     (b) a window [W] with [pa_z a ≠ 0] on it — the RAM window of the
         instruction's text word and its data word, both above 0x80000000;
     (c) [pinned_read σ] on [W]      — [WeakInstr.wkernel_text_pinned] for the
         text half (unwritten this era, free) and [wpt4_pinned] for the data
         half (owned), or NOTHING for an AMO's data word (the read half is
         [ak_latest], and [wstep_ok] asks for no pinnedness there — but the
         window must still be listed, since a WRITE's footprint is confined by
         the window too);
     (d) [exec (riscv_step tick) (MState (wm_regs σ) (wmem_restrict σ W)
         (wm_dev σ)) = Some (tt, t')] with [dom (mem t') ⊆ W] — the leaf's own
         SC library lemma, instantiated at a SECOND state whose memory is the
         restriction.  Its register/config premises are literally the same
         terms ([wm_regs] is shared); its memory premises are discharged from
         the same [wpt4_flat] / [wkernel_text_flat] facts through
         [wmem_restrict_lookup].

   No model walking appears anywhere in that list, and nothing in it is
   specific to the instruction beyond naming its data address. *)
