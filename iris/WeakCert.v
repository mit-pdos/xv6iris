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
    [wstep_ok_confined] (§5) is that theorem, and [wstep_cert_conf] (§6) is it
    packaged as the [WeakInstr.wstep_cert] half it discharges.

    ============ THE SECOND HALF: [Q], OFF AN EFFECT TRACE ==============

    [wstep_cert] has a second component [Q], the instruction's WEAK-MEMORY
    EFFECT (which message the step appended, that the [.aq] really raised the
    scalar floor, that the fence really moved the index).  That one is not
    visible in [exec] AS WRITTEN — the SC interpreter ignores access kinds and
    barriers entirely.  But it is visible in the SHAPE of the run, and the run
    is what [exec] walks.  So §4 INSTRUMENTS the interpreter: [exec_eff] is
    [exec] plus an EFFECT TRACE [list weff], one entry per RAM access and per
    barrier, recording exactly the data the weak interpreter's post-state
    depends on.  §5's [wstep_eff_confined] then says that under the SAME
    confinement premises the weak successor's log and views are the FOLD
    [weffs] of that trace over the pre-state.

    After that a per-instruction [Q] is a fact about a CONCRETE, two- or
    three-element effect list — pure view arithmetic, no reasoning about
    [wexec], no oracle quantifier (§7 packages it, §8 pays it for the four
    instruction classes M3c needs). *)
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
Require Import WeakGhost.
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

(** ... and the SUBSET form: a write whose base map and footprint both live in
    [X] stays inside [X].  This is the shape every store/AMO leaf's
    write-domain confinement ([dom (mem s_exec) ⊆ W]) instantiates — the
    per-leaf [w*_window_wdom] lemmas are one [apply] of this. *)
Lemma write_bytes_dom_sub {wd : N} (mm : gmap Arch.pa (bv 8)) pa n (v : bv wd)
    (X : gset Arch.pa) :
  dom mm ⊆ X ->
  (forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ X) ->
  dom (write_bytes mm pa n v) ⊆ X.
Proof.
  rewrite /write_bytes => Hbase Hin.
  assert (Hin' : forall j : nat, j ∈ seq 0 (N.to_nat n) -> pa_add pa j ∈ X)
    by (intros j Hj%elem_of_seq; apply Hin; lia).
  revert Hin'. induction (seq 0 (N.to_nat n)) as [|j l IH]; intros Hin';
    simpl; [exact Hbase|].
  rewrite dom_insert_L. apply union_least.
  - intros z ->%elem_of_singleton. apply Hin', elem_of_cons. by left.
  - apply IH. intros k Hk. apply Hin', elem_of_cons. by right.
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

(** The write case ([t ≤ coh] at every byte the window store touches) is
    [WeakMem.store_post_run_coh]: the W4 lift batch made that the canonical
    copy, so this file's duplicate (and its [store_post_bytes_coh] helper)
    are gone.  Uses below are against [WeakMem]'s. *)

Lemma pinned_read_write tid (s : wmstate) ak (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (a : Z) :
  pinned_read s a -> pinned_read (wwrite_post tid s ak pa n v) a.
Proof.
  rewrite /pinned_read /wwrite_post /= => Hp.
  rewrite latest_ts_app.
  destruct (msg_writesb (wwrite_msg tid (wm_class_of ak (wm_ws s)) pa n v) a)
    eqn:Hw.
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
(** ** 4. THE EFFECT TRACE, and the instrumented SC interpreter

    A [weff] is one weak-memory-relevant thing a run does: a RAM read (at its
    access kind, address and width — the timestamps are NOT part of it, since
    §5 shows they can only be the canonical [coh_ts]), a RAM write (the same
    plus the value), or a barrier.  Everything else a run does — registers,
    device transactions, announces — is invisible to [WeakInterp]'s log and
    views, and so emits nothing.

    [weffs] folds a trace over a state, giving the successor's log and views
    without ever mentioning the monad.  The five small facts below are all the
    algebra §7/§8 need; the load-bearing one is [weffs_congr], which says the
    fold only ever LOOKS at [wm_img]/[wm_log]/[wm_ws].  That is what lets the
    §5 induction push the fold past a register or a device write: those change
    the state, but not in any way an effect can see. *)

Inductive weff : Type :=
| WEread  (ak : akinfo) (pa : Arch.pa) (n : N)
| WEwrite (ak : akinfo) (pa : Arch.pa) (n : N) (v : bv (8 * n))
| WEbar   (b : barrier_kind).

Definition weff_apply (tid : option nat) (s : wmstate) (e : weff) : wmstate :=
  match e with
  | WEread ak pa n    => wread_post s ak pa (coh_ts s pa n)
  | WEwrite ak pa n v => wwrite_post tid s ak pa n v
  | WEbar b           => wset_ws s (barrier_post (wm_ws s) b)
  end.

Definition weffs (tid : option nat) (s : wmstate) (es : list weff) : wmstate :=
  foldl (weff_apply tid) s es.

(** The three [weff_apply] arms, spelled out, so a certificate proof never has
    to reduce the fold by hand. *)
Lemma weff_apply_read tid s ak pa n :
  weff_apply tid s (WEread ak pa n) = wread_post s ak pa (coh_ts s pa n).
Proof. reflexivity. Qed.
Lemma weff_apply_write tid s ak pa n (v : bv (8 * n)) :
  weff_apply tid s (WEwrite ak pa n v) = wwrite_post tid s ak pa n v.
Proof. reflexivity. Qed.
Lemma weff_apply_bar tid s b :
  weff_apply tid s (WEbar b) = wset_ws s (barrier_post (wm_ws s) b).
Proof. reflexivity. Qed.

Lemma weffs_nil tid s : weffs tid s [] = s.
Proof. reflexivity. Qed.
Lemma weffs_cons tid s e es :
  weffs tid s (e :: es) = weffs tid (weff_apply tid s e) es.
Proof. reflexivity. Qed.
Lemma weffs_cons2 tid s e1 e2 :
  weffs tid s [e1; e2] = weff_apply tid (weff_apply tid s e1) e2.
Proof. reflexivity. Qed.
Lemma weffs_cons3 tid s e1 e2 e3 :
  weffs tid s [e1; e2; e3]
  = weff_apply tid (weff_apply tid (weff_apply tid s e1) e2) e3.
Proof. reflexivity. Qed.

(** Two post-state projections, at the shape §8 consumes them. *)
Lemma wwrite_post_ws tid s ak pa n (v : bv (8 * n)) :
  wm_ws (wwrite_post tid s ak pa n v)
  = store_post_run (wm_ws s) (ak_sync ak) (pa_z pa) (N.to_nat n)
                   (S (length (wm_log s))).
Proof. reflexivity. Qed.

Lemma wread_post_ws_weak s ak pa ts :
  ak_coh ak = false ->
  wm_ws (wread_post s ak pa ts) = load_post_run (wm_ws s) (ak_sync ak) (pa_z pa) ts.
Proof. rewrite /wread_post => ->. reflexivity. Qed.

(** [coh_ts] reads the LOG and nothing else — the reason a read effect can be
    replayed at any state with the same log. *)
Lemma coh_ts_log s1 s2 pa n :
  wm_log s1 = wm_log s2 -> coh_ts s1 pa n = coh_ts s2 pa n.
Proof. rewrite /coh_ts => ->. reflexivity. Qed.

(** The era-initial image is untouched by every effect ... *)
Lemma weff_apply_img tid s e : wm_img (weff_apply tid s e) = wm_img s.
Proof. destruct e; [apply wread_post_img|reflexivity|reflexivity]. Qed.

Lemma weffs_img tid s es : wm_img (weffs tid s es) = wm_img s.
Proof.
  revert s. induction es as [|e es IH]; intros s; [reflexivity|].
  rewrite weffs_cons IH. apply weff_apply_img.
Qed.

(** ... every effect only RAISES the hart's views ... *)
Lemma weff_apply_ws_le tid s e : ws_le (wm_ws s) (wm_ws (weff_apply tid s e)).
Proof.
  destruct e.
  - apply wread_post_ws_le.
  - apply wwrite_post_ws_le.
  - apply barrier_post_le.
Qed.

Lemma weffs_ws_le tid s es : ws_le (wm_ws s) (wm_ws (weffs tid s es)).
Proof.
  revert s. induction es as [|e es IH]; intros s; [reflexivity|].
  rewrite weffs_cons. etrans; [apply weff_apply_ws_le|apply IH].
Qed.

(** ... and only ever APPENDS to the log. *)
Lemma weff_apply_log_app tid s e :
  exists l : list wmsg, wm_log (weff_apply tid s e) = (wm_log s ++ l)%list.
Proof.
  destruct e.
  - exists []. rewrite weff_apply_read wread_post_log app_nil_r //.
  - by eexists.
  - exists []. rewrite app_nil_r //.
Qed.

Lemma weffs_log_app tid s es :
  exists l : list wmsg, wm_log (weffs tid s es) = (wm_log s ++ l)%list.
Proof.
  revert s. induction es as [|e es IH]; intros s.
  - exists []. by rewrite app_nil_r.
  - rewrite weffs_cons.
    destruct (weff_apply_log_app tid s e) as [l1 Hl1].
    destruct (IH (weff_apply tid s e)) as [l2 Hl2].
    exists (l1 ++ l2)%list. by rewrite Hl2 Hl1 app_assoc.
Qed.

(** THE CONGRUENCE.  Two states that agree on the image, the log and the weak
    state are indistinguishable to the fold — registers and the device fabric
    are not inputs to any effect.  §5's induction needs exactly this, because
    the register and device writes an instruction performs sit BETWEEN its
    memory effects and must not disturb the fold. *)
Lemma weff_apply_congr tid s1 s2 e :
  wm_img s1 = wm_img s2 -> wm_log s1 = wm_log s2 -> wm_ws s1 = wm_ws s2 ->
  wm_img (weff_apply tid s1 e) = wm_img (weff_apply tid s2 e) /\
  wm_log (weff_apply tid s1 e) = wm_log (weff_apply tid s2 e) /\
  wm_ws (weff_apply tid s1 e) = wm_ws (weff_apply tid s2 e).
Proof.
  intros Hi Hl Hw. destruct e; simpl.
  - rewrite /wread_post. destruct (ak_coh ak); simpl.
    + by split_and!.
    + split_and!; [exact Hi|exact Hl|]. by rewrite /coh_ts Hw Hl.
  - rewrite /wwrite_post /=.
    split_and!; [exact Hi|by rewrite Hl Hw|by rewrite Hw Hl].
  - simpl. split_and!; [exact Hi|exact Hl|by rewrite Hw].
Qed.

Lemma weffs_congr tid s1 s2 es :
  wm_img s1 = wm_img s2 -> wm_log s1 = wm_log s2 -> wm_ws s1 = wm_ws s2 ->
  wm_img (weffs tid s1 es) = wm_img (weffs tid s2 es) /\
  wm_log (weffs tid s1 es) = wm_log (weffs tid s2 es) /\
  wm_ws (weffs tid s1 es) = wm_ws (weffs tid s2 es).
Proof.
  revert s1 s2. induction es as [|e es IH]; intros s1 s2 Hi Hl Hw;
    [by split_and!|].
  rewrite !weffs_cons.
  destruct (weff_apply_congr tid s1 s2 e Hi Hl Hw) as (Hi' & Hl' & Hw').
  exact (IH _ _ Hi' Hl' Hw').
Qed.

(** The form the induction applies it in: a successor described against [s2]
    is a successor described against any [s1] that agrees with it. *)
Lemma weffs_transport tid s1 s2 es (s' : wmstate) :
  wm_img s1 = wm_img s2 -> wm_log s1 = wm_log s2 -> wm_ws s1 = wm_ws s2 ->
  (wm_img s' = wm_img s2 /\ wm_log s' = wm_log (weffs tid s2 es) /\
     wm_ws s' = wm_ws (weffs tid s2 es)) ->
  wm_img s' = wm_img s1 /\ wm_log s' = wm_log (weffs tid s1 es) /\
    wm_ws s' = wm_ws (weffs tid s1 es).
Proof.
  intros Hi Hl Hw (Hi' & Hl' & Hw').
  destruct (weffs_congr tid s1 s2 es Hi Hl Hw) as (Hi2 & Hl2 & Hw2).
  split_and!; [by rewrite Hi' Hi|by rewrite Hl' Hl2|by rewrite Hw' Hw2].
Qed.

(** [exec], ARM FOR ARM, with the trace threaded.  The only arms that differ
    are the two RAM ones and [Barrier]: a DEVICE access emits nothing (device
    views are M5), and neither does anything else. *)
Fixpoint exec_eff {X} (m : M X) (s : mstate) {struct m}
    : option (X * mstate * list weff) :=
  match m with
  | Interface.Ret y => Some (y, s, [])
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * mstate * list weff) with
       | Interface.RegRead r _ => fun k =>
           exec_eff (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v => fun k => exec_eff (k tt) (set_reg s r v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 exec_eff (k (inl (w, None))) (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w =>
                 match exec_eff (k (inl (w, None))) s with
                 | Some (y, s', es) =>
                     Some (y, s',
                           WEread (classify (Interface.ReadReq.access_kind req))
                                  (Interface.ReadReq.pa req) n :: es)
                 | None => None
                 end
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => exec_eff (k (inl None)) (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match exec_eff (k (inl None))
                     (MState s.(sregs)
                        (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) s.(mdev)) with
             | Some (y, s', es) =>
                 Some (y, s',
                       WEwrite (classify (Interface.WriteReq.access_kind req))
                               (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) :: es)
             | None => None
             end
       | Interface.InstrAnnounce _   => fun k => exec_eff (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => exec_eff (k tt) s
       | Interface.Barrier b         => fun k =>
           match exec_eff (k tt) s with
           | Some (y, s', es) => Some (y, s', WEbar b :: es)
           | None => None
           end
       | Interface.CacheOp _         => fun k => exec_eff (k tt) s
       | Interface.TlbOp _           => fun k => exec_eff (k tt) s
       | Interface.TakeException _   => fun k => exec_eff (k tt) s
       | Interface.ReturnException _ => fun k => exec_eff (k tt) s
       | Interface.TranslationStart _=> fun k => exec_eff (k tt) s
       | Interface.TranslationEnd _  => fun k => exec_eff (k tt) s
       | Interface.CycleCount        => fun k => exec_eff (k tt) s
       | Interface.Message _         => fun k => exec_eff (k tt) s
       | Interface.GetCycleCount     => fun k => exec_eff (k 0%Z) s
       | _ => fun _ => None   (* Choose / GenericFail / Discard / ExtraOutcome *)
       end) k
  end.

(** The instrumentation is exactly that: the two interpreters agree on the
    value and the state, and differ only in whether the trace is recorded. *)
Lemma exec_eff_exec {X} (m : M X) :
  forall s x s' es, exec_eff m s = Some (x, s', es) -> exec m s = Some (x, s').
Proof.
  induction m as [y|T oc k IH]; intros s x s' es Hex.
  - simpl in Hex |- *. by injection Hex as <- <- <-.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hex));
      try (destruct (exec_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate];
           injection Hex as <- <- <-; exact (IH _ _ _ _ _ Hee)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (exec_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-. exact (IH _ _ _ _ _ Hee).
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex).
      * destruct (exec_eff _ _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-. exact (IH _ _ _ _ _ Hee).
Qed.

Lemma exec_exec_eff {X} (m : M X) :
  forall s x s', exec m s = Some (x, s') -> exists es, exec_eff m s = Some (x, s', es).
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hex.
  - simpl in Hex |- *. injection Hex as <- <-. by exists [].
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ Hex));
      try (destruct (IH _ _ _ _ Hex) as [es0 Hee]; rewrite Hee /=; by eexists).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (IH _ _ _ _ Hex) as [es0 Hee]. rewrite Hee /=. by eexists.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ Hex).
      * destruct (IH _ _ _ _ Hex) as [es0 Hee]. rewrite Hee /=. by eexists.
Qed.

(* ====================================================================== *)
(** ** 5. THE CONFINED-EXEC CERTIFICATE

    *** 5a. [trace_pin] — pinnedness, keyed on the TRACE.

    THE PRIMARY CONFINEMENT PREMISE.  "Every read of the trace whose access
    kind does not itself force the latest value has its footprint pinned for
    this hart."  This is exactly what the two consumers of pinnedness —
    [wstep_ok]'s read arm and [WeakBridge.wread_pinned_ts] — ask for, premise
    for premise: both take it under [ak_pins ak = false], so a SELF-PINNING
    read ([ak_coh]: fetch/walker; [ak_latest]: an AMO's read half) is exempt.
    The historical whole-window form ("[pinned_read] on ALL of [W]") is an
    over-approximation that is right for the owned-data leaves but UNPROVABLE
    for a contended AMO — the lock word is in the window (the WRITE's
    footprint is confined by it) while the acquirer's index need not cover
    its latest write.  It survives below (§5c) as the every-read-pinned
    INSTANCE of the pin theorem. *)

Definition trace_pin (s : wmstate) (es : list weff) : Prop :=
  forall (ak : akinfo) (pa : Arch.pa) (n : N),
    WEread ak pa n ∈ es -> ak_pins ak = false ->
    forall j : nat, (j < N.to_nat n)%nat -> pinned_read s (acc_addr pa j).

(** The three transports the induction needs — each is the corresponding
    [pinned_read] transport, pointwise. *)
Lemma trace_pin_mono (s s' : wmstate) (es : list weff) :
  wm_log s' = wm_log s -> ws_le (wm_ws s) (wm_ws s') ->
  trace_pin s es -> trace_pin s' es.
Proof.
  intros Hl Hle Hp ak pa n Hin Hnp j Hj.
  exact (pinned_read_mono s s' _ Hl Hle (Hp ak pa n Hin Hnp j Hj)).
Qed.

Lemma trace_pin_write (tid : option nat) (s : wmstate) (ak0 : akinfo)
    (pa0 : Arch.pa) (n0 : N) (v : bv (8 * n0)) (es : list weff) :
  trace_pin s es -> trace_pin (wwrite_post tid s ak0 pa0 n0 v) es.
Proof.
  intros Hp ak pa n Hin Hnp j Hj.
  exact (pinned_read_write tid s ak0 pa0 n0 v _ (Hp ak pa n Hin Hnp j Hj)).
Qed.

Lemma trace_pin_tail (s : wmstate) (e : weff) (es : list weff) :
  trace_pin s (e :: es) -> trace_pin s es.
Proof.
  intros Hp ak pa n Hin. apply (Hp ak pa n). apply elem_of_cons. by right.
Qed.

(** *** 5b. THE CONFINED-RUN INDUCTION, under [trace_pin] — THE theorem.

    Read the premises as: the window [W] does not contain the null address;
    every non-self-pinning read of the trace is pinned for this hart; the
    confined map [mm] lives in the window and agrees with the real memory;
    the (instrumented) SC interpreter RUNS TO COMPLETION on it; and it never
    writes outside the window.  Conclusion: the whole step's peel, plus the
    weak successor's log and views as the fold of §4's trace.

    The induction is [WeakBridge]'s own ([exec_of_wexec_pinned]'s shape) with
    the confined map threaded alongside the weak state; the three arms that do
    any work are:
      - RAM read: [read_bytes mm] returned [Some], so the footprint is inside
        [dom mm ⊆ W], which gives [acc_wf]; pinnedness — needed only under
        [ak_pins = false] — comes off the trace's HEAD element; and the
        canonical weak read returns the same word ([wread_bytes_read_bytes]
        plus [read_bytes_mono]), so the two runs stay in lockstep;
      - RAM write: the footprint is inside the FINAL memory's domain
        ([exec_dom_mono]), hence in [W], which gives [acc_wf];
      - [Choose]: [exec] is stuck there, so the [False] arm — i.e. the whole
        [wexec_covers] side of the merge — is discharged by the [exec] fact
        itself.

    The non-memory arms are where [weffs_congr] earns its keep: they change
    the state (a register, a device) in a way the fold cannot see, so the
    IH's answer transports back verbatim. *)

Lemma wstep_eff_confined_pin (tid : option nat) {X} (m : M X) :
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa)
         (x : X) (t' : mstate) (es : list weff),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    trace_pin s es ->
    dom mm ⊆ W ->
    mm ⊆ wflat (wm_img s) (wm_log s) ->
    dom (mem t') ⊆ W ->
    exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t', es) ->
    wstep_ok tid m s /\
    (forall χ (y : X) (s' : wmstate) (χ' : list (list nat)),
       wexec tid m χ s = Some (y, s', χ') ->
       wm_img s' = wm_img s /\
       wm_log s' = wm_log (weffs tid s es) /\
       wm_ws s' = wm_ws (weffs tid s es)).
Proof.
  induction m as [y|T oc k IH];
    intros s mm W x t' es Hwf HW0 Hpes Hdom Hsub Hdom' Hex.
  - simpl in Hex. injection Hex as <- <- <-.
    split; [exact I|]. intros χ y0 s' χ' Hw.
    simpl in Hw. injection Hw as <- <- <-. by split_and!.
  - pose proof (exec_eff_exec _ _ _ _ _ Hex) as Hexc.
    destruct oc; simpl in Hex, Hexc |- *; try discriminate;
      try (exact (IH _ s mm W x t' es Hwf HW0 Hpes Hdom Hsub Hdom' Hex)).
    + (* RegWrite: the fold cannot see a register *)
      assert (Hp2 : trace_pin (wset_reg s reg regval) es)
        by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
      destruct (IH tt (wset_reg s reg regval) mm W x t' es Hwf HW0 Hp2
                  Hdom Hsub Hdom' Hex) as [Hok Hag].
      split; [exact Hok|]. intros χ y s' χ' Hw.
      apply (weffs_transport tid s (wset_reg s reg regval) es s');
        [reflexivity|reflexivity|reflexivity|exact (Hag χ y s' χ' Hw)].
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * (* device: no effect emitted *)
        destruct (dev_read _ _ _) as [[w0 d0]|] eqn:Hdr; [|discriminate].
        assert (Hp2 : trace_pin (wset_dev s d0) es)
          by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
        destruct (IH _ (wset_dev s d0) mm W x t' es Hwf HW0 Hp2
                    Hdom Hsub Hdom' Hex) as [Hok Hag].
        split.
        -- intros w d' Hdr'. simplify_eq. exact Hok.
        -- intros χ y s' χ' Hw.
           apply (weffs_transport tid s (wset_dev s d0) es s');
             [reflexivity|reflexivity|reflexivity|exact (Hag χ y s' χ' Hw)].
      * destruct (read_bytes mm _ _) as [w0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff (k (inl (w0, None))) (MState (wm_regs s) mm (wm_dev s)))
          as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        (* the footprint is inside the window *)
        assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                  pa_add (Interface.ReadReq.pa t) j ∈ W)
          by (intros j Hj; apply Hdom, (read_bytes_dom mm _ _ w0 Hrb j Hj)).
        assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
          by (apply (acc_wf_window W); [exact HW0|exact Hin]).
        (* THE PIN REFINEMENT: pinnedness of THIS read's footprint, exactly
           under [ak_pins = false] — off the trace's head element *)
        assert (Hpinf : ak_pins (classify (Interface.ReadReq.access_kind t))
                          = false ->
                  forall j : nat, (j < N.to_nat n)%nat ->
                    pinned_read s (acc_addr (Interface.ReadReq.pa t) j)).
        { intros Hnp j Hj.
          apply (Hpes (classify (Interface.ReadReq.access_kind t))
                   (Interface.ReadReq.pa t) n);
            [apply elem_of_cons; by left|exact Hnp|exact Hj]. }
        (* the canonical weak read IS the confined one *)
        assert (Hwrb : wread_bytes s (classify (Interface.ReadReq.access_kind t))
                         (Interface.ReadReq.pa t) n
                         (coh_ts s (Interface.ReadReq.pa t) n) = Some w0).
        { rewrite (wread_bytes_read_bytes s
                     (classify (Interface.ReadReq.access_kind t))
                     (Interface.ReadReq.pa t) n Hwf Hacc).
          exact (read_bytes_mono mm _ _ _ w0 Hsub Hrb). }
        assert (Hp2 : trace_pin
                        (wread_post s
                           (classify (Interface.ReadReq.access_kind t))
                           (Interface.ReadReq.pa t)
                           (coh_ts s (Interface.ReadReq.pa t) n)) es0).
        { apply (trace_pin_mono s);
            [by rewrite wread_post_log|apply wread_post_ws_le
            |exact (trace_pin_tail s _ es0 Hpes)]. }
        assert (Hsub2 : mm ⊆
                  wflat (wm_img (wread_post s
                                   (classify (Interface.ReadReq.access_kind t))
                                   (Interface.ReadReq.pa t)
                                   (coh_ts s (Interface.ReadReq.pa t) n)))
                        (wm_log (wread_post s
                                   (classify (Interface.ReadReq.access_kind t))
                                   (Interface.ReadReq.pa t)
                                   (coh_ts s (Interface.ReadReq.pa t) n))))
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
        destruct (IH _ _ mm W x0 t0 es0 (wlog_wf_read_post _ _ _ _ Hwf) HW0 Hp2
                    Hdom Hsub2 Hdom' Hee2) as [Hok Hag].
        split.
        -- split_and!.
           ++ exact Hacc.
           ++ exact Hpinf.
           ++ intros w Hw. rewrite Hwrb in Hw. injection Hw as <-. exact Hok.
        -- intros χ y s' χ' Hw.
           destruct (ak_coh (classify (Interface.ReadReq.access_kind t))) eqn:Hcoh.
           ++ (* coherent read: no oracle entry consumed *)
              rewrite Hwrb in Hw.
              destruct (Hag χ y s' χ' Hw) as (Hi & Hl & Hws).
              split_and!; [by rewrite Hi wread_post_img|exact Hl|exact Hws].
           ++ (* weak read: the oracle's timestamps ARE the canonical ones *)
              destruct χ as [|ts χ0]; [discriminate|].
              destruct (wread_bytes s _ _ n ts) as [w|] eqn:Hrb2; [|discriminate].
              assert (Hts : ts = coh_ts s (Interface.ReadReq.pa t) n).
              { apply (wread_pinned_ts s
                         (classify (Interface.ReadReq.access_kind t))
                         (Interface.ReadReq.pa t) n ts w);
                  [exact Hpinf
                  |exact (wread_bytes_spec _ _ _ _ _ _ Hrb2)]. }
              rewrite Hts in Hrb2. rewrite Hwrb in Hrb2. injection Hrb2 as <-.
              rewrite Hts in Hw.
              destruct (Hag χ0 y s' χ' Hw) as (Hi & Hl & Hws).
              split_and!; [by rewrite Hi wread_post_img|exact Hl|exact Hws].
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d0|] eqn:Hdw; [|discriminate].
        assert (Hp2 : trace_pin (wset_dev s d0) es)
          by (apply (trace_pin_mono s); [reflexivity|reflexivity|exact Hpes]).
        destruct (IH _ (wset_dev s d0) mm W x t' es Hwf HW0 Hp2
                    Hdom Hsub Hdom' Hex) as [Hok Hag].
        split.
        -- intros d' Hdw'. simplify_eq. exact Hok.
        -- intros χ y s' χ' Hw.
           apply (weffs_transport tid s (wset_dev s d0) es s');
             [reflexivity|reflexivity|reflexivity|exact (Hag χ y s' χ' Hw)].
      * destruct (exec_eff (k (inl None))
                    (MState (wm_regs s)
                       (write_bytes mm (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) (wm_dev s)))
          as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        (* the written footprint is inside the final memory, hence in [W] *)
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
        assert (Hsub2 : write_bytes mm (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)
                        ⊆ wflat (wm_img (wwrite_post tid s
                                   (classify (Interface.WriteReq.access_kind t))
                                   (Interface.WriteReq.pa t) n
                                   (Interface.WriteReq.value t)))
                                (wm_log (wwrite_post tid s
                                   (classify (Interface.WriteReq.access_kind t))
                                   (Interface.WriteReq.pa t) n
                                   (Interface.WriteReq.value t)))).
        { rewrite (wflat_write tid s (classify (Interface.WriteReq.access_kind t))
                     (Interface.WriteReq.pa t) n (Interface.WriteReq.value t)).
          by apply write_bytes_mono. }
        destruct (IH _ _ _ W x0 t0 es0
                    (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) HW0 Hp2
                    Hdom2 Hsub2 Hdom' Hee) as [Hok Hag].
        split.
        -- split; [exact Hacc|exact Hok].
        -- intros χ y s' χ' Hw.
           destruct (Hag χ y s' χ' Hw) as (Hi & Hl & Hws).
           by split_and!.
    + (* Barrier *)
      destruct (exec_eff (k tt) (MState (wm_regs s) mm (wm_dev s)))
        as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      assert (Hp2 : trace_pin (wset_ws s (barrier_post (wm_ws s) b)) es0).
      { apply (trace_pin_mono s);
          [reflexivity|apply barrier_post_le
          |exact (trace_pin_tail s _ es0 Hpes)]. }
      destruct (IH tt (wset_ws s (barrier_post (wm_ws s) b)) mm W x0 t0 es0
                  Hwf HW0 Hp2 Hdom Hsub Hdom' Hee) as [Hok Hag].
      split; [exact Hok|]. intros χ y s' χ' Hw.
      destruct (Hag χ y s' χ' Hw) as (Hi & Hl & Hws). by split_and!.
Qed.

(** *** 5c. The whole-window form, as the EVERY-READ-PINNED instance.

    Whole-window pinnedness implies [trace_pin]: every read the confined run
    records has its footprint inside the final memory's domain (reads look up
    the current map, which only grows — the read twin of [exec_dom_mono]),
    hence inside [W], where everything is pinned. *)

Lemma exec_eff_reads_dom {X} (m : M X) :
  forall (s : mstate) (x : X) (s' : mstate) (es : list weff),
    exec_eff m s = Some (x, s', es) ->
    forall (ak : akinfo) (pa : Arch.pa) (n : N),
      WEread ak pa n ∈ es ->
      forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ dom (mem s').
Proof.
  induction m as [y|T oc k IH]; intros s x s' es Hex ak pa n Hin j Hj.
  - simpl in Hex. injection Hex as <- <- <-. by apply elem_of_nil in Hin.
  - destruct oc; simpl in Hex; try discriminate;
      try (exact (IH _ _ _ _ _ Hex ak pa n Hin j Hj)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex ak pa n Hin j Hj).
      * destruct (read_bytes _ _ _) as [w0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff _ _) as [[[x1 u1] es1]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        apply elem_of_cons in Hin as [He|Hin].
        -- injection He as -> -> ->.
           apply (exec_dom_mono _ _ _ _ (exec_eff_exec _ _ _ _ _ Hee)).
           exact (read_bytes_dom _ _ _ _ Hrb j Hj).
        -- exact (IH _ _ _ _ _ Hee ak pa n Hin j Hj).
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex ak pa n Hin j Hj).
      * destruct (exec_eff _ _) as [[[x1 u1] es1]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        apply elem_of_cons in Hin as [He|Hin]; [discriminate He|].
        exact (IH _ _ _ _ _ Hee ak pa n Hin j Hj).
    + (* Barrier *)
      destruct (exec_eff _ _) as [[[x1 u1] es1]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      apply elem_of_cons in Hin as [He|Hin]; [discriminate He|].
      exact (IH _ _ _ _ _ Hee ak pa n Hin j Hj).
Qed.

Lemma confined_trace_pin {X} (m : M X) (s : wmstate)
    (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa) (x : X) (t' : mstate)
    (es : list weff) :
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read s (pa_z a)) ->
  dom (mem t') ⊆ W ->
  exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t', es) ->
  trace_pin s es.
Proof.
  intros HW0 HWp Hdom' Hex ak pa n Hin _ j Hj.
  assert (Hin' : forall j0 : nat, (j0 < N.to_nat n)%nat -> pa_add pa j0 ∈ W)
    by (intros j0 Hj0; apply Hdom',
          (exec_eff_reads_dom m _ _ _ _ Hex ak pa n Hin j0 Hj0)).
  assert (Hacc : acc_wf pa n)
    by (apply (acc_wf_window W); [exact HW0|exact Hin']).
  rewrite -(acc_wf_byte pa n j Hacc Hj). exact (HWp _ (Hin' j Hj)).
Qed.

Lemma wstep_eff_confined (tid : option nat) {X} (m : M X) :
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa)
         (x : X) (t' : mstate) (es : list weff),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    (forall a, a ∈ W -> pinned_read s (pa_z a)) ->
    dom mm ⊆ W ->
    mm ⊆ wflat (wm_img s) (wm_log s) ->
    dom (mem t') ⊆ W ->
    exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t', es) ->
    wstep_ok tid m s /\
    (forall χ (y : X) (s' : wmstate) (χ' : list (list nat)),
       wexec tid m χ s = Some (y, s', χ') ->
       wm_img s' = wm_img s /\
       wm_log s' = wm_log (weffs tid s es) /\
       wm_ws s' = wm_ws (weffs tid s es)).
Proof.
  intros s mm W x t' es Hwf HW0 HWp Hdom Hsub Hdom' Hex.
  exact (wstep_eff_confined_pin tid m s mm W x t' es Hwf HW0
           (confined_trace_pin m s mm W x t' es HW0 HWp Hdom' Hex)
           Hdom Hsub Hdom' Hex).
Qed.

(** The peel alone, at M3b's statement — everything downstream still sees
    exactly this. *)
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
  intros s mm W x t' Hwf HW0 HWp Hdom Hsub Hdom' Hex.
  destruct (exec_exec_eff _ _ _ _ Hex) as [es Hee].
  exact (proj1 (wstep_eff_confined tid m s mm W x t' es
                  Hwf HW0 HWp Hdom Hsub Hdom' Hee)).
Qed.

(* ====================================================================== *)
(** ** 6. Packaged as the certificate

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

Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr.

(** THE CERTIFICATE, wstep_ok half discharged for EVERY instruction at once.
    [Q] — the weak-memory effect — is the only thing left to supply, and only
    the sync instructions have one worth stating ([WeakInstr.wQ_amo_aq],
    [wQ_fence], [wQ_store]); a plain load or an ALU instruction takes
    [wQ_none] and then the certificate is UNCONDITIONAL. *)
Lemma wstep_cert_conf (cid : nat) (pc : SailStdpp.Values.mword 64)
    (Q : wmstate -> wmstate -> Prop) :
  (forall (s : wmstate) (tick : bool),
     register_lookup PC (wm_regs s) = pc -> wP_conf s ->
     forall χ s' χ', wexec (Some cid) (riscv_step tick) χ s = Some (tt, s', χ') ->
       Q s s') ->
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
    (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
  (forall s, P s -> wP_conf s) ->
  (forall (s : wmstate) (tick : bool),
     register_lookup PC (wm_regs s) = pc -> P s ->
     forall χ s' χ', wexec (Some cid) (riscv_step tick) χ s = Some (tt, s', χ') ->
       Q s s') ->
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
         half (owned).  THE EXACT ACCOUNTING IS TRACE-KEYED (§5a): pinnedness
         is needed precisely where [ak_pins ak = false]; a self-pinning read
         — [ak_coh] (fetch/walker) or [ak_latest] (an AMO's read half) — is
         exempt.  This whole-window form demands it of ALL of [W], which is
         right for the owned-data leaves but UNPROVABLE for a contended AMO
         (the acquirer's index need not cover the lock word's latest write):
         such a leaf uses [wP_eff_pin] (§7) instead.  Either way an AMO's
         data word must still be LISTED in [W], since a WRITE's footprint is
         confined by the window too;
     (d) [exec (riscv_step tick) (MState (wm_regs σ) (wmem_restrict σ W)
         (wm_dev σ)) = Some (tt, t')] with [dom (mem t') ⊆ W] — the leaf's own
         SC library lemma, instantiated at a SECOND state whose memory is the
         restriction.  Its register/config premises are literally the same
         terms ([wm_regs] is shared); its memory premises are discharged from
         the same [wpt4_flat] / [wkernel_text_flat] facts through
         [wmem_restrict_lookup].

   No model walking appears anywhere in that list, and nothing in it is
   specific to the instruction beyond naming its data address. *)

(* ====================================================================== *)
(** ** 7. A CERTIFICATE WHOSE [Q] COMES FROM THE TRACE

    [wstep_conf] (§6) asks for an [exec] fact; [wstep_conf_eff_pin] asks for
    the INSTRUMENTED one, at a FIXED trace [es].  That is the whole
    difference, and it costs the leaf nothing: the same SC library lemma, run
    through [exec_eff] instead of [exec], names the same window and the same
    final memory — it additionally pins the (two- or three-element) list of
    memory effects the instruction performs, which is exactly the data [Q] is
    about.

    THE PRIMARY FORM IS THE PIN ONE: its pinnedness premise is §5a's
    trace-keyed [trace_pin], so it serves the invariant-form AMO leaf as well
    as the owned-data leaves.  The historical whole-window [wP_eff] survives
    below as the every-read-pinned instance ([wP_eff_pin_of_eff]), and its
    certificate rule [wstep_cert_eff] is unchanged in statement — both reduce
    a certificate to a statement about the concrete effect list: no [wexec],
    no oracle, no monad. *)

Definition wstep_conf_eff_pin (tid : option nat) (es : list weff)
    (s : wmstate) : Prop :=
  exists W : gset Arch.pa,
    (forall a, a ∈ W -> pa_z a <> 0) /\
    trace_pin s es /\
    (forall tick : bool, exists t' : mstate,
       exec_eff (riscv_step tick)
         (MState (wm_regs s) (wmem_restrict s W) (wm_dev s)) = Some (tt, t', es) /\
       dom (mem t') ⊆ W).

Definition wP_eff_pin (tid : option nat) (es : list weff) : wmstate -> Prop :=
  fun s => wlog_wf (wm_log s) /\ wstep_conf_eff_pin tid es s.

(** The pin obligation, as an [apply]-able rule ([WeakEffSkel.wP_eff_of_window]'s
    twin). *)
Lemma wP_eff_pin_of_window (cid : nat) (es : list weff) (σ : wmstate)
    (W : gset Arch.pa) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  trace_pin σ es ->
  (forall tick : bool, exists t' : mstate,
     exec_eff (riscv_step tick)
       (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)) = Some (tt, t', es) /\
     dom (mem t') ⊆ W) ->
  wP_eff_pin (Some cid) es σ.
Proof.
  intros Hwf HW0 HWp Hrun. split; [exact Hwf|].
  exists W. split_and!; [exact HW0|exact HWp|exact Hrun].
Qed.

Lemma wstep_cert_eff_pin (cid : nat) (pc : SailStdpp.Values.mword 64)
    (es : list weff) (Q : wmstate -> wmstate -> Prop) :
  (forall s s' : wmstate,
     wm_img s' = wm_img s ->
     wm_log s' = wm_log (weffs (Some cid) s es) ->
     wm_ws s' = wm_ws (weffs (Some cid) s es) ->
     Q s s') ->
  wstep_cert cid pc (wP_eff_pin (Some cid) es) Q.
Proof.
  intros HQ s tick Hpc Hacc Htext HP.
  pose proof HP as (Hwf & W & HW0 & HWp & Hex).
  destruct (Hex tick) as (t' & Ht' & Hdom').
  destruct (wstep_eff_confined_pin (Some cid) (riscv_step tick) s
              (wmem_restrict s W) W tt t' es Hwf HW0 HWp
              (wmem_restrict_dom s W) (wmem_restrict_sub s W) Hdom' Ht')
    as [Hok Hag].
  split; [exact Hok|].
  intros χ s' χ' Hw. destruct (Hag χ tt s' χ' Hw) as (Hi & Hl & Hws).
  exact (HQ s s' Hi Hl Hws).
Qed.

(** THE WHOLE-WINDOW FORM — what every owned-data leaf produces. *)

Definition wstep_conf_eff (tid : option nat) (es : list weff) (s : wmstate)
    : Prop :=
  exists W : gset Arch.pa,
    (forall a, a ∈ W -> pa_z a <> 0) /\
    (forall a, a ∈ W -> pinned_read s (pa_z a)) /\
    (forall tick : bool, exists t' : mstate,
       exec_eff (riscv_step tick)
         (MState (wm_regs s) (wmem_restrict s W) (wm_dev s)) = Some (tt, t', es) /\
       dom (mem t') ⊆ W).

Definition wP_eff (tid : option nat) (es : list weff) : wmstate -> Prop :=
  fun s => wlog_wf (wm_log s) /\ wstep_conf_eff tid es s.

(** The instrumented witness is a witness: everything §6 proves off [wP_conf]
    is available under [wP_eff] too. *)
Lemma wP_eff_conf tid es s : wP_eff tid es s -> wP_conf s.
Proof.
  intros (Hwf & W & HW0 & HWp & Hex). split; [exact Hwf|].
  exists W. split_and!; [exact HW0|exact HWp|].
  intros tick. destruct (Hex tick) as (t' & Ht' & Hdom').
  exists t'. split; [exact (exec_eff_exec _ _ _ _ _ Ht')|exact Hdom'].
Qed.

(** ... and it is the every-read-pinned INSTANCE of the pin form (§5c's
    conversion, off any one tick's run). *)
Lemma wP_eff_pin_of_eff tid es s : wP_eff tid es s -> wP_eff_pin tid es s.
Proof.
  intros (Hwf & W & HW0 & HWp & Hex). split; [exact Hwf|].
  exists W. split_and!; [exact HW0| |exact Hex].
  destruct (Hex false) as (t' & Ht' & Hdom').
  exact (confined_trace_pin _ s _ W tt t' es HW0 HWp Hdom' Ht').
Qed.

Lemma wstep_cert_eff (cid : nat) (pc : SailStdpp.Values.mword 64)
    (es : list weff) (Q : wmstate -> wmstate -> Prop) :
  (forall s s' : wmstate,
     wm_img s' = wm_img s ->
     wm_log s' = wm_log (weffs (Some cid) s es) ->
     wm_ws s' = wm_ws (weffs (Some cid) s es) ->
     Q s s') ->
  wstep_cert cid pc (wP_eff (Some cid) es) Q.
Proof.
  intros HQ s tick Hpc Hacc Htext HP.
  pose proof HP as (Hwf & W & HW0 & HWp & Hex).
  destruct (Hex tick) as (t' & Ht' & Hdom').
  destruct (wstep_eff_confined (Some cid) (riscv_step tick) s
              (wmem_restrict s W) W tt t' es Hwf HW0 HWp
              (wmem_restrict_dom s W) (wmem_restrict_sub s W) Hdom' Ht')
    as [Hok Hag].
  split; [exact Hok|].
  intros χ s' χ' Hw. destruct (Hag χ tt s' χ' Hw) as (Hi & Hl & Hws).
  exact (HQ s s' Hi Hl Hws).
Qed.

(* ====================================================================== *)
(** ** 8. THE FOUR INSTRUCTION CERTIFICATES

    With §7 each of these is pure view arithmetic over a short effect list.
    EVERY instruction's trace begins with the FETCH read: rv64d emits
    [Read_plain] for instruction fetch (WeakInterp §3's table), so the fetch
    is NOT [ak_coh] and it DOES raise views — which is why the text window has
    to be pinned, and why the fetch's effect must be carried along here rather
    than dropped.  Nothing below constrains its kind, address or width: the
    fetch only ever RAISES the views a later effect starts from, and all four
    [Q]s are monotone in exactly that direction. *)

(** *** 8a. The view arithmetic, in [mword]-free lemmas *)

Lemma wm_ws_wset_ws s ws : wm_ws (wset_ws s ws) = ws.
Proof. reflexivity. Qed.

(** A fence is monotone in the state it fences: it only ever takes maxima of
    fields that grew. *)
Lemma fence_post_mono ws1 ws2 pr pw sr sw :
  ws_le ws1 ws2 -> ws_le (fence_post ws1 pr pw sr sw) (fence_post ws2 pr pw sr sw).
Proof.
  intros (Hc & Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hvcap).
  rewrite /ws_le /fence_post /=. split_and!.
  - intros a. exact (Hc a).
  - exact Hro.
  - exact Hwo.
  - destruct sr; destruct pr; destruct pw; lia.
  - destruct sw; destruct pr; destruct pw; lia.
  - exact Hrel.
  - exact Hpub.
  - exact Hvcap.
Qed.

Lemma barrier_post_mono ws1 ws2 b :
  ws_le ws1 ws2 -> ws_le (barrier_post ws1 b) (barrier_post ws2 b).
Proof.
  intros Hle. destruct b; rewrite /barrier_post;
    first [ exact Hle
          | by apply fence_post_mono, fence_post_mono
          | by apply fence_post_mono ].
Qed.

(** THE PER-BYTE GAIN OF A MULTI-BYTE LOAD.  Whatever a single [load_post_at]
    delivers ([WeakFence.amo_acq_gain] for an acquire's scalar floor,
    [WeakFence.load_byte_gain] for a plain load's byte floor), the whole fold
    delivers at every byte: the byte's own step delivers it, and the remaining
    steps only raise views. *)
Lemma load_post_fold_gain (V : Z -> nat -> view) (aq : bool) (vpre : nat) :
  (forall ws a t, V a t ⊑ ws_view (load_post_at ws aq vpre a t)) ->
  forall (ats : list (Z * nat)) (ws : wstate) (j : nat) (at_ : Z * nat),
    ats !! j = Some at_ ->
    V at_.1 at_.2
    ⊑ ws_view (foldl (fun w a => load_post_at w aq vpre a.1 a.2) ws ats).
Proof.
  intros Hgain ats. induction ats as [|a0 l IH]; intros ws j at_ Hj.
  - by rewrite lookup_nil in Hj.
  - destruct j as [|j]; simpl in Hj.
    + injection Hj as <-. simpl.
      etrans; [apply Hgain|]. apply ws_view_mono, load_post_fold_le.
    + exact (IH _ j at_ Hj).
Qed.

Lemma load_post_run_gain (V : Z -> nat -> view) (ws : wstate) (aq : bool)
    (base : Z) (ts : list nat) (j : nat) :
  (forall w a t, V a t ⊑ ws_view (load_post_at w aq (load_vpre ws aq) a t)) ->
  (j < length ts)%nat ->
  V (base + Z.of_nat j) (ts !!! j) ⊑ ws_view (load_post_run ws aq base ts).
Proof.
  intros Hgain Hj. rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_gain V aq (load_vpre ws aq) Hgain _ ws j
           (base + Z.of_nat j, ts !!! j)).
  apply lookup_zip_with_Some. exists j, (ts !!! j). split_and!.
  - reflexivity.
  - rewrite lookup_seq_lt; first [exact Hj|reflexivity].
  - by apply list_lookup_lookup_total_lt.
Qed.

(** *** 8b. [fence] *)

Lemma wcert_fence (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (b : barrier_kind) :
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEbar b]) (wQ_fence b).
Proof.
  apply wstep_cert_eff. intros s s' Hi Hl Hws.
  rewrite /wQ_fence /wV_fence Hws weffs_cons2 weff_apply_read weff_apply_bar
          wm_ws_wset_ws.
  split; [apply barrier_post_mono, wread_post_ws_le|].
  intros Ha. by apply barrier_post_relp.
Qed.

(** *** 8c. The 4-byte STORE *)

Lemma wcert_store (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEwrite akw ea 4 v])
    (wQ_store (Some cid) ea v).
Proof.
  apply wstep_cert_eff. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  rewrite weffs_cons2 weff_apply_read weff_apply_write in Hl Hws.
  rewrite wwrite_post_log wread_post_log in Hl.
  rewrite wwrite_post_ws wread_post_log in Hws.
  rewrite /wQ_store /wV_store.
  split_and!; [exact Hi| |exact Hle|].
  { eexists. split; [exact Hl|]. intros Hr. apply wm_class_of_relp.
    by rewrite wread_post_relp. }
  intros j Hj. rewrite Hws flr_ws_view /acc_addr.
  etrans; [|apply Nat.le_max_r].
  apply (store_post_run_coh (wm_ws (wread_post s akf pf (coh_ts s pf nf)))
           (ak_sync akw) (pa_z ea) (N.to_nat 4) (S (length (wm_log s))) j).
  exact Hj.
Qed.

(** *** 8d. [amoswap.w.aq] — the store effect PLUS the acquire's index gain *)

Lemma wcert_amo_aq (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true -> ak_latest akw = true ->
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEread aka ea 4; WEwrite akw ea 4 v])
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync Hlat. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  rewrite weffs_cons3 !weff_apply_read weff_apply_write in Hl Hws.
  (* the fetch left the log alone, so the AMO's read is at [coh_ts s] *)
  rewrite (coh_ts_log (wread_post s akf pf (coh_ts s pf nf)) s ea 4
             (wread_post_log s akf pf (coh_ts s pf nf))) in Hl Hws.
  rewrite wwrite_post_log !wread_post_log in Hl.
  rewrite wwrite_post_ws !wread_post_log in Hws.
  rewrite (wread_post_ws_weak (wread_post s akf pf (coh_ts s pf nf)) aka ea
             (coh_ts s ea 4) Hcoh) Hsync in Hws.
  assert (Hexcl : wm_class_of akw
            (wm_ws (wread_post (wread_post s akf pf (coh_ts s pf nf)) aka ea
                      (coh_ts s ea 4))) = WCexcl)
    by (unfold wm_class_of; by rewrite Hlat).
  rewrite /wQ_amo_aq. split_and!; [| |by rewrite Hl Hexcl].
  - rewrite /wQ_store /wV_store.
    split_and!; [exact Hi| |exact Hle|].
    { eexists. split; [exact Hl|]. intros Hr. apply wm_class_of_relp.
      by rewrite !wread_post_relp. }
    intros j Hj. rewrite Hws flr_ws_view /acc_addr.
    etrans; [|apply Nat.le_max_r].
    apply (store_post_run_coh
             (load_post_run (wm_ws (wread_post s akf pf (coh_ts s pf nf)))
                true (pa_z ea) (coh_ts s ea 4))
             (ak_sync akw) (pa_z ea) (N.to_nat 4) (S (length (wm_log s))) j).
    exact Hj.
  - rewrite /wV_amo_aq. intros j Hj. rewrite Hws.
    rewrite -(coh_ts_lookup s ea 4 j Hj).
    etrans; [|apply ws_view_mono, store_post_run_le].
    apply (load_post_run_gain (fun _ t => view_scl t)
             (wm_ws (wread_post s akf pf (coh_ts s pf nf))) true (pa_z ea)
             (coh_ts s ea 4) j).
    + intros w a t. apply amo_acq_gain.
    + rewrite coh_ts_length. exact Hj.
Qed.

(** *** 8e. The 4-byte plain LOAD *)

Lemma wcert_load (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEread akl ea 4]) (wQ_load ea).
Proof.
  intros Hcoh. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  rewrite weffs_cons2 !weff_apply_read in Hl Hws.
  rewrite (coh_ts_log (wread_post s akf pf (coh_ts s pf nf)) s ea 4
             (wread_post_log s akf pf (coh_ts s pf nf))) in Hl Hws.
  rewrite !wread_post_log in Hl.
  rewrite (wread_post_ws_weak (wread_post s akf pf (coh_ts s pf nf)) akl ea
             (coh_ts s ea 4) Hcoh) in Hws.
  rewrite /wQ_load /wV_load. split_and!; [exact Hi|exact Hl|].
  intros j Hj. rewrite Hws.
  rewrite -(coh_ts_lookup s ea 4 j Hj) /acc_addr.
  apply (load_post_run_gain (fun a t => view_byte a t)
           (wm_ws (wread_post s akf pf (coh_ts s pf nf))) (ak_sync akl)
           (pa_z ea) (coh_ts s ea 4) j).
  - intros w a t. apply load_byte_gain.
  - rewrite coh_ts_length. exact Hj.
Qed.

(** *** 8f. [amoswap.w.aq], PIN FORM — the certificate the invariant-form
    lock leaf consumes.  §8d's view arithmetic, verbatim, over
    [wstep_cert_eff_pin]: the arithmetic never used the [P], and the
    trace-keyed premise is the only [P] a contended acquirer can discharge
    (the fetch is the sole non-self-pinning read of the trace).
    Width-4-only, like §8d: this IS the width-4 instruction (generalize with
    the first [amoswap.d] leaf, per the notes). *)

Lemma wcert_amo_aq_pin (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true -> ak_latest akw = true ->
  wstep_cert cid pc
    (wP_eff_pin (Some cid) [WEread akf pf nf; WEread aka ea 4; WEwrite akw ea 4 v])
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync Hlat. apply wstep_cert_eff_pin. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  rewrite weffs_cons3 !weff_apply_read weff_apply_write in Hl Hws.
  (* the fetch left the log alone, so the AMO's read is at [coh_ts s] *)
  rewrite (coh_ts_log (wread_post s akf pf (coh_ts s pf nf)) s ea 4
             (wread_post_log s akf pf (coh_ts s pf nf))) in Hl Hws.
  rewrite wwrite_post_log !wread_post_log in Hl.
  rewrite wwrite_post_ws !wread_post_log in Hws.
  rewrite (wread_post_ws_weak (wread_post s akf pf (coh_ts s pf nf)) aka ea
             (coh_ts s ea 4) Hcoh) Hsync in Hws.
  assert (Hexcl : wm_class_of akw
            (wm_ws (wread_post (wread_post s akf pf (coh_ts s pf nf)) aka ea
                      (coh_ts s ea 4))) = WCexcl)
    by (unfold wm_class_of; by rewrite Hlat).
  rewrite /wQ_amo_aq /wQ_amo_aq_w. split_and!; [| |by rewrite Hl Hexcl].
  - rewrite /wQ_store_w /wV_store_w.
    split_and!; [exact Hi| |exact Hle|].
    { eexists. split; [exact Hl|]. intros Hr. apply wm_class_of_relp.
      by rewrite !wread_post_relp. }
    intros j Hj. rewrite Hws flr_ws_view /acc_addr.
    etrans; [|apply Nat.le_max_r].
    apply (store_post_run_coh
             (load_post_run (wm_ws (wread_post s akf pf (coh_ts s pf nf)))
                true (pa_z ea) (coh_ts s ea 4))
             (ak_sync akw) (pa_z ea) (N.to_nat 4) (S (length (wm_log s))) j).
    exact Hj.
  - rewrite /wV_amo_aq_w. intros j Hj. rewrite Hws.
    rewrite -(coh_ts_lookup s ea 4 j Hj).
    etrans; [|apply ws_view_mono, store_post_run_le].
    apply (load_post_run_gain (fun _ t => view_scl t)
             (wm_ws (wread_post s akf pf (coh_ts s pf nf))) true (pa_z ea)
             (coh_ts s ea 4) j).
    + intros w a t. apply amo_acq_gain.
    + rewrite coh_ts_length. exact Hj.
Qed.

(* ====================================================================== *)
(** ** 5b. THE COHERENCE FOOTPRINT of a trace (φ-upgrade, deliverable C)

    THE MACHINE-LEVEL FACT the violation-freedom conjunct needs and that the
    tree did not have: a step raises a hart's [WeakMem.coh] ONLY at the bytes
    its effect trace names.  Everything else about φ's preservation is either
    pure ([WeakViolation] §2) or a reading of the mover's own C/D/S fragment
    ([WeakViolation] §3); this is the one piece that has to come from the
    interpreter, and the effect trace is where it can be said, because
    [WeakCert.wstep_cert_eff] pins the successor's [wstate] to
    [WeakCert.weffs] on the nose.

    WHY IT IS INDISPENSABLE.  [WeakInstr.wstep_post] carries only
    [WeakMem.ws_le] about the successor's views, and monotonicity alone does
    not bound the RISE at an untouched byte — while [WeakMem.load_post_at]
    absorbs the whole pre-view [vpre] into [coh] at every byte it reads, so
    a floor really can jump arbitrarily far at a byte the step touches.  With
    the frame below, "which bytes may have jumped" is decidable from the
    trace, and [WeakViolation.nv_hart_coh_step] turns the obligation into one
    [nv_byte] per touched byte — which is exactly what a leaf can pay from
    the points-to / sync witness it already holds for its own window. *)

Definition weff_touches (e : weff) (a : Z) : Prop :=
  match e with
  | WEread _ pa n => exists j : nat, (j < N.to_nat n)%nat /\ a = acc_addr pa j
  | WEwrite _ pa n _ => exists j : nat, (j < N.to_nat n)%nat /\ a = acc_addr pa j
  | WEbar _ => False
  end.

Definition weffs_touch (es : list weff) (a : Z) : Prop :=
  exists e, e ∈ es /\ weff_touches e a.

(** Both are DECIDABLE — a window is an interval, and a trace is a list —
    which is what lets the frame below be used in the contrapositive
    direction without any classical reasoning. *)
Global Instance weff_touches_dec (e : weff) (a : Z) : Decision (weff_touches e a).
Proof.
  assert (Hiv : forall (pa : Arch.pa) (n : N),
            Decision (exists j : nat, (j < N.to_nat n)%nat /\ a = acc_addr pa j)).
  { intros pa n.
    destruct (decide (pa_z pa <= a /\ a < pa_z pa + Z.of_nat (N.to_nat n)))
      as [[Hlo Hhi]|Hno].
    - left. exists (Z.to_nat (a - pa_z pa)). rewrite /acc_addr. split; lia.
    - right. intros (j & Hj & Heq). apply Hno. rewrite /acc_addr in Heq. lia. }
  destruct e as [ak pa n|ak pa n v|b]; simpl; [apply Hiv|apply Hiv|right; tauto].
Qed.

Global Instance weffs_touch_dec (es : list weff) (a : Z)
    : Decision (weffs_touch es a).
Proof.
  induction es as [|e es IH].
  - right. intros (e & He & _). by apply elem_of_nil in He.
  - destruct (decide (weff_touches e a)) as [H|H].
    + left. exists e. split; [apply elem_of_list_here|exact H].
    + destruct IH as [IH|IH].
      * left. destruct IH as (e' & He' & Hp). exists e'.
        split; [by apply elem_of_list_further|exact Hp].
      * right. intros (e' & He' & Hp).
        apply elem_of_cons in He' as [->|He']; [by apply H|].
        apply IH. by exists e'.
Qed.

(** Decomposition, for the leaves that read their footprint off a literal
    trace. *)
Lemma weffs_touch_cons (e : weff) (es : list weff) (a : Z) :
  weffs_touch (e :: es) a -> weff_touches e a \/ weffs_touch es a.
Proof.
  intros (e' & He' & Ht). apply elem_of_cons in He' as [->|He'];
    [by left|right; by exists e'].
Qed.

Lemma weffs_touch_app (es1 es2 : list weff) (a : Z) :
  weffs_touch (es1 ++ es2) a -> weffs_touch es1 a \/ weffs_touch es2 a.
Proof.
  intros (e & He & Ht). apply elem_of_app in He as [He|He];
    [left|right]; by exists e.
Qed.

Lemma weffs_touch_nil (a : Z) : weffs_touch [] a -> False.
Proof. intros (e & He & _). by apply elem_of_nil in He. Qed.

Lemma weffs_touch_read1 (ak : akinfo) (pa : Arch.pa) (n : N) (a : Z) :
  weffs_touch [WEread ak pa n] a ->
  exists j : nat, (j < N.to_nat n)%nat /\ a = acc_addr pa j.
Proof.
  intros (e & He & Ht). apply elem_of_list_singleton in He as ->. exact Ht.
Qed.

Lemma weffs_touch_write1 (ak : akinfo) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (a : Z) :
  weffs_touch [WEwrite ak pa n v] a ->
  exists j : nat, (j < N.to_nat n)%nat /\ a = acc_addr pa j.
Proof.
  intros (e & He & Ht). apply elem_of_list_singleton in He as ->. exact Ht.
Qed.

(** The other fetch-trace shape the register-only family uses — a single
    read of [pc], at width 4 or (compressed) 2.  Same conclusion as
    [WeakLeafRegOnly.weffs_touch_regonly]: the footprint is inside the four text bytes. *)
Lemma weffs_touch_read1_4 (ak : akinfo) (pc : Arch.pa) (n : N) (a : Z) :
  (N.to_nat n <= 4)%nat ->
  weffs_touch [WEread ak pc n] a ->
  exists j : nat, (j < 4)%nat /\ a = acc_addr pc j.
Proof.
  intros Hn Ha. destruct (weffs_touch_read1 ak pc n a Ha) as (j & Hj & ->).
  exists j. split; [lia|reflexivity].
Qed.

(** The COMPRESSED fetch trace (two 2-byte reads, the 2-not-4-aligned arm):
    its footprint is still inside the four text bytes of [pc], which needs
    the wrap-freedom of the window to move the high half's base. *)
Lemma weffs_touch_fetch2 (ak : akinfo) (pc : Arch.pa) (a : Z) :
  acc_wf pc 4 ->
  weffs_touch [WEread ak pc 2; WEread ak (add_vec_int pc 2) 2] a ->
  exists j : nat, (j < 4)%nat /\ a = acc_addr pc j.
Proof.
  intros Hacc Ha.
  assert (Hhi : pa_z (add_vec_int pc 2) = pa_z pc + 2).
  { replace (add_vec_int pc 2) with (pa_add pc 2)
      by (rewrite /pa_add; f_equal).
    rewrite (acc_wf_byte pc 4 2 Hacc ltac:(lia)) /acc_addr. lia. }
  apply weffs_touch_cons in Ha as [Ha|Ha].
  - destruct Ha as (j & Hj & ->). exists j. split; [cbn in Hj; lia|reflexivity].
  - destruct (weffs_touch_read1 _ _ _ a Ha) as (j & Hj & ->).
    exists (2 + j)%nat. cbn in Hj. split; [lia|].
    rewrite /acc_addr Hhi. lia.
Qed.

(** The two per-byte frames, off [WeakMem.coh_upd_ne]. *)
Lemma coh_load_post_at_ne ws aq vpre a' t a :
  a <> a' -> coh (load_post_at ws aq vpre a' t) a = coh ws a.
Proof. intros Hne. rewrite /load_post_at /coh /= lookup_insert_ne //. Qed.

Lemma coh_store_post_ne ws rl a' t a :
  a <> a' -> coh (store_post ws rl a' t) a = coh ws a.
Proof. intros Hne. rewrite /store_post /coh /= lookup_insert_ne //. Qed.

Lemma coh_foldl_load_ne (aq : bool) (vpre : nat) (ats : list (Z * nat)) (a : Z) :
  (forall p, p ∈ ats -> a <> p.1) ->
  forall w, coh (foldl (fun w at_ => load_post_at w aq vpre at_.1 at_.2) w ats) a
            = coh w a.
Proof.
  induction ats as [|at_ ats IH]; intros Hno w; [reflexivity|].
  simpl. rewrite IH; [|intros p Hp; apply Hno; by apply elem_of_list_further].
  apply coh_load_post_at_ne, Hno, elem_of_list_here.
Qed.

Lemma coh_load_post_bytes_ne ws aq ats a :
  (forall p, p ∈ ats -> a <> p.1) -> coh (load_post_bytes ws aq ats) a = coh ws a.
Proof. intros Hno. by apply coh_foldl_load_ne. Qed.

Lemma coh_foldl_store_ne (rl : bool) (as_ : list Z) (t : nat) (a : Z) :
  (forall z, z ∈ as_ -> a <> z) ->
  forall w, coh (foldl (fun w z => store_post w rl z t) w as_) a = coh w a.
Proof.
  induction as_ as [|z as_ IH]; intros Hno w; [reflexivity|].
  simpl. rewrite IH; [|intros z' Hz'; apply Hno; by apply elem_of_list_further].
  apply coh_store_post_ne, Hno, elem_of_list_here.
Qed.

Lemma coh_store_post_bytes_ne ws rl as_ t a :
  (forall z, z ∈ as_ -> a <> z) -> coh (store_post_bytes ws rl as_ t) a = coh ws a.
Proof. intros Hno. by apply coh_foldl_store_ne. Qed.

(** ... and the two contiguous instances, at the [acc_addr] spelling of a
    window that both [WeakInterp.wread_post] and [wwrite_post] use. *)
Lemma coh_load_post_run_ne ws aq (pa : Arch.pa) (ts : list nat) (a : Z) :
  (forall j : nat, (j < length ts)%nat -> a <> acc_addr pa j) ->
  coh (load_post_run ws aq (pa_z pa) ts) a = coh ws a.
Proof.
  intros Hno. rewrite /load_post_run. apply coh_load_post_bytes_ne.
  intros p Hp. apply elem_of_zip_with in Hp as (j & t & -> & Hj & _).
  apply elem_of_seq in Hj as [_ Hj]. simpl.
  apply (Hno j). lia.
Qed.

Lemma coh_store_post_run_ne ws rl (pa : Arch.pa) (n : nat) (t : nat) (a : Z) :
  (forall j : nat, (j < n)%nat -> a <> acc_addr pa j) ->
  coh (store_post_run ws rl (pa_z pa) n t) a = coh ws a.
Proof.
  intros Hno. rewrite /store_post_run. apply coh_store_post_bytes_ne.
  intros z Hz. apply elem_of_list_fmap in Hz as (j & -> & Hj).
  apply elem_of_seq in Hj as [_ Hj]. apply (Hno j). lia.
Qed.

(** THE FRAME, per effect and then along a whole trace. *)
Lemma weff_apply_coh_frame tid s e a :
  ¬ weff_touches e a -> coh (wm_ws (weff_apply tid s e)) a = coh (wm_ws s) a.
Proof.
  destruct e as [ak pa n|ak pa n v|b]; intros Hno.
  - rewrite weff_apply_read /wread_post. destruct (ak_coh ak); [reflexivity|].
    rewrite /wset_ws /=. apply coh_load_post_run_ne.
    intros j Hj Heq. apply Hno. exists j.
    split; [by rewrite coh_ts_length in Hj|exact Heq].
  - rewrite weff_apply_write /wwrite_post /=. apply coh_store_post_run_ne.
    intros j Hj Heq. apply Hno. by exists j.
  - rewrite weff_apply_bar /wset_ws /= /barrier_post. by destruct b.
Qed.

Lemma weffs_coh_frame tid s es a :
  ¬ weffs_touch es a -> coh (wm_ws (weffs tid s es)) a = coh (wm_ws s) a.
Proof.
  revert s. induction es as [|e es IH]; intros s Hno; [reflexivity|].
  rewrite weffs_cons IH.
  - apply weff_apply_coh_frame. intros Ht. apply Hno.
    exists e. split; [apply elem_of_list_here|exact Ht].
  - intros (e' & He' & Ht). apply Hno. exists e'.
    split; [by apply elem_of_list_further|exact Ht].
Qed.

(** THE LOG SIDE: every message a trace appends carries the runner's own tid
    ([WeakInterp.wwrite_msg] stamps the interpreter's [tid] parameter), which
    is what makes a hart's own stores free for its own violation-freedom
    obligation ([WeakViolation.nv_hart_app_own]). *)
Lemma weffs_log_own tid s es :
  exists ms, wm_log (weffs tid s es) = (wm_log s ++ ms)%list /\
             (forall m, m ∈ ms -> wm_tid m = tid).
Proof.
  revert s. induction es as [|e es IH]; intros s.
  - exists []. rewrite weffs_nil app_nil_r. split; [reflexivity|].
    intros m Hm. by apply elem_of_nil in Hm.
  - destruct (IH (weff_apply tid s e)) as (ms2 & Hms2 & Hown2).
    assert (Hstep : exists ms1, wm_log (weff_apply tid s e)
                                = (wm_log s ++ ms1)%list /\
                                (forall m, m ∈ ms1 -> wm_tid m = tid)).
    { destruct e as [ak pa n|ak pa n v|b].
      - exists []. rewrite weff_apply_read wread_post_log app_nil_r.
        split; [reflexivity|]. intros m Hm. by apply elem_of_nil in Hm.
      - exists [wwrite_msg tid (wm_class_of ak (wm_ws s)) pa n v].
        rewrite weff_apply_write /wwrite_post /=. split; [reflexivity|].
        intros m Hm. apply elem_of_list_singleton in Hm as ->. reflexivity.
      - exists []. rewrite weff_apply_bar app_nil_r.
        split; [reflexivity|]. intros m Hm. by apply elem_of_nil in Hm. }
    destruct Hstep as (ms1 & Hms1 & Hown1).
    exists (ms1 ++ ms2)%list. rewrite weffs_cons Hms2 Hms1 -app_assoc.
    split; [reflexivity|]. intros m Hm.
    apply elem_of_app in Hm as [Hm|Hm]; [by apply Hown1|by apply Hown2].
Qed.

(** THE LEAF-FACING COMBINATOR, and the point of the whole section: a leaf's
    violation-freedom obligation reduces to ONE [WeakViolation.nv_byte] per
    byte of its own effect trace — which is precisely what
    [WeakViolation.nv_byte_of_pointsto] / [_of_own_st] / [_of_sync] read off
    the resources the leaf already holds for its window (and, for the FETCH,
    what [WeakFunnel.winstr_flat]'s "the text is unwritten" gives for free:
    a byte no message writes satisfies [nv_byte] vacuously). *)
Lemma nv_hart_weffs (c : CPU) (s : wmstate) (es : list weff) :
  nv_hart (wm_log s) c (wm_ws s) ->
  (forall a : Z, weffs_touch es a ->
     nv_byte (wm_log (weffs (Some (fin_to_nat c)) s es)) c a
             (coh (wm_ws (weffs (Some (fin_to_nat c)) s es)) a)) ->
  nv_hart (wm_log (weffs (Some (fin_to_nat c)) s es)) c
          (wm_ws (weffs (Some (fin_to_nat c)) s es)).
Proof.
  intros Hnv Htouch.
  destruct (weffs_log_own (Some (fin_to_nat c)) s es) as (ms & Hms & Hown).
  rewrite Hms. apply (nv_hart_coh_step _ c (wm_ws s)).
  - by apply nv_hart_app_own.
  - intros a Hlt. rewrite -Hms. apply Htouch.
    destruct (decide (weffs_touch es a)) as [Ht|Ht]; [exact Ht|exfalso].
    rewrite (weffs_coh_frame (Some (fin_to_nat c)) s es a Ht) in Hlt. lia.
Qed.

(* ====================================================================== *)
(** ** 5c. CARRYING THE TRACE THROUGH THE CERTIFICATE (φ-upgrade, (i))

    [WeakCert.wstep_cert_eff] already PROVES that the successor's log and
    weak state are the fold of the effect trace; every [wcert_*] below then
    throws that away and keeps only the view arithmetic its leaf wants.  The
    violation-freedom conjunct needs it back — [nv_hart_weffs] is stated
    exactly at it — so [wQ_eff] names it and [wstep_cert_fr] pairs it with
    ANY certificate the leaf already has, generically, so that no [wcert_*]
    has to be restated. *)

Definition wQ_eff (tid : option nat) (es : list weff) : wmstate -> wmstate -> Prop :=
  fun s s' => wm_img s' = wm_img s /\
              wm_log s' = wm_log (weffs tid s es) /\
              wm_ws s' = wm_ws (weffs tid s es).

Definition wQ_fr (Q : wmstate -> wmstate -> Prop) (tid : option nat)
    (es : list weff) : wmstate -> wmstate -> Prop :=
  fun s s' => Q s s' /\ wQ_eff tid es s s'.

Lemma wcert_eff (cid : nat) (pc : SailStdpp.Values.mword 64) (es : list weff) :
  wstep_cert cid pc (wP_eff (Some cid) es) (wQ_eff (Some cid) es).
Proof.
  apply wstep_cert_eff. intros s s' Hi Hl Hws. by split_and!.
Qed.

(** Two certificates over the SAME precondition conjoin — [wstep_cert]'s
    "the step is admissible" half is shared and its post half is pointwise.
    This is the whole content of pairing the trace onto a leaf's own
    certificate, at either shape of the precondition. *)
Lemma wstep_cert_pair (cid : nat) (pc : SailStdpp.Values.mword 64)
    (P : wmstate -> Prop) (Q1 Q2 : wmstate -> wmstate -> Prop) :
  wstep_cert cid pc P Q1 ->
  wstep_cert cid pc P Q2 ->
  wstep_cert cid pc P (fun s s' => Q1 s s' /\ Q2 s s').
Proof.
  intros H1 H2 s tick Hpc Hacc Htext HP.
  destruct (H1 s tick Hpc Hacc Htext HP) as [Hok Hq1].
  destruct (H2 s tick Hpc Hacc Htext HP) as [_ Hq2].
  split; [exact Hok|]. intros χ s' χ' Hex.
  split; [exact (Hq1 χ s' χ' Hex)|exact (Hq2 χ s' χ' Hex)].
Qed.

Lemma wstep_cert_fr (cid : nat) (pc : SailStdpp.Values.mword 64)
    (es : list weff) (Q : wmstate -> wmstate -> Prop) :
  wstep_cert cid pc (wP_eff (Some cid) es) Q ->
  wstep_cert cid pc (wP_eff (Some cid) es) (wQ_fr Q (Some cid) es).
Proof.
  intros HQ. exact (wstep_cert_pair cid pc _ Q _ HQ (wcert_eff cid pc es)).
Qed.

(** ... and the same at the PIN shape of the precondition, which is what an
    invariant-form leaf produces ([WeakFetchEff.wcert_amo_aq_pin_base4]): the
    lock's AMO cannot present [wP_eff]'s every-read-pinned window (the lock
    word is read out of the INVARIANT, not out of the hart's own bundle), so
    the trace has to ride onto the pin certificate directly. *)
Lemma wcert_eff_pin (cid : nat) (pc : SailStdpp.Values.mword 64)
    (es : list weff) :
  wstep_cert cid pc (wP_eff_pin (Some cid) es) (wQ_eff (Some cid) es).
Proof.
  apply wstep_cert_eff_pin. intros s s' Hi Hl Hws. by split_and!.
Qed.

Lemma wstep_cert_fr_pin (cid : nat) (pc : SailStdpp.Values.mword 64)
    (es : list weff) (Q : wmstate -> wmstate -> Prop) :
  wstep_cert cid pc (wP_eff_pin (Some cid) es) Q ->
  wstep_cert cid pc (wP_eff_pin (Some cid) es) (wQ_fr Q (Some cid) es).
Proof.
  intros HQ. exact (wstep_cert_pair cid pc _ Q _ HQ (wcert_eff_pin cid pc es)).
Qed.

(** THE LEAF-FACING ONE-LINER.  With [wQ_eff] in hand, a leaf's whole
    violation-freedom obligation is: for each byte its OWN effect trace
    touches, one [WeakViolation.nv_byte] — paid by the fragment it already
    holds for that byte ([nv_byte_of_pointsto] / [_of_own_st] / [_of_sync]),
    or, for the FETCH window, for free ([nv_byte_unwritten]). *)
Lemma nv_hart_of_wQ_eff (c : CPU) (σ σ' : wmstate) (es : list weff) :
  wQ_eff (Some (fin_to_nat c)) es σ σ' ->
  nv_hart (wm_log σ) c (wm_ws σ) ->
  (forall a : Z, weffs_touch es a ->
     nv_byte (wm_log σ') c a (coh (wm_ws σ') a)) ->
  nv_hart (wm_log σ') c (wm_ws σ').
Proof.
  intros (_ & Hl & Hws) Hnv Ht. rewrite Hl Hws. rewrite Hl Hws in Ht.
  by apply nv_hart_weffs.
Qed.

(** The [nv_ok] form — the one the DATA leaves use, since an owned byte is
    safe for its owner but not for everyone. *)
Lemma nv_hart_of_wQ_eff_ok (c : CPU) (σ σ' : wmstate) (es : list weff) :
  wQ_eff (Some (fin_to_nat c)) es σ σ' ->
  nv_hart (wm_log σ) c (wm_ws σ) ->
  (forall a : Z, weffs_touch es a -> nv_ok (wm_log σ') c a) ->
  nv_hart (wm_log σ') c (wm_ws σ').
Proof.
  intros HQ Hnv Ht. apply (nv_hart_of_wQ_eff c σ σ' es HQ Hnv).
  intros a Ha. by apply nv_byte_of_ok, Ht.
Qed.

(** ... and its FETCH-ONLY instance, which is what every register-only leaf
    (the bulk of the sweep) applies: the trace touches only the text window,
    and text is unwritten. *)
Lemma nv_hart_of_wQ_eff_unwritten (c : CPU) (σ σ' : wmstate) (es : list weff) :
  wQ_eff (Some (fin_to_nat c)) es σ σ' ->
  nv_hart (wm_log σ) c (wm_ws σ) ->
  (forall a : Z, weffs_touch es a -> latest_ts (wm_log σ') a = 0%nat) ->
  nv_hart (wm_log σ') c (wm_ws σ').
Proof.
  intros HQ Hnv Ht. apply (nv_hart_of_wQ_eff c σ σ' es HQ Hnv).
  intros a Ha. by apply nv_byte_unwritten, Ht.
Qed.
