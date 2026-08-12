(** * WeakRacy.v — the RACY-LOAD rule (M4-prep)

    THE GAP THIS CLOSES.  [WeakInstr.wp_winstr] rests on the PINNED-fragment
    bridge of [WeakBridge]: its read arm demands that the hart's own index
    already cover the latest write to every byte the step reads, and then the
    whole step is described by an [exec] fact about the COHERENT flat
    projection [WeakBridge.wflat_st σ].  A hart spinning on [started] is
    exactly the case where that fails: it legally reads a STALE message while
    [wflat_st σ] already holds the setter's 1, so NO [exec] fact about the flat
    projection describes the step (see the closing note of [WeakAcquire.v]).

    THE SHAPE OF THE ANSWER.  One RACY WINDOW [ra, ra+rn) is singled out, and
    everything is stated at the flat memory PATCHED at that window with the
    value the run actually read:

      [wpatch_st σ ra rn w := MState (wm_regs σ) (write_bytes (wflat …) ra rn w) (wm_dev σ)]

    Away from the window the machine is on the pinned fragment and the M3a
    argument goes through verbatim; at the window nothing is pinned and the
    rule quantifies over the ADMISSIBLE read results instead.  The ∀-oracle
    surface that survives to the user is therefore ONE binder — the racy WORD
    [w : bv (8*rn)] — together with the per-byte admissibility
    [∃ t, wbyte_ok σ rak (acc_addr ra j) t (nth_byte w j)], which is exactly
    what [WeakStarted.wstarted_read_ts] consumes.  No oracle, no timestamp
    list, no view appears in any user-facing statement.

    ======================= WHAT IS IN HERE =======================

    §1  the window: disjointness of two accesses, and the [write_bytes]
        algebra the patch needs (a disjoint read does not see the patch; a
        disjoint write commutes with it; a patch by the value already there is
        the identity).
    §2  [wstep_ok_racy] — [WeakBridge.wstep_ok] arm for arm, EXCEPT at a RAM
        read whose footprint IS the window, where the pinnedness obligation is
        replaced by a ∀ over admissible timestamp lists and values.  A boolean
        phase parameter says whether the racy read is still ahead ([true]) or
        already behind ([false]); after it, the window may not be touched
        again.
    §3  the transport lemmas of the pre-racy phase (its states differ from the
        initial one only in views, so admissibility transports DOWN).
    §4  THE BRIDGE, [exec_of_wrun_racy] (consumption direction, over [wrun] —
        the relational interpreter, which is what [WeakExec.wp_wrun_step]
        hands a leaf), and its window-free companion [exec_of_wrun_win].
    §5  the reducibility direction, [wexec_of_exec_racy], and the
        [wexec_covers] mirror [wrun_wexec_racy] — both at the CANONICAL
        (latest) value, which is pinned, so the caller's ordinary [exec] fact
        about [wflat_st σ] serves.
    §6  THE RULE, [wp_wracy_load], over [WeakExec.wp_wrun_step] (which has no
        bridge premise at all).
    §7  the [lw]-shaped racy leaf: the collapse of the ∀-over-admissible-values
        into a DISJUNCTION for a one-shot flag.

    ================== WHAT IS DELIBERATELY RESTRICTED ==================

    A RAM WRITE IS ALLOWED ONLY AFTER THE RACY READ.  In the pre-racy phase
    the states of the run differ from the initial one only in VIEWS (image and
    log are untouched), which is what makes the admissibility of the racy
    value transportable back to the pre-state with no side conditions.  A
    racy LOAD writes nothing before its own read, so nothing is lost; and
    after the racy read a RAM write is allowed, subject to its footprint being
    disjoint from the window. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import WeakLock.
Require Import WeakStarted.
Require Import RiscvLang RiscvPtsto RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The racy window and the patched memory *)

(** Two accesses do not overlap.  Stated on the [Z] side (where [acc_wf] makes
    an access an honest interval) rather than as a [gset] disjointness, so
    that the whole argument is [lia]. *)
Definition racc_disj (ra : Arch.pa) (rn : N) (pa : Arch.pa) (n : N) : Prop :=
  pa_z pa + Z.of_N n <= pa_z ra \/ pa_z ra + Z.of_N rn <= pa_z pa.

Lemma acc_addr_range (pa : Arch.pa) (n : N) (j : nat) :
  acc_wf pa n -> (j < N.to_nat n)%nat ->
  0 <= acc_addr pa j < 18446744073709551616.
Proof.
  rewrite /acc_wf /acc_addr => Hwf Hj.
  pose proof (pa_z_range pa) as Hr.
  assert (Z.of_nat j < Z.of_N n) by lia. lia.
Qed.

(** Distinct bytes of two disjoint accesses are distinct addresses ... *)
Lemma pa_add_neq (pa ra : Arch.pa) (n rn : N) (j i : nat) :
  acc_wf pa n -> acc_wf ra rn -> racc_disj ra rn pa n ->
  (j < N.to_nat n)%nat -> (i < N.to_nat rn)%nat ->
  pa_add pa j <> pa_add ra i.
Proof.
  intros Hp Hr Hd Hj Hi Heq.
  rewrite -(z_pa_acc_addr pa j) -(z_pa_acc_addr ra i) in Heq.
  apply z_pa_inj in Heq;
    [| exact (acc_addr_range pa n j Hp Hj)
     | exact (acc_addr_range ra rn i Hr Hi)].
  rewrite /acc_addr in Heq. rewrite /racc_disj in Hd.
  assert (Z.of_nat j < Z.of_N n) by lia.
  assert (Z.of_nat i < Z.of_N rn) by lia. lia.
Qed.

(** ... and distinct bytes of ONE wrap-free access are distinct addresses. *)
Lemma pa_add_inj (pa : Arch.pa) (n : N) (j j' : nat) :
  acc_wf pa n -> (j < N.to_nat n)%nat -> (j' < N.to_nat n)%nat ->
  pa_add pa j = pa_add pa j' -> j = j'.
Proof.
  intros Hwf Hj Hj' Heq.
  rewrite -(z_pa_acc_addr pa j) -(z_pa_acc_addr pa j') in Heq.
  apply z_pa_inj in Heq;
    [| exact (acc_addr_range pa n j Hwf Hj)
     | exact (acc_addr_range pa n j' Hwf Hj')].
  rewrite /acc_addr in Heq. lia.
Qed.

(** *** The [write_bytes] algebra *)

Lemma write_bytes_lookup_ne {wd : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (v : bv wd) (a : Arch.pa) :
  (forall j : nat, (j < N.to_nat n)%nat -> a <> pa_add pa j) ->
  write_bytes mm pa n v !! a = mm !! a.
Proof.
  intros Hne. rewrite /write_bytes.
  assert (Hl : forall j : nat, j ∈ seq 0 (N.to_nat n) -> a <> pa_add pa j).
  { intros j Hj%elem_of_seq. apply Hne. lia. }
  revert Hl. generalize (seq 0 (N.to_nat n)) as l. intros l Hl.
  induction l as [|j l IH]; [reflexivity|].
  simpl. rewrite lookup_insert_ne.
  - apply IH. intros j' Hj'. apply Hl, elem_of_cons. by right.
  - intros Heq. apply (Hl j); [apply elem_of_cons; by left|]. by rewrite Heq.
Qed.

Lemma write_bytes_lookup_at {wd : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (v : bv wd) (j : nat) :
  acc_wf pa n -> (j < N.to_nat n)%nat ->
  write_bytes mm pa n v !! pa_add pa j = Some (nth_byte v j).
Proof.
  intros Hwf Hj. rewrite /write_bytes.
  assert (Hin : j ∈ seq 0 (N.to_nat n)) by (apply elem_of_seq; lia).
  assert (Hsub : forall i : nat, i ∈ seq 0 (N.to_nat n) -> (i < N.to_nat n)%nat)
    by (intros i Hi%elem_of_seq; lia).
  revert Hin Hsub. generalize (seq 0 (N.to_nat n)) as l. intros l Hin Hsub.
  induction l as [|i l IH]; [by apply elem_of_nil in Hin|].
  simpl. destruct (decide (i = j)) as [->|Hne].
  - by rewrite lookup_insert.
  - rewrite lookup_insert_ne.
    + apply IH.
      * apply elem_of_cons in Hin as [Hij|Hin'];
          [by destruct (Hne (eq_sym Hij))|exact Hin'].
      * intros i' Hi'. apply Hsub, elem_of_cons. by right.
    + intros Heq. apply Hne.
      apply (pa_add_inj pa n i j Hwf); [|exact Hj|exact Heq].
      apply Hsub, elem_of_cons. by left.
Qed.

(** Patching a window with the value it already holds is the identity. *)
Lemma write_bytes_id (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) :
  (forall j : nat, (j < N.to_nat n)%nat -> mm !! pa_add pa j = Some (nth_byte v j)) ->
  write_bytes mm pa n v = mm.
Proof.
  intros Hv. rewrite /write_bytes.
  assert (Hl : forall j : nat, j ∈ seq 0 (N.to_nat n) ->
                 mm !! pa_add pa j = Some (nth_byte v j)).
  { intros j Hj%elem_of_seq. apply Hv. lia. }
  revert Hl. generalize (seq 0 (N.to_nat n)) as l. intros l Hl.
  induction l as [|j l IH]; [reflexivity|].
  simpl. rewrite IH.
  - apply insert_id, Hl, elem_of_cons. by left.
  - intros j' Hj'. apply Hl, elem_of_cons. by right.
Qed.

(** The converse of [RiscvModelBytes.read_bytes_spec] — the shape the caller
    of the rule uses to see the window in the flat memory. *)
Lemma read_bytes_of_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) :
  (forall j : nat, (j < N.to_nat n)%nat -> mm !! pa_add pa j = Some (nth_byte v j)) ->
  read_bytes mm pa n = Some v.
Proof.
  intros Hv.
  assert (Hm : mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n))
               = Some ((fun j : nat => nth_byte v j) <$> seq 0 (N.to_nat n))).
  { apply mapM_Some_2, Forall2_fmap_r, Forall_Forall2_diag, Forall_forall.
    intros j Hj. apply Hv.
    assert (Hj' : j ∈ seq 0 (N.to_nat n))
      by (first [exact Hj | by apply elem_of_list_In]).
    apply elem_of_seq in Hj'. lia. }
  assert (Hs : exists u, read_bytes mm pa n = Some u).
  { rewrite /read_bytes Hm. by eexists. }
  destruct Hs as [u Hu]. rewrite Hu. f_equal.
  apply bv_eq_of_bytes. intros j Hj.
  pose proof (read_bytes_spec mm pa n u Hu j Hj) as Hb.
  pose proof (Hv j ltac:(lia)) as Hb2. congruence.
Qed.

(** A read DISJOINT from the window does not see the patch ... *)
Lemma read_bytes_patch_disj (mm : gmap Arch.pa (bv 8)) (ra : Arch.pa) (rn : N)
    (w : bv (8 * rn)) (pa : Arch.pa) (n : N) :
  acc_wf ra rn -> acc_wf pa n -> racc_disj ra rn pa n ->
  read_bytes (write_bytes mm ra rn w) pa n = read_bytes mm pa n.
Proof.
  intros Hr Hp Hd. rewrite /read_bytes.
  rewrite (mapM_seq_ext
             (fun j : nat => write_bytes mm ra rn w !! pa_add pa j)
             (fun j : nat => mm !! pa_add pa j) 0 (N.to_nat n)) //.
  intros j Hj. apply write_bytes_lookup_ne. intros i Hi.
  apply (pa_add_neq pa ra n rn j i Hp Hr Hd); lia.
Qed.

(** ... and a WRITE disjoint from the window commutes with it. *)
Lemma write_bytes_patch_comm {wd : N} (mm : gmap Arch.pa (bv 8))
    (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    (pa : Arch.pa) (n : N) (v : bv wd) :
  acc_wf ra rn -> acc_wf pa n -> racc_disj ra rn pa n ->
  write_bytes (write_bytes mm ra rn w) pa n v
  = write_bytes (write_bytes mm pa n v) ra rn w.
Proof.
  intros Hr Hp Hd. apply map_eq. intros a.
  destruct (existsb (fun i : nat => bool_decide (a = pa_add ra i))
                    (seq 0 (N.to_nat rn))) eqn:Hin.
  - (* [a] is in the window *)
    apply existsb_exists in Hin as (i & Hi%elem_of_list_In%elem_of_seq & Hai).
    apply bool_decide_eq_true in Hai as ->.
    assert (Hi' : (i < N.to_nat rn)%nat) by lia.
    rewrite (write_bytes_lookup_ne (write_bytes mm ra rn w) pa n v (pa_add ra i)).
    2:{ intros j Hj Heq. apply (pa_add_neq pa ra n rn j i Hp Hr Hd);
        [lia|lia|by rewrite Heq]. }
    rewrite (write_bytes_lookup_at mm ra rn w i Hr Hi').
    rewrite (write_bytes_lookup_at (write_bytes mm pa n v) ra rn w i Hr Hi') //.
  - (* [a] is outside the window *)
    assert (Hout : forall i : nat, (i < N.to_nat rn)%nat -> a <> pa_add ra i).
    { intros i Hi Heq. destruct (existsb_exists
        (fun i0 : nat => bool_decide (a = pa_add ra i0)) (seq 0 (N.to_nat rn)))
        as [_ Hb].
      rewrite Hb in Hin; [discriminate|]. exists i.
      split; [apply elem_of_list_In, elem_of_seq; lia|].
      by apply bool_decide_eq_true. }
    rewrite (write_bytes_lookup_ne (write_bytes mm pa n v) ra rn w a Hout).
    destruct (existsb (fun j : nat => bool_decide (a = pa_add pa j))
                      (seq 0 (N.to_nat n))) eqn:Hinp.
    + apply existsb_exists in Hinp as (j & Hj%elem_of_list_In%elem_of_seq & Haj).
      apply bool_decide_eq_true in Haj as ->.
      assert (Hj' : (j < N.to_nat n)%nat) by lia.
      rewrite (write_bytes_lookup_at (write_bytes mm ra rn w) pa n v j Hp Hj').
      rewrite (write_bytes_lookup_at mm pa n v j Hp Hj') //.
    + assert (Houtp : forall j : nat, (j < N.to_nat n)%nat -> a <> pa_add pa j).
      { intros j Hj Heq. destruct (existsb_exists
          (fun j0 : nat => bool_decide (a = pa_add pa j0)) (seq 0 (N.to_nat n)))
          as [_ Hb].
        rewrite Hb in Hinp; [discriminate|]. exists j.
        split; [apply elem_of_list_In, elem_of_seq; lia|].
        by apply bool_decide_eq_true. }
      rewrite (write_bytes_lookup_ne (write_bytes mm ra rn w) pa n v a Houtp).
      rewrite (write_bytes_lookup_ne mm pa n v a Houtp).
      rewrite (write_bytes_lookup_ne mm ra rn w a Hout) //.
Qed.

(** THE PATCHED SC STATE.  [WeakBridge.wflat_st] with the racy window
    overwritten by [w] — the state every [exec] fact in this file is about. *)
Definition wpatch_st (s : wmstate) (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    : mstate :=
  MState (wm_regs s) (write_bytes (wflat (wm_img s) (wm_log s)) ra rn w)
         (wm_dev s).

Lemma wpatch_st_reg_set s ra rn w r v :
  wpatch_st (wset_reg s r v) ra rn w = set_reg (wpatch_st s ra rn w) r v.
Proof. reflexivity. Qed.

Lemma wpatch_st_ws s ra rn w ws : wpatch_st (wset_ws s ws) ra rn w = wpatch_st s ra rn w.
Proof. reflexivity. Qed.

Lemma wpatch_st_read_post s ra rn w ak pa ts :
  wpatch_st (wread_post s ak pa ts) ra rn w = wpatch_st s ra rn w.
Proof.
  rewrite /wpatch_st wread_post_regs wread_post_img wread_post_log
          wread_post_dev //.
Qed.

Lemma wpatch_st_dev_set s ra rn w d :
  wpatch_st (wset_dev s d) ra rn w
  = MState (sregs (wpatch_st s ra rn w)) (mem (wpatch_st s ra rn w)) d.
Proof. reflexivity. Qed.

(** The patch of the successor of a DISJOINT write is the write over the
    patch — the one algebraic fact the write arm of the bridge needs. *)
Lemma wpatch_st_write_post tid s ra rn (w : bv (8 * rn)) ak pa n (v : bv (8 * n)) :
  acc_wf ra rn -> acc_wf pa n -> racc_disj ra rn pa n ->
  wpatch_st (wwrite_post tid s ak pa n v) ra rn w
  = MState (sregs (wpatch_st s ra rn w))
           (write_bytes (mem (wpatch_st s ra rn w)) pa n v)
           (mdev (wpatch_st s ra rn w)).
Proof.
  intros Hr Hp Hd. rewrite /wpatch_st /= (wflat_write tid s ak pa n v).
  by rewrite (write_bytes_patch_comm _ ra rn w pa n v Hr Hp Hd).
Qed.

(* ====================================================================== *)
(** ** 2. [wstep_ok_racy]: the racy-window generalisation of [wstep_ok]

    Arm for arm [WeakBridge.wstep_ok], with two changes at the RAM arms.

    A RAM READ must either be DISJOINT from the window — and then it carries
    [wstep_ok]'s obligations verbatim (pinnedness where the access kind does
    not already force the latest read, successor at the canonical [coh_ts]) —
    or BE the window, and then it carries NO pinnedness and instead quantifies
    over every admissible timestamp list and value.  Partial overlap is
    ruled out (neither disjunct holds).

    A RAM WRITE must be disjoint from the window, and may only occur AFTER the
    racy read (see the header): [b] is [true] while the racy read is still
    ahead and [false] once it is behind, and only the [false] phase writes. *)

Fixpoint wstep_ok_racy (tid : option nat) (ra : Arch.pa) (rn : N)
    (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) (b : bool)
    {X} (m : M X) (s : wmstate) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       | Interface.RegRead r _ =>
           fun k => wstep_ok_racy tid ra rn rak Φ b
                      (k (register_lookup r s.(wm_regs))) s
       | Interface.RegWrite r _ v =>
           fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) (wset_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               forall w d',
                 dev_read s.(wm_dev) (Interface.ReadReq.pa req) n = Some (w, d') ->
                 wstep_ok_racy tid ra rn rak Φ b (k (inl (w, None))) (wset_dev s d')
             else
               acc_wf (Interface.ReadReq.pa req) n /\
               ( (* AWAY FROM THE WINDOW: [wstep_ok]'s own arm *)
                 (racc_disj ra rn (Interface.ReadReq.pa req) n /\
                  (ak_pins (classify (Interface.ReadReq.access_kind req)) = false ->
                     forall j, (j < N.to_nat n)%nat ->
                       pinned_read s (acc_addr (Interface.ReadReq.pa req) j)) /\
                  (forall w,
                     wread_bytes s (classify (Interface.ReadReq.access_kind req))
                       (Interface.ReadReq.pa req) n
                       (coh_ts s (Interface.ReadReq.pa req) n) = Some w ->
                     wstep_ok_racy tid ra rn rak Φ b (k (inl (w, None)))
                       (wread_post s (classify (Interface.ReadReq.access_kind req))
                          (Interface.ReadReq.pa req)
                          (coh_ts s (Interface.ReadReq.pa req) n))))
                 \/
                 (* THE RACY READ: no pinnedness, ∀ admissible result *)
                 (b = true /\ Interface.ReadReq.pa req = ra /\ n = rn /\
                  classify (Interface.ReadReq.access_kind req) = rak /\
                  (forall ts w,
                     wread_bytes s (classify (Interface.ReadReq.access_kind req))
                       (Interface.ReadReq.pa req) n ts = Some w ->
                     Φ (fun j : nat => nth_byte w j) ->
                     wstep_ok_racy tid ra rn rak Φ false (k (inl (w, None)))
                       (wread_post s (classify (Interface.ReadReq.access_kind req))
                          (Interface.ReadReq.pa req) ts))) )
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               forall d',
                 dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                           (Interface.WriteReq.value req) = Some d' ->
                 wstep_ok_racy tid ra rn rak Φ b (k (inl None)) (wset_dev s d')
             else
               b = false /\
               acc_wf (Interface.WriteReq.pa req) n /\
               racc_disj ra rn (Interface.WriteReq.pa req) n /\
               wstep_ok_racy tid ra rn rak Φ b (k (inl None))
                 (wwrite_post tid s
                    (classify (Interface.WriteReq.access_kind req))
                    (Interface.WriteReq.pa req) n (Interface.WriteReq.value req))
       | Interface.Barrier bk =>
           fun k => wstep_ok_racy tid ra rn rak Φ b (k tt)
                      (wset_ws s (barrier_post s.(wm_ws) bk))
       | Interface.InstrAnnounce _   => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.CacheOp _         => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.TlbOp _           => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.TakeException _   => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.ReturnException _ => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.TranslationStart _=> fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.TranslationEnd _  => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.CycleCount        => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.Message _         => fun k => wstep_ok_racy tid ra rn rak Φ b (k tt) s
       | Interface.GetCycleCount     => fun k => wstep_ok_racy tid ra rn rak Φ b (k 0%Z) s
       (* as in [wstep_ok]: a [Choose] breaks the wrun -> wexec bridge *)
       | Interface.Choose _          => fun _ => False
       | _ => fun _ => True
       end) k
  end.

(** THE USER-FACING ADMISSIBILITY of a racy word: per byte, SOME timestamp of
    the log holds it, and it is admissible for the load's access kind.  This
    is the whole ∀-oracle surface of the rule. *)
Definition wadm (s : wmstate) (rak : akinfo) (ra : Arch.pa) (rn : N)
    (w : bv (8 * rn)) : Prop :=
  forall j : nat, (j < N.to_nat rn)%nat ->
    exists t : nat, wbyte_ok s rak (acc_addr ra j) t (nth_byte w j).

(** A whole admissible read is a fortiori admissible byte by byte. *)
Lemma wadm_of_wread_ok s rak ra rn ts (w : bv (8 * rn)) :
  wread_ok s rak ra rn ts w -> wadm s rak ra rn w.
Proof.
  intros [Hlen Hbytes] j Hj. exists (ts !!! j). apply Hbytes. lia.
Qed.

(* ====================================================================== *)
(** THE VALUE FILTER.  [wstep_ok_racy]'s racy arm asks the caller to prove
    the continuation for every admissible word — which is right for a flag
    whose every value the code handles, and far too strong for a PAGE-TABLE
    LEAF, where an arbitrary 64-bit word need not even be a valid PTE and the
    walk would fault.  [Φ] narrows the obligation to the words the window can
    actually hold, and [wadm_filter] is the side condition that makes that
    sound: it is what REPLACES pinnedness.

    For the [started] flag it is [wadm_any] and costs nothing.  For the walk's
    leaf slot it is [WeakVariant.wadm_variant]'s conclusion — "every
    admissible word is an A/D variant of the canonical leaf" — which
    [WeakKpt.wtlb_res_pt_translateAddr_at] already hands out.

    Stated per BYTE ([nat -> bv 8]) rather than over [bv (8 * rn)] so that no
    width cast is needed inside the fixpoint, where the arm's width is only
    PROPOSITIONALLY equal to [rn]. *)
Definition wadm_filter (s : wmstate) (rak : akinfo) (ra : Arch.pa) (rn : N)
    (Φ : (nat -> bv 8) -> Prop) : Prop :=
  forall w : bv (8 * rn), wadm s rak ra rn w -> Φ (fun j : nat => nth_byte w j).

Definition wadm_any : (nat -> bv 8) -> Prop := fun _ => True.

Lemma wadm_filter_any s rak ra rn : wadm_filter s rak ra rn wadm_any.
Proof. by intros w _. Qed.

(* ====================================================================== *)
(** ** 3. Transport: the pre-racy phase only moves VIEWS

    Every arm the run may take before its racy read leaves the image and the
    log alone and only raises the hart's views ([wread_post] is a [wset_ws],
    and a RAM write is forbidden until the racy read is behind).  So the
    admissibility of the racy value transports DOWN to the pre-state, and so
    does the readability of the window at its canonical timestamps. *)

Lemma load_vpre_mono ws ws2 aq :
  ws_le ws ws2 -> (load_vpre ws aq <= load_vpre ws2 aq)%nat.
Proof.
  intros (_ & _ & _ & Hrn & _ & Hrel & _). rewrite /load_vpre. destruct aq; lia.
Qed.

Lemma readable_ws_down img log ws ws2 vpre vpre2 a t :
  (Nat.max vpre (coh ws a) <= Nat.max vpre2 (coh ws2 a))%nat ->
  readable img log ws2 vpre2 a t -> readable img log ws vpre a t.
Proof.
  intros Hle [Hs Hn]. split; [exact Hs|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|exact Hw]. lia.
Qed.

Lemma wbyte_ok_down (s s2 : wmstate) ak a t b :
  wm_img s2 = wm_img s -> wm_log s2 = wm_log s -> ws_le (wm_ws s) (wm_ws s2) ->
  wbyte_ok s2 ak a t b -> wbyte_ok s ak a t b.
Proof.
  intros Himg Hlog Hle [Hv Hadm].
  rewrite /wimg Himg Hlog in Hv. split; [exact Hv|].
  destruct (ak_coh ak).
  - by rewrite Hlog in Hadm.
  - destruct Hadm as [Hrd Hlat]. rewrite /wimg Himg Hlog in Hrd.
    split.
    + eapply readable_ws_down; [|exact Hrd].
      pose proof (load_vpre_mono (wm_ws s) (wm_ws s2) (ak_sync ak) Hle).
      destruct Hle as (Hcoh & _). pose proof (Hcoh a). lia.
    + rewrite -Hlog. exact Hlat.
Qed.

Lemma wadm_down (s s2 : wmstate) rak ra rn (w : bv (8 * rn)) :
  wm_img s2 = wm_img s -> wm_log s2 = wm_log s -> ws_le (wm_ws s) (wm_ws s2) ->
  wadm s2 rak ra rn w -> wadm s rak ra rn w.
Proof.
  intros Himg Hlog Hle Hw j Hj. destruct (Hw j Hj) as [t Ht].
  exists t. exact (wbyte_ok_down s s2 rak _ t _ Himg Hlog Hle Ht).
Qed.

(** ... and so does the filter's soundness, in the same direction. *)
Lemma wadm_filter_down (s s2 : wmstate) rak ra rn Φ :
  wm_img s2 = wm_img s -> wm_log s2 = wm_log s -> ws_le (wm_ws s) (wm_ws s2) ->
  wadm_filter s rak ra rn Φ -> wadm_filter s2 rak ra rn Φ.
Proof.
  intros Himg Hlog Hle HΦ w Hw. apply HΦ.
  exact (wadm_down s s2 rak ra rn w Himg Hlog Hle Hw).
Qed.

(** The pre-racy phase's step functions, one by one — what the two
    [wexec]-direction traversals need in order to carry the filter's
    soundness across an arm that changes the state. *)
Lemma wadm_filter_set_reg s r v rak ra rn Φ :
  wadm_filter s rak ra rn Φ -> wadm_filter (wset_reg s r v) rak ra rn Φ.
Proof. exact (wadm_filter_down s _ rak ra rn Φ eq_refl eq_refl (reflexivity _)). Qed.

Lemma wadm_filter_set_dev s d rak ra rn Φ :
  wadm_filter s rak ra rn Φ -> wadm_filter (wset_dev s d) rak ra rn Φ.
Proof. exact (wadm_filter_down s _ rak ra rn Φ eq_refl eq_refl (reflexivity _)). Qed.

Lemma wadm_filter_set_ws s ws' rak ra rn Φ :
  ws_le (wm_ws s) ws' ->
  wadm_filter s rak ra rn Φ -> wadm_filter (wset_ws s ws') rak ra rn Φ.
Proof.
  intros Hle.
  exact (wadm_filter_down s (wset_ws s ws') rak ra rn Φ eq_refl eq_refl Hle).
Qed.

Lemma wadm_filter_read_post s ak pa ts rak ra rn Φ :
  wadm_filter s rak ra rn Φ -> wadm_filter (wread_post s ak pa ts) rak ra rn Φ.
Proof.
  apply wadm_filter_down;
    [apply wread_post_img|apply wread_post_log|apply wread_post_ws_le].
Qed.

(** The one move the two traversals make at every arm of the PRE-racy phase. *)
Ltac filt_step :=
  let Hb := fresh "Hb" in
  intros Hb;
  match goal with
  | HΦ : _ = true -> wadm_filter _ _ _ _ _ |- _ =>
      first [ exact (HΦ Hb)
            | exact (wadm_filter_set_reg _ _ _ _ _ _ _ (HΦ Hb))
            | exact (wadm_filter_set_dev _ _ _ _ _ _ _ (HΦ Hb))
            | exact (wadm_filter_read_post _ _ _ _ _ _ _ _ (HΦ Hb))
            | exact (wadm_filter_set_ws _ _ _ _ _ _ (barrier_post_le _ _) (HΦ Hb)) ]
  end.

(* ====================================================================== *)
(** ** 4. THE BRIDGE, consumption direction

    Over [WeakInterp.wrun] — the RELATIONAL interpreter — because that is what
    [WeakExec.wp_wrun_step]'s continuation hands a leaf, and because a racy
    read has no oracle-free description to hand back.

    First the window-free phase: with the racy read behind (or never taken),
    the run is on the pinned fragment away from the window, and the patched
    memory is carried through unchanged — a disjoint read does not see it and
    a disjoint write commutes with it. *)

Lemma exec_of_wrun_win tid ra rn rak Φ (w : bv (8 * rn)) {X} (m : M X) :
  acc_wf ra rn ->
  forall s, wstep_ok_racy tid ra rn rak Φ false m s -> wlog_wf (wm_log s) ->
  forall x s', wrun tid m s x s' ->
    exec m (wpatch_st s ra rn w) = Some (x, wpatch_st s' ra rn w) /\
    wlog_wf (wm_log s').
Proof.
  intros Hracc.
  induction m as [y|T oc k IH]; intros s Hok Hwf x s' Hrun.
  - destruct Hrun as [-> ->]. by split.
  - destruct oc; simpl in Hok, Hrun |- *;
      try (exact (IH _ _ Hok Hwf _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ _ (Hok w0 d' eq_refl) Hwf _ _ Hrun).
      * destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hb & _)]);
          [|discriminate].
        destruct Hrun as (w0 & ts & Hokr & Hrun).
        pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin Hokr) as Hts.
        rewrite Hts in Hokr, Hrun.
        pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
        destruct (IH _ _ (Hk w0 Hrb) (wlog_wf_read_post _ _ _ _ Hwf) _ _ Hrun)
          as [Hex Hwf'].
        rewrite wpatch_st_read_post in Hex.
        rewrite (read_bytes_patch_disj
                   (wflat (wm_img s) (wm_log s)) ra rn w _ _ Hracc Hacc Hdisj).
        rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hrb.
        rewrite Hrb. by split.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ _ (Hok d' eq_refl) Hwf _ _ Hrun).
      * destruct Hok as (_ & Hacc & Hdisj & Hok).
        destruct (IH _ _ Hok (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) _ _ Hrun)
          as [Hex Hwf'].
        rewrite (wpatch_st_write_post _ s ra rn w _ _ n _ Hracc Hacc Hdisj)
          in Hex.
        by split.
Qed.

(** THE BRIDGE THEOREM, in the form the induction wants: the admissibility of
    the racy value is reported at the state [s0] the WHOLE step started in,
    while the run is at an intermediate state [s] that differs from it only in
    views.  (That is what the "no RAM write before the racy read" restriction
    buys: the transport of §3 has no side conditions.) *)
Lemma exec_of_wrun_racy_gen tid ra rn rak Φ {X} (m : M X) :
  acc_wf ra rn ->
  forall (s0 s : wmstate),
    wadm_filter s0 rak ra rn Φ ->
    wstep_ok_racy tid ra rn rak Φ true m s ->
    wm_img s = wm_img s0 -> wm_log s = wm_log s0 -> ws_le (wm_ws s0) (wm_ws s) ->
    wlog_wf (wm_log s) ->
    is_Some (wread_bytes s0 rak ra rn (coh_ts s0 ra rn)) ->
  forall x s', wrun tid m s x s' ->
    exists w : bv (8 * rn),
      wadm s0 rak ra rn w /\
      exec m (wpatch_st s ra rn w) = Some (x, wpatch_st s' ra rn w) /\
      wlog_wf (wm_log s').
Proof.
  intros Hracc.
  induction m as [y|T oc k IH];
    intros s0 s HΦ Hok Himg Hlog Hle Hwf Hrd x s' Hrun.
  - (* the run never took the racy read: the CANONICAL word serves *)
    destruct Hrun as [-> ->]. destruct Hrd as [w0 Hw0].
    exists w0. split_and!; [|reflexivity|exact Hwf].
    exact (wadm_of_wread_ok _ _ _ _ _ _ (wread_bytes_spec _ _ _ _ _ _ Hw0)).
  - destruct oc; simpl in Hok, Hrun |- *;
      try (exact (IH _ s0 _ HΦ Hok Himg Hlog Hle Hwf Hrd _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ s0 _ HΦ (Hok w0 d' eq_refl) Himg Hlog Hle Hwf Hrd _ _ Hrun).
      * destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(_ & Hpa & Hn & Hak & Hk)]).
        -- (* a pinned read away from the window *)
           destruct Hrun as (w0 & ts & Hokr & Hrun).
           pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin Hokr) as Hts.
           rewrite Hts in Hokr, Hrun.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           destruct (IH _ s0 _ HΦ (Hk w0 Hrb)
                       ltac:(etrans; [apply wread_post_img|exact Himg])
                       ltac:(etrans; [apply wread_post_log|exact Hlog])
                       ltac:(etrans; [exact Hle|apply wread_post_ws_le])
                       (wlog_wf_read_post _ _ _ _ Hwf) Hrd _ _ Hrun)
             as (w & Hadm & Hex & Hwf').
           exists w. rewrite wpatch_st_read_post in Hex.
           rewrite (read_bytes_patch_disj
                      (wflat (wm_img s) (wm_log s)) ra rn w _ _
                      Hracc Hacc Hdisj).
           rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hrb.
           rewrite Hrb. split_and!; [exact Hadm|exact Hex|exact Hwf'].
        -- (* THE RACY READ *)
           subst n. rewrite Hpa in Hacc Hk |- *. rewrite Hak in Hk.
           destruct Hrun as (w0 & ts & Hokr & Hrun).
           rewrite Hpa Hak in Hokr, Hrun.
           exists w0.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           (* the filter is discharged at the PRE-state, which is what
              [wadm_down] transports the admissibility to *)
           assert (Hadm0 : wadm s0 rak ra rn w0).
           { eapply wadm_down; [exact Himg|exact Hlog|exact Hle|].
             exact (wadm_of_wread_ok _ _ _ _ _ _ Hokr). }
           destruct (exec_of_wrun_win tid ra rn rak Φ w0 _ Hracc _
                       (Hk ts w0 Hrb (HΦ w0 Hadm0))
                       (wlog_wf_read_post _ _ _ _ Hwf) _ _ Hrun)
             as [Hex Hwf'].
           rewrite wpatch_st_read_post in Hex.
           rewrite /wpatch_st /=.
           rewrite (read_bytes_of_bytes
                      (write_bytes (wflat (wm_img s) (wm_log s)) ra rn w0)
                      ra rn w0
                      (fun j Hj => write_bytes_lookup_at
                                     (wflat (wm_img s) (wm_log s)) ra rn w0 j
                                     Hracc Hj)).
           split_and!; [exact Hadm0|exact Hex|exact Hwf'].
    + (* MemWrite: forbidden before the racy read *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ s0 _ HΦ (Hok d' eq_refl) Himg Hlog Hle Hwf Hrd _ _ Hrun).
      * destruct Hok as (Hb & _). discriminate.
    + (* Barrier *)
      refine (IH tt s0 _ HΦ Hok Himg Hlog _ Hwf Hrd _ _ Hrun).
      etrans; [exact Hle|apply barrier_post_le].
Qed.

(** THE BRIDGE THEOREM.  Read it as: whatever the racy run did, there is a
    word [w] — admissible for the window in the PRE-state, byte by byte — such
    that the whole step IS the SC run over the flat memory PATCHED at the
    window with it. *)
Lemma exec_of_wrun_racy tid ra rn rak Φ {X} (m : M X) :
  acc_wf ra rn ->
  forall s, wadm_filter s rak ra rn Φ -> wlog_wf (wm_log s) ->
    is_Some (wread_bytes s rak ra rn (coh_ts s ra rn)) ->
    wstep_ok_racy tid ra rn rak Φ true m s ->
  forall x s', wrun tid m s x s' ->
    exists w : bv (8 * rn),
      wadm s rak ra rn w /\
      exec m (wpatch_st s ra rn w) = Some (x, wpatch_st s' ra rn w) /\
      wlog_wf (wm_log s').
Proof.
  intros Hracc s HΦ Hwf Hrd Hok x s' Hrun.
  exact (exec_of_wrun_racy_gen tid ra rn rak Φ m Hracc s s HΦ Hok eq_refl
           eq_refl (reflexivity _) Hwf Hrd x s' Hrun).
Qed.

(* ====================================================================== *)
(** ** 4b. THE GAIN: the racy read's VIEW content, taken from the model

    [wadm] says WHICH byte values the run could have returned.  It does not
    say at which timestamp, and a handoff needs exactly that: the fence that
    cashes a receipt consumes [t ≤ w_vrOld], "the timestamp I read is under my
    read floor".  That pairing used to be a per-instruction PREMISE
    ([WkStartedLoad.wstarted_gain], porting guide §2c) because
    [wracy_cert]'s [Q] is a relation on STATES and cannot name the word the
    load returned.

    It does not have to be.  The bridge's own induction knows the timestamp
    list the racy read took — [wread_ok]'s [ts] — and [WeakMem]'s read step
    puts it under [w_vrOld] on the spot ([load_post_run_vrOld]); every later
    step only raises the floor ([WeakInterp.wrun_ws_le]).  So the gain comes
    out of the SAME traversal that produces [wadm], under one side condition
    that is about the READER and not about the instruction: the hart has not
    stored to the window, so its read is not FORWARDED (a forwarded load takes
    the view the store banked, not the timestamp — [WeakMem.fwd_view]).

    WHAT IS LEFT FOR THE LEAF is the one thing a generic traversal cannot
    know: whether the run took the racy read at all.  A run that never touches
    the window is patch-INDEPENDENT — it produces the same answer for every
    word one writes there — and that is the second disjunct below, in the
    shape that refutes itself at any load: the destination register would have
    to hold every word at once. *)

(** The window is not in this hart's forward bank.  Implied by "this hart has
    never stored to the window"; for a secondary hart waiting on [started],
    which only ever reads the flag, it is immediate. *)
Definition wunwritten (ws : wstate) (ra : Arch.pa) (rn : N) : Prop :=
  forall j : nat, (j < N.to_nat rn)%nat -> w_fwd ws !! (acc_addr ra j) = None.

(** [wadm] with the timestamps pinned under the SUCCESSOR's read floor. *)
Definition wgain (s0 s' : wmstate) (rak : akinfo) (ra : Arch.pa) (rn : N)
    (w : bv (8 * rn)) : Prop :=
  forall j : nat, (j < N.to_nat rn)%nat ->
    exists t : nat, wbyte_ok s0 rak (acc_addr ra j) t (nth_byte w j) /\
                    (t <= w_vrOld (wm_ws s'))%nat.

Lemma wgain_wadm s0 s' rak ra rn (w : bv (8 * rn)) :
  wgain s0 s' rak ra rn w -> wadm s0 rak ra rn w.
Proof. intros Hg j Hj. destruct (Hg j Hj) as (t & Hok & _). by exists t. Qed.

Lemma wgain_mono s0 s' s'' rak ra rn (w : bv (8 * rn)) :
  ws_le (wm_ws s') (wm_ws s'') ->
  wgain s0 s' rak ra rn w -> wgain s0 s'' rak ra rn w.
Proof.
  intros Hle Hg j Hj. destruct (Hg j Hj) as (t & Hok & Ht).
  exists t. split; [exact Hok|]. destruct Hle as (_ & Hold & _). lia.
Qed.

(** The forward bank is untouched by everything the pre-racy phase may do. *)
Lemma wread_post_fwd s ak pa ts :
  w_fwd (wm_ws (wread_post s ak pa ts)) = w_fwd (wm_ws s).
Proof.
  rewrite /wread_post. destruct (ak_coh ak); [done|]. apply load_post_run_fwd.
Qed.

Lemma barrier_post_fwd ws b : w_fwd (barrier_post ws b) = w_fwd ws.
Proof. by destruct b. Qed.

(** THE READ STEP'S OWN GAIN, at the fold the interpreter builds. *)
Lemma wread_post_vrOld (s : wmstate) (ak : akinfo) (pa : Arch.pa) (n : N)
    (ts : list nat) (j : nat) :
  ak_coh ak = false ->
  wunwritten (wm_ws s) pa n ->
  length ts = N.to_nat n ->
  (j < N.to_nat n)%nat ->
  (ts !!! j <= w_vrOld (wm_ws (wread_post s ak pa ts)))%nat.
Proof.
  intros Hcoh Hun Hlen Hj. rewrite /wread_post Hcoh /=.
  apply load_post_run_vrOld; [lia|]. exact (Hun j Hj).
Qed.

(** THE STRENGTHENED BRIDGE.  [exec_of_wrun_racy_gen] with the gain threaded
    through the induction, and the patch-independence escape hatch for a run
    that never read the window. *)
Lemma exec_of_wrun_gain_gen tid ra rn rak Φ {X} (m : M X) :
  acc_wf ra rn ->
  ak_coh rak = false ->
  forall (s0 s : wmstate),
    wadm_filter s0 rak ra rn Φ ->
    wstep_ok_racy tid ra rn rak Φ true m s ->
    wm_img s = wm_img s0 -> wm_log s = wm_log s0 -> ws_le (wm_ws s0) (wm_ws s) ->
    w_fwd (wm_ws s) = w_fwd (wm_ws s0) ->
    wunwritten (wm_ws s0) ra rn ->
    wlog_wf (wm_log s) ->
    is_Some (wread_bytes s0 rak ra rn (coh_ts s0 ra rn)) ->
  forall x s', wrun tid m s x s' ->
    exists w : bv (8 * rn),
      wadm s0 rak ra rn w /\
      exec m (wpatch_st s ra rn w) = Some (x, wpatch_st s' ra rn w) /\
      wlog_wf (wm_log s') /\
      (wgain s0 s' rak ra rn w \/
       forall u : bv (8 * rn),
         exec m (wpatch_st s ra rn u) = Some (x, wpatch_st s' ra rn u)).
Proof.
  intros Hracc Hakc.
  induction m as [y|T oc k IH];
    intros s0 s HΦ Hok Himg Hlog Hle Hfwd Hun Hwf Hrd x s' Hrun.
  - (* the run never took the racy read: the CANONICAL word serves, and the
       whole step is patch-independent *)
    destruct Hrun as [-> ->]. destruct Hrd as [w0 Hw0].
    exists w0. split_and!; [|reflexivity|exact Hwf|right; reflexivity].
    exact (wadm_of_wread_ok _ _ _ _ _ _ (wread_bytes_spec _ _ _ _ _ _ Hw0)).
  - destruct oc; simpl in Hok, Hrun |- *;
      try (exact (IH _ s0 _ HΦ Hok Himg Hlog Hle Hfwd Hun Hwf Hrd _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ s0 _ HΦ (Hok w0 d' eq_refl) Himg Hlog Hle Hfwd Hun Hwf Hrd
                 _ _ Hrun).
      * destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(_ & Hpa & Hn & Hak & Hk)]).
        -- (* a pinned read away from the window *)
           destruct Hrun as (w0 & ts & Hokr & Hrun).
           pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin Hokr) as Hts.
           rewrite Hts in Hokr, Hrun.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           destruct (IH _ s0 _ HΦ (Hk w0 Hrb)
                       ltac:(etrans; [apply wread_post_img|exact Himg])
                       ltac:(etrans; [apply wread_post_log|exact Hlog])
                       ltac:(etrans; [exact Hle|apply wread_post_ws_le])
                       ltac:(etrans; [apply wread_post_fwd|exact Hfwd])
                       Hun (wlog_wf_read_post _ _ _ _ Hwf) Hrd _ _ Hrun)
             as (w & Hadm & Hex & Hwf' & Hdisj').
           exists w. rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hrb.
           split_and!; [exact Hadm| |exact Hwf'|].
           { rewrite wpatch_st_read_post in Hex.
             rewrite (read_bytes_patch_disj
                        (wflat (wm_img s) (wm_log s)) ra rn w _ _
                        Hracc Hacc Hdisj) Hrb. exact Hex. }
           destruct Hdisj' as [Hg|Huni]; [by left|right].
           intros u. specialize (Huni u).
           rewrite wpatch_st_read_post in Huni.
           rewrite (read_bytes_patch_disj
                      (wflat (wm_img s) (wm_log s)) ra rn u _ _
                      Hracc Hacc Hdisj) Hrb. exact Huni.
        -- (* THE RACY READ — and this is where the gain is minted *)
           subst n. rewrite Hpa in Hacc Hk |- *. rewrite Hak in Hk.
           destruct Hrun as (w0 & ts & Hokr & Hrun).
           rewrite Hpa Hak in Hokr, Hrun.
           exists w0.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           assert (Hadm0 : wadm s0 rak ra rn w0).
           { eapply wadm_down; [exact Himg|exact Hlog|exact Hle|].
             exact (wadm_of_wread_ok _ _ _ _ _ _ Hokr). }
           destruct (exec_of_wrun_win tid ra rn rak Φ w0 _ Hracc _
                       (Hk ts w0 Hrb (HΦ w0 Hadm0))
                       (wlog_wf_read_post _ _ _ _ Hwf) _ _ Hrun)
             as [Hex Hwf'].
           rewrite wpatch_st_read_post in Hex.
           rewrite /wpatch_st /=.
           rewrite (read_bytes_of_bytes
                      (write_bytes (wflat (wm_img s) (wm_log s)) ra rn w0)
                      ra rn w0
                      (fun j Hj => write_bytes_lookup_at
                                     (wflat (wm_img s) (wm_log s)) ra rn w0 j
                                     Hracc Hj)).
           split_and!; [exact Hadm0|exact Hex|exact Hwf'|left].
           (* the timestamps the read took are under the successor's floor *)
           destruct Hokr as [Hlen Hbytes].
           eapply (wgain_mono s0 (wread_post s rak ra ts) s');
             [exact (wrun_ws_le _ _ _ _ _ Hrun)|].
           intros j Hj. exists (ts !!! j). split.
           ++ eapply wbyte_ok_down; [exact Himg|exact Hlog|exact Hle|].
              apply Hbytes. lia.
           ++ exact (wread_post_vrOld s rak ra rn ts j Hakc
                       (fun i Hi => eq_trans (f_equal (fun mm => mm !! acc_addr ra i)
                                                Hfwd) (Hun i Hi))
                       Hlen Hj).
    + (* MemWrite: forbidden before the racy read *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ s0 _ HΦ (Hok d' eq_refl) Himg Hlog Hle Hfwd Hun Hwf Hrd
                 _ _ Hrun).
      * destruct Hok as (Hb & _). discriminate.
    + (* Barrier *)
      refine (IH tt s0 _ HΦ Hok Himg Hlog _ _ Hun Hwf Hrd _ _ Hrun).
      * etrans; [exact Hle|apply barrier_post_le].
      * etrans; [apply barrier_post_fwd|exact Hfwd].
Qed.

Lemma exec_of_wrun_gain tid ra rn rak Φ {X} (m : M X) :
  acc_wf ra rn ->
  ak_coh rak = false ->
  forall s, wadm_filter s rak ra rn Φ -> wlog_wf (wm_log s) ->
    is_Some (wread_bytes s rak ra rn (coh_ts s ra rn)) ->
    wunwritten (wm_ws s) ra rn ->
    wstep_ok_racy tid ra rn rak Φ true m s ->
  forall x s', wrun tid m s x s' ->
    exists w : bv (8 * rn),
      wadm s rak ra rn w /\
      exec m (wpatch_st s ra rn w) = Some (x, wpatch_st s' ra rn w) /\
      wlog_wf (wm_log s') /\
      (wgain s s' rak ra rn w \/
       forall u : bv (8 * rn),
         exec m (wpatch_st s ra rn u) = Some (x, wpatch_st s' ra rn u)).
Proof.
  intros Hracc Hakc s HΦ Hwf Hrd Hun Hok x s' Hrun.
  exact (exec_of_wrun_gain_gen tid ra rn rak Φ m Hracc Hakc s s HΦ Hok eq_refl
           eq_refl (reflexivity _) eq_refl Hun Hwf Hrd x s' Hrun).
Qed.

(* ====================================================================== *)
(** ** 5. Reducibility, and the [wexec_covers] mirror

    [WeakExec.wp_wrun_step] asks for ONE witness that the weak machine can
    step, and it asks for it at [wexec].  It is obtained at the CANONICAL
    (latest) value of the window — which IS pinned, whatever the hart's index
    — so the caller's ORDINARY [exec] fact about [WeakBridge.wflat_st σ]
    serves, exactly as it does for [WeakInstr.wp_winstr]. *)

Lemma wexec_of_exec_racy tid ra rn rak Φ {X} (m : M X) :
  acc_wf ra rn ->
  forall b s, wstep_ok_racy tid ra rn rak Φ b m s -> wlog_wf (wm_log s) ->
    (b = true -> wadm_filter s rak ra rn Φ) ->
  forall x t', exec m (wflat_st s) = Some (x, t') ->
    exists χ s' χ', wexec tid m χ s = Some (x, s', χ') /\ wflat_st s' = t'.
Proof.
  intros Hracc.
  induction m as [y|T oc k IH]; intros b s Hok Hwf HΦ x t' Hex.
  - simpl in Hex. injection Hex as <- <-. by exists [], s, [].
  - destruct oc; simpl in Hok, Hex; try discriminate;
      try (exact (IH _ _ _ Hok Hwf ltac:(filt_step) _ _ Hex));
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        destruct (IH _ _ _ (Hok w0 d' eq_refl) Hwf ltac:(filt_step) _ _ Hex)
          as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd Hdr.
      * destruct (read_bytes _ _ _) as [w0|] eqn:Hrd; [|discriminate].
        destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hbt & Hpa & Hn & Hak & Hk)]).
        -- lazymatch type of Hpin with
           | ak_pins ?ak0 = false -> _ =>
               pose proof (wread_bytes_read_bytes s ak0 _ _ Hwf Hacc) as Heqrb
           end.
           rewrite Hrd in Heqrb.
           pose proof (Hk w0 Heqrb) as Hp2.
           lazymatch type of Hp2 with
           | wstep_ok_racy _ _ _ _ _ _ _ ?sr =>
               assert (Hex2 : exec (k (inl (w0, None))) (wflat_st sr)
                              = Some (x, t'))
                 by (rewrite wflat_st_read_post; exact Hex)
           end.
           destruct (IH _ _ _ Hp2 (wlog_wf_read_post _ _ _ _ Hwf)
                       ltac:(filt_step) _ _ Hex2)
             as (χ & s2 & χ' & Hw & Heq).
           lazymatch type of Hpin with
           | ak_pins ?ak0 = false -> _ => destruct (ak_coh ak0) eqn:Hcoh
           end.
           ++ exists χ, s2, χ'. split; [|exact Heq].
              simpl. rewrite Hd Hcoh Heqrb. exact Hw.
           ++ lazymatch type of Heqrb with
              | wread_bytes _ _ _ _ ?ts0 = _ => exists (ts0 :: χ), s2, χ'
              end.
              split; [|exact Heq]. simpl. rewrite Hd Hcoh Heqrb. exact Hw.
        -- subst n. rewrite Hpa in Hacc Hk Hrd. rewrite Hak in Hk.
           pose proof (wread_bytes_read_bytes s rak ra rn Hwf Hacc) as Heqrb.
           rewrite Hrd in Heqrb.
           (* the CANONICAL word is admissible, so the filter accepts it *)
           pose proof (Hk (coh_ts s ra rn) w0 Heqrb
                        (HΦ Hbt w0
                           (wadm_of_wread_ok _ _ _ _ _ _
                              (wread_bytes_spec _ _ _ _ _ _ Heqrb)))) as Hp2.
           lazymatch type of Hp2 with
           | wstep_ok_racy _ _ _ _ _ _ _ ?sr =>
               assert (Hex2 : exec (k (inl (w0, None))) (wflat_st sr)
                              = Some (x, t'))
                 by (rewrite wflat_st_read_post; exact Hex)
           end.
           destruct (IH _ _ _ Hp2 (wlog_wf_read_post _ _ _ _ Hwf)
                       ltac:(intros ?; discriminate) _ _ Hex2)
             as (χ & s2 & χ' & Hw & Heq).
           destruct (ak_coh rak) eqn:Hcoh.
           ++ exists χ, s2, χ'. split; [|exact Heq].
              simpl. rewrite Hd Hak Hpa Hcoh Heqrb. exact Hw.
           ++ exists (coh_ts s ra rn :: χ), s2, χ'. split; [|exact Heq].
              simpl. rewrite Hd Hak Hpa Hcoh Heqrb. exact Hw.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        destruct (IH _ _ _ (Hok d' eq_refl) Hwf ltac:(filt_step) _ _ Hex)
          as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd Hdw.
      * destruct Hok as (Hbf & Hacc & _ & Hok).
        lazymatch type of Hok with
        | wstep_ok_racy _ _ _ _ _ _ _ ?sw =>
            assert (Hex2 : exec (k (inl None)) (wflat_st sw) = Some (x, t'))
              by (rewrite wflat_st_write_post; exact Hex)
        end.
        destruct (IH _ _ _ Hok (wflat_write_wf _ _ _ _ _ _ Hwf Hacc)
                    ltac:(intros ?; congruence) _ _ Hex2)
          as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd.
Qed.

(** The [wexec_covers] mirror: every relational successor of a racy run is a
    functional one at SOME oracle.  Same argument as [WeakExec.wrun_wexec] —
    a racy read is accepted at whatever timestamps the run chose, and a
    coherent one is pinned by [wread_coh_ts]. *)
Lemma wrun_wexec_racy tid ra rn rak Φ {X} (m : M X) :
  forall b s, wstep_ok_racy tid ra rn rak Φ b m s ->
    (b = true -> wadm_filter s rak ra rn Φ) ->
  forall x s', wrun tid m s x s' ->
    exists χ χ', wexec tid m χ s = Some (x, s', χ').
Proof.
  induction m as [y|T oc k IH]; intros b s Hok HΦ x s' Hrun.
  - destruct Hrun as [-> ->]. by exists [], [].
  - destruct oc; simpl in Hok, Hrun;
      try (exact (IH _ _ _ Hok ltac:(filt_step) _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        destruct (IH _ _ _ (Hok w0 d' eq_refl) ltac:(filt_step) _ _ Hrun)
          as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdr. exact Hex.
      * destruct Hrun as (w0 & ts & Hokr & Hrun).
        destruct Hok as (Hacc & [(Hdisj & Hpin & Hk)|(Hbt & Hpa & Hn & Hak & Hk)]).
        -- pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin Hokr) as Hts.
           rewrite Hts in Hokr, Hrun.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           destruct (IH _ _ _ (Hk w0 Hrb) ltac:(filt_step) _ _ Hrun)
             as (χ & χ' & Hex).
           lazymatch type of Hpin with
           | ak_pins ?ak0 = false -> _ => destruct (ak_coh ak0) eqn:Hcoh
           end.
           ++ exists χ, χ'. simpl. rewrite Hd Hcoh Hrb. exact Hex.
           ++ lazymatch type of Hrb with
              | wread_bytes _ _ _ _ ?ts0 = _ => exists (ts0 :: χ), χ'
              end.
              simpl. rewrite Hd Hcoh Hrb. exact Hex.
        -- subst n. rewrite Hpa in Hacc Hk. rewrite Hak in Hk.
           rewrite Hpa Hak in Hokr, Hrun.
           pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
           (* the word the run actually read is admissible, so the filter
              accepts it *)
           destruct (IH _ _ _
                       (Hk ts w0 Hrb
                          (HΦ Hbt w0 (wadm_of_wread_ok _ _ _ _ _ _ Hokr)))
                       ltac:(intros ?; discriminate) _ _ Hrun)
             as (χ & χ' & Hex).
           destruct (ak_coh rak) eqn:Hcoh.
           ++ pose proof (wread_coh_ts _ _ _ _ _ _ Hcoh Hokr) as Hts.
              exists χ, χ'. simpl. rewrite Hd Hak Hpa Hcoh -Hts Hrb. exact Hex.
           ++ exists (ts :: χ), χ'. simpl.
              rewrite Hd Hak Hpa Hcoh Hrb. exact Hex.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        destruct (IH _ _ _ (Hok d' eq_refl) ltac:(filt_step) _ _ Hrun)
          as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdw. exact Hex.
      * destruct Hok as (Hbf & _ & _ & Hok).
        destruct (IH _ _ _ Hok ltac:(intros ?; congruence) _ _ Hrun)
          as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd. exact Hex.
Qed.

(* ====================================================================== *)
(** ** 6. THE RULE

    [WeakInstr.wp_winstr]'s racy twin, over [WeakExec.wp_wrun_step].  The
    certificate is [wracy_cert], the exact analogue of
    [WeakInstr.wstep_cert] with [wstep_ok] replaced by [wstep_ok_racy]; its
    [Q] half is unchanged in shape and in meaning, so [WeakCert]'s trace
    machinery applies to it verbatim.

    WHAT THE CALLER SUPPLIES ABOUT MEMORY, and why it is not the racy value:

      - [is_Some (read_bytes (wflat …) ra rn)] — the window is IN memory.  Any
        owner of the four bytes (the escrow's elements, a [wpt4]) has this;
      - ONE ordinary [exec] fact about [WeakBridge.wflat_st σ], i.e. at the
        COHERENT value of the window.  That is the reducibility witness, and
        it is exactly what the caller already proves today.

    WHAT THE CALLER GETS BACK is the racy word [w], its per-byte
    admissibility, and the step described as an [exec] over
    [wpatch_st σ ra rn w] — from which its own library lemma identifies every
    register, the device state and the memory by [exec]'s functionality. *)

Definition wstep_post_racy (σ σ' : wmstate) : Prop :=
  wm_img σ' = wm_img σ /\
  (exists l, wm_log σ' = (wm_log σ ++ l)%list) /\
  ws_le (wm_ws σ) (wm_ws σ') /\
  wlog_wf (wm_log σ') /\
  ws_bounded (wm_ws σ') (length (wm_log σ')).

Definition wracy_cert (cid : nat) (pc : SailStdpp.Values.mword 64)
    (ra : Arch.pa) (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop)
    (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) : Prop :=
  forall (σ : wmstate) (tick : bool),
    register_lookup PC (wm_regs σ) = pc ->
    acc_wf pc 4 ->
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)) ->
    P σ ->
    wstep_ok_racy (Some cid) ra rn rak Φ true (riscv_step tick) σ /\
    (forall χ σ' χ',
       wexec (Some cid) (riscv_step tick) χ σ = Some (tt, σ', χ') ->
       Q σ σ').

Section rule.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_wracy_load (pc : SailStdpp.Values.mword 64)
      (ra : Arch.pa) (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop)
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    acc_wf ra rn ->
    wracy_cert (fin_to_nat cpu_id) pc ra rn rak Φ P Q ->
    (* φ-upgrade, deliverable A: THE RACY WINDOW IS SYNC.  Persistent, and
       not consumed by the proof below — it is what §C's violation-freedom
       preservation reads at this rule ([WeakGhost.wcds_sync]: a sync byte
       carries no [WCplain] message at all, so a racy read of it can observe
       no unpublished owned store), and it is stated here so that the rule's
       INTERFACE already carries the obligation. *)
    sync_win ra rn -∗
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ⌜wadm_filter σ rak ra rn Φ⌝ ∗
       ⌜is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) ra rn)⌝ ∗
       (∃ t0 : mstate,
          ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝) ∗
       ▷ (∀ (tick : bool) (σ' : wmstate) (w : bv (8 * rn)),
            ⌜wadm σ rak ra rn w⌝ -∗
            ⌜exec (riscv_step tick) (wpatch_st σ ra rn w)
             = Some (tt, wpatch_st σ' ra rn w)⌝ -∗
            ⌜wstep_post_racy σ σ'⌝ -∗
            ⌜Q σ σ'⌝
            ={∅,⊤}=∗ wmstate_interp σ' ∗
                     WWP Loop)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hracc Hcert) "#Hsync H".
    iApply (wp_wrun_step with "[H]"); [exact Hgid|].
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(%Hbnd & %Hwf & Hrest)".
    iMod ("H" $! σ with "[Hrest]")
      as "(%Hpc & %Htext & %HP & %HΦ & %Hrd & Ht0 & Hk)".
    { rewrite /wmstate_interp.
      iSplitR; [iPureIntro; exact Hbnd|].
      iSplitR; [iPureIntro; exact Hwf|]. iExact "Hrest". }
    iDestruct "Ht0" as (t0) "%Hex0".
    assert (Hc : ∀ tick : bool,
              wstep_ok_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ true
                (riscv_step tick) σ ∧
              (∀ χ σ' χ',
                 wexec (Some (fin_to_nat cpu_id)) (riscv_step tick) χ σ
                 = Some (tt, σ', χ') → Q σ σ'))
      by (intros tick; exact (Hcert σ tick Hpc Haccpc Htext HP)).
    (* the window's coherent word — the pinned value, which is what the
       reducibility witness is taken at *)
    assert (Hcoh : is_Some (wread_bytes σ rak ra rn (coh_ts σ ra rn))).
    { rewrite (wread_bytes_read_bytes σ rak ra rn Hwf Hracc). exact Hrd. }
    iModIntro.
    iSplitR.
    { iPureIntro.
      destruct (wexec_of_exec_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ
                  (riscv_step false) Hracc true σ (proj1 (Hc false)) Hwf
                  (fun _ => HΦ) tt t0 Hex0) as (χ & σ0 & χ' & Hw & _).
      by exists χ, σ0, χ'. }
    iNext. iIntros (tick σ' Hrun).
    destruct (exec_of_wrun_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ
                (riscv_step tick) Hracc σ HΦ Hwf Hcoh (proj1 (Hc tick))
                tt σ' Hrun) as (w & Hadm & Hex & Hwf').
    destruct (wrun_wexec_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ
                (riscv_step tick) true σ (proj1 (Hc tick)) (fun _ => HΦ)
                tt σ' Hrun) as (χ & χ' & Hwex).
    iApply ("Hk" $! tick σ' w with "[%] [%] [%] [%]").
    - exact Hadm.
    - exact Hex.
    - rewrite /wstep_post_racy. split_and!.
      + exact (wrun_img _ _ _ _ _ Hrun).
      + exact (wrun_log_app _ _ _ _ _ Hrun).
      + exact (wrun_ws_le _ _ _ _ _ Hrun).
      + exact Hwf'.
      + exact (wrun_ws_bounded _ _ _ _ _ Hrun Hbnd).
    - exact (proj2 (Hc tick) χ σ' χ' Hwex).
  Qed.

  (** THE SAME RULE WITH THE VIEW GAIN ATTACHED (§4b).

      Two premises more than [wp_wracy_load], both about the READER rather
      than about the instruction: the access is not a coherent-tier one
      ([ak_coh rak = false] — a fetch/walker read moves no view, so there is
      nothing to gain), and the hart has not stored to the window
      ([wunwritten], supplied per state by the caller's own callback, exactly
      like the pinnedness facts).

      One conclusion more: besides the racy word and its admissibility, the
      continuation is told that either the timestamps behind that word are
      under the successor's read floor — which is what a fence cashes — or the
      step never looked at the window at all.  A leaf kills the second arm
      with [wreads_win]. *)
  Lemma wp_wracy_load_gain (pc : SailStdpp.Values.mword 64)
      (ra : Arch.pa) (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop)
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    acc_wf ra rn ->
    ak_coh rak = false ->
    wracy_cert (fin_to_nat cpu_id) pc ra rn rak Φ P Q ->
    (* φ-upgrade, deliverable A — see [wp_wracy_load]. *)
    sync_win ra rn -∗
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ⌜wunwritten (wm_ws σ) ra rn⌝ ∗
       ⌜wadm_filter σ rak ra rn Φ⌝ ∗
       ⌜is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) ra rn)⌝ ∗
       (∃ t0 : mstate,
          ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝) ∗
       ▷ (∀ (tick : bool) (σ' : wmstate) (w : bv (8 * rn)),
            ⌜wadm σ rak ra rn w⌝ -∗
            ⌜exec (riscv_step tick) (wpatch_st σ ra rn w)
             = Some (tt, wpatch_st σ' ra rn w)⌝ -∗
            ⌜wstep_post_racy σ σ'⌝ -∗
            ⌜Q σ σ'⌝ -∗
            ⌜wgain σ σ' rak ra rn w ∨
             ∀ u : bv (8 * rn),
               exec (riscv_step tick) (wpatch_st σ ra rn u)
               = Some (tt, wpatch_st σ' ra rn u)⌝
            ={∅,⊤}=∗ wmstate_interp σ' ∗
                     WWP Loop)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hracc Hakc Hcert) "#Hsync H".
    iApply (wp_wrun_step with "[H]"); [exact Hgid|].
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(%Hbnd & %Hwf & Hrest)".
    iMod ("H" $! σ with "[Hrest]")
      as "(%Hpc & %Htext & %HP & %Hun & %HΦ & %Hrd & Ht0 & Hk)".
    { rewrite /wmstate_interp.
      iSplitR; [iPureIntro; exact Hbnd|].
      iSplitR; [iPureIntro; exact Hwf|]. iExact "Hrest". }
    iDestruct "Ht0" as (t0) "%Hex0".
    assert (Hc : ∀ tick : bool,
              wstep_ok_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ true
                (riscv_step tick) σ ∧
              (∀ χ σ' χ',
                 wexec (Some (fin_to_nat cpu_id)) (riscv_step tick) χ σ
                 = Some (tt, σ', χ') → Q σ σ'))
      by (intros tick; exact (Hcert σ tick Hpc Haccpc Htext HP)).
    assert (Hcoh : is_Some (wread_bytes σ rak ra rn (coh_ts σ ra rn))).
    { rewrite (wread_bytes_read_bytes σ rak ra rn Hwf Hracc). exact Hrd. }
    iModIntro.
    iSplitR.
    { iPureIntro.
      destruct (wexec_of_exec_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ
                  (riscv_step false) Hracc true σ (proj1 (Hc false)) Hwf
                  (fun _ => HΦ) tt t0 Hex0) as (χ & σ0 & χ' & Hw & _).
      by exists χ, σ0, χ'. }
    iNext. iIntros (tick σ' Hrun).
    destruct (exec_of_wrun_gain (Some (fin_to_nat cpu_id)) ra rn rak Φ
                (riscv_step tick) Hracc Hakc σ HΦ Hwf Hcoh Hun
                (proj1 (Hc tick)) tt σ' Hrun) as (w & Hadm & Hex & Hwf' & Hg).
    destruct (wrun_wexec_racy (Some (fin_to_nat cpu_id)) ra rn rak Φ
                (riscv_step tick) true σ (proj1 (Hc tick)) (fun _ => HΦ)
                tt σ' Hrun) as (χ & χ' & Hwex).
    iApply ("Hk" $! tick σ' w with "[%] [%] [%] [%] [%]").
    - exact Hadm.
    - exact Hex.
    - rewrite /wstep_post_racy. split_and!.
      + exact (wrun_img _ _ _ _ _ Hrun).
      + exact (wrun_log_app _ _ _ _ _ Hrun).
      + exact (wrun_ws_le _ _ _ _ _ Hrun).
      + exact Hwf'.
      + exact (wrun_ws_bounded _ _ _ _ _ Hrun Hbnd).
    - exact (proj2 (Hc tick) χ σ' χ' Hwex).
    - exact Hg.
  Qed.

End rule.

(** THE LEAF-SIDE REFUTATION of the patch-independence arm: "this step READS
    the window".  A load does: it writes the window's word into its
    destination register, and the register imprint is injective, so two
    different patches leave two different successors.  Note what this is NOT
    — it says nothing about views, timestamps or the weak machine; it is an
    ordinary SC fact about the instruction, of exactly the kind every leaf
    already proves. *)
Definition wreads_win (ra : Arch.pa) (rn : N) (tick : bool) (σ : wmstate)
    : Prop :=
  ¬ (∃ σ' : wmstate, ∀ u : bv (8 * rn),
       exec (riscv_step tick) (wpatch_st σ ra rn u)
       = Some (tt, wpatch_st σ' ra rn u)).

(* ====================================================================== *)
(** ** 7. The [lw]-shaped racy leaf: collapsing the ∀ into a DISJUNCTION

    For a ONE-SHOT flag the ∀-over-admissible-values is not a real
    quantification: every timestamp that holds a non-clear byte is the
    setter's ([WeakStarted.wstarted_oneshot]), and the setter's word agrees
    with the cleared word everywhere else.  So the racy word is one of TWO,
    and the rule's user branches on a disjunction exactly as the SC proof
    does. *)

(** The per-byte hypothesis: every value any timestamp holds for a byte of
    the window is either the cleared one or the setter's. *)
Definition wtwo_valued (s : wmstate) (ra : Arch.pa) (rn : N)
    (v0 v : bv (8 * rn)) : Prop :=
  forall (j : nat), (j < N.to_nat rn)%nat ->
    forall (t : nat) (b : bv 8),
      log_byte (wimg s) (wm_log s) t (acc_addr ra j) = Some b ->
      b = nth_byte v0 j \/ b = nth_byte v j.

Lemma wadm_two_valued (s : wmstate) (rak : akinfo) (ra : Arch.pa) (rn : N)
    (v0 v w : bv (8 * rn)) (i : nat) :
  (i < N.to_nat rn)%nat ->
  (forall j : nat, (j < N.to_nat rn)%nat -> j <> i -> nth_byte v j = nth_byte v0 j) ->
  wtwo_valued s ra rn v0 v ->
  wadm s rak ra rn w ->
  w = v0 \/ w = v.
Proof.
  intros Hi Hagree Htwo Hadm.
  destruct (decide (nth_byte w i = nth_byte v0 i)) as [Hwi|Hwi].
  - left. apply bv_eq_of_bytes. intros j Hj.
    assert (Hjn : (j < N.to_nat rn)%nat) by lia.
    destruct (decide (j = i)) as [->|Hne]; [exact Hwi|].
    destruct (Hadm j Hjn) as (t & Ht & _).
    destruct (Htwo j Hjn t (nth_byte w j) Ht) as [Hb|Hb]; [exact Hb|].
    rewrite Hb. by apply Hagree.
  - right. apply bv_eq_of_bytes. intros j Hj.
    assert (Hjn : (j < N.to_nat rn)%nat) by lia.
    destruct (decide (j = i)) as [->|Hne].
    + destruct (Hadm i Hi) as (t & Ht & _).
      destruct (Htwo i Hi t (nth_byte w i) Ht) as [Hb|Hb]; [by destruct (Hwi Hb)|].
      exact Hb.
    + destruct (Hadm j Hjn) as (t & Ht & _).
      destruct (Htwo j Hjn t (nth_byte w j) Ht) as [Hb|Hb]; [|exact Hb].
      rewrite Hb. symmetry. by apply Hagree.
Qed.

(** The [started] instance, and the whole point of §7: the escrow's one-shot
    fact ([WeakStarted.wstarted_oneshot], byte by byte over the flag word) plus
    the escrow's own value at its timestamp turn the rule's ∀-over-admissible-
    words into the two-way case split the SC proof already branches on.

    (The flag is 4 bytes and only byte 0 ever differs — [lock_one] and
    [lock_zero] agree above it — which is why ONE one-shot address is not
    enough and all four bytes carry the fact.) *)

Lemma nth_byte_lock_zero (j : nat) :
  (j < 4)%nat -> nth_byte lock_zero j = nth_byte lock_zero 0.
Proof.
  intros Hj. destruct j as [|[|[|[|j]]]]; [reflexivity| | | |lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma nth_byte_lock_one_high (j : nat) :
  (0 < j < 4)%nat -> nth_byte lock_one j = nth_byte lock_zero j.
Proof.
  intros Hj. destruct j as [|[|[|[|j]]]]; [lia| | | |lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma wadm_started_lw4 (σ : wmstate) (rak : akinfo) (a : Arch.pa) (t : nat)
    (w : bv 32) :
  (forall j : nat, (j < 4)%nat ->
     wstarted_oneshot (wimg σ) (wm_log σ) (acc_addr a j) t) ->
  (forall j : nat, (j < 4)%nat ->
     log_byte (wimg σ) (wm_log σ) t (acc_addr a j) = Some (nth_byte lock_one j)) ->
  wadm σ rak a 4 w ->
  w = lock_zero \/ w = lock_one.
Proof.
  intros Hone Hval Hadm.
  apply (wadm_two_valued σ rak a 4 lock_zero lock_one w 0%nat ltac:(lia)).
  - intros j Hj Hne. apply nth_byte_lock_one_high. lia.
  - intros j Hj t' b Hb.
    destruct (decide (b = nth_byte lock_zero 0)) as [->|Hne].
    + left. symmetry. by apply nth_byte_lock_zero.
    + right. pose proof (Hone j Hj t' b Hb Hne) as Ht'.
      rewrite Ht' (Hval j Hj) in Hb. by injection Hb as <-.
  - exact Hadm.
Qed.


(* ======================================================================
   WHAT IS *NOT* HERE, AND WHAT IT NEEDS

   THE COMPOSED WAITER ([wwp_started_wait]: the escrow's [lw] through the
   invariant, then the payload delivery) IS NOT IN THIS FILE, and the reason
   is a gap in the ESCROW rather than in the rule.

     §7's collapse takes TWO facts about the flag word.  One of them —
     "timestamp [t] holds the setter's value at every byte" — falls straight
     out of [WeakStarted.wstarted_at]'s element bundle ([wlat4], through
     [WeakGhost.wlat_lookup]).  The other is [WeakStarted.wstarted_oneshot]
     itself ("every timestamp holding a non-clear byte is [t]"), and NOTHING
     in [WeakStarted.wstarted_at] carries it: the latest-write elements pin
     the LATEST message, not the absence of an earlier non-clear one.  It is
     a statement about the whole log, so it is not a persistent pure fact
     either — it has to be re-established as the log grows, i.e. it belongs
     in the escrow's invariant with a preservation argument
     ([WeakStarted.wstarted_oneshot_app] is that argument's byte-level half).

   So the composition is one escrow-side change away, and the change is in
   [WeakStarted.v] (add the one-shot conjunct to [wstarted_at] / re-establish
   it in [wstarted_set]), not here.  Everything above it — the rule, the
   bridge and the collapse — is done, and the loop composes with
   [WeakAcquire.wwp_spin_loop] exactly as the spinlock's does: a waiter that
   reads [lock_zero] leaves nothing behind, so the retry edge carries no
   weak-memory content at all. *)
