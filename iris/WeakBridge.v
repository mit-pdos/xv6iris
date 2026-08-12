(** * WeakBridge.v — the pinned-fragment transfer bridge (M2b, item 0)

    ONE lemma family that makes every existing [RiscvExec.exec]-level fact
    reusable on the weak side.

    THE IDEA.  A weak state [σ : wmstate] projects to an SC state

        [wflat_st σ := MState (wm_regs σ) (wflat (wm_img σ) (wm_log σ)) (wm_dev σ)]

    — registers and devices verbatim, memory as [WeakLang.wflat], the
    COHERENT flat view of image + log ([wflat_lookup]: byte [a] holds what its
    latest write wrote).  On the fragment of runs where every read is FORCED
    to that latest value, [wexec] over [σ] and [exec] over [wflat_st σ] are
    the same run, and every existing leaf transfers.

    WHEN IS A READ FORCED?  Three ways, and the bridge takes all three:

      - the access is COHERENT ([ak_coh]: fetch/walker — dead for rv64d) or
        EXCLUSIVE/ATOMIC ([ak_latest]: the AMO read half).  Its admissibility
        condition IS [WeakMem.latest], so the timestamp is pinned with NO
        ownership at all — an [amoswap] read transfers for free.
      - the byte is PINNED IN [σ]: the hart's own index already covers the
        latest write to it ([pinned_read] below).  That is what owning an
        [↦w] at the hart's index gives ([WeakVProp.wpt_at] + [wlat_lookup]),
        and it is [WeakMem.readable_latest_pin] that turns it into
        "every admissible timestamp is THE latest one".
      - the byte has NEVER BEEN WRITTEN in this era ([latest_ts = 0], e.g. all
        kernel text and rodata): [pinned_read] then holds unconditionally
        ([pinned_read_unwritten]), which is what keeps the whole fetch/decode
        path on the pinned fragment for free.

    WHAT THE PREDICATE COLLECTS.  [pinned_exec] mirrors [wexec]'s recursion
    and collects exactly the per-ACCESS side conditions: the read footprint's
    pinnedness (only where the access kind does not already force it) and, on
    both reads and writes, the wrap-freedom of the access range ([acc_wf] —
    every RAM access has it, from [RiscvPtsto.addr_is_ram]).  Wrap-freedom is
    not bureaucracy: [wflat] is [Arch.pa]-keyed and the log is [Z]-keyed, so a
    message that wraps the address space is genuinely NOT described by
    [wflat] ([WeakLang.wflat_lookup] needs [wlog_wf]).

    THE TWO DIRECTIONS, and which one M3 consumes.  Both are proved:

      [exec_of_wexec_pinned] : wexec  ⟹  exec    — the CONSUMPTION direction.
        [WeakExec.wp_wexec_step]'s continuation quantifies over the oracle,
        so a leaf is HANDED a [wexec] fact and must identify its post-state;
        this direction turns it into an [exec] fact, which the caller's
        existing library lemma then determines by [exec]'s functionality.
      [wexec_of_exec_pinned] : exec  ⟹  ∃ oracle, wexec  — the REDUCIBILITY
        direction, which discharges the same rule's [∃ χ σ0 χ'] premise out
        of the [exec] witness every existing leaf already carries.

    [wexec_pinned_agree] packages both, and is the lemma a leaf applies. *)
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
Require Import RiscvLang RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The address seam, in the direction the bridge needs

    [WeakInterp.pa_z_add] converts [pa_add] to [acc_addr] under a
    wrap-freedom side condition.  The bridge needs the OTHER direction —
    [z_pa] of the additive address is the model's [pa_add] — and that one is
    UNCONDITIONAL: both sides wrap modulo 2^64, so the wrap-freedom question
    never arises. *)

Lemma bv_unsigned_mword_of_int (z : Z) :
  bv_unsigned (SailStdpp.Values.mword_of_int z : Arch.pa)
  = bv_wrap (SailStdpp.MachineWord.MachineWord.Z_idx
               (if 64 =? 32 then 34 else 64)) z.
Proof.
  unfold SailStdpp.Values.mword_of_int, SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, SailStdpp.MachineWord.MachineWord.Z_to_word.
  apply Z_to_bv_unsigned.
Qed.

Lemma z_pa_acc_addr (a : Arch.pa) (j : nat) : z_pa (acc_addr a j) = pa_add a j.
Proof.
  apply bv_eq. rewrite /z_pa /acc_addr /pa_z pa_uint_unsigned.
  rewrite bv_unsigned_mword_of_int.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, SailStdpp.Values.with_word.
  unfold SailStdpp.MachineWord.MachineWord.add.
  rewrite bv_add_unsigned bv_unsigned_mword_of_int.
  by rewrite bv_wrap_add_idemp_r.
Qed.

(** ... and so [wflat]'s [Arch.pa] key for byte [j] of an access IS the
    [Z] key the log uses, as soon as the access does not wrap. *)
Definition acc_wf (pa : Arch.pa) (n : N) : Prop :=
  pa_z pa + Z.of_N n <= 18446744073709551616.

Lemma acc_wf_byte pa n j :
  acc_wf pa n -> (j < N.to_nat n)%nat -> pa_z (pa_add pa j) = acc_addr pa j.
Proof.
  rewrite /acc_wf => Hwf Hj. apply pa_z_add. rewrite /pa_z in Hwf |- *. lia.
Qed.

(** The messages a wrap-free write appends are [WeakLang]-well-formed, which
    is what keeps [wflat] describing the log after the step. *)
Lemma acc_wf_msg tid k pa n {w : N} (v : bv w) :
  acc_wf pa n -> wmsg_wf (wwrite_msg tid k pa n v).
Proof.
  rewrite /acc_wf => Hwf. apply wwrite_msg_wf. lia.
Qed.

(* ====================================================================== *)
(** ** 2. The flat projection of a weak state, and the pinned predicate *)

(** The SC state a weak state projects to.  Registers and devices are
    literally the same objects (the weak machine reuses [RiscvLang]'s);
    memory is the coherent flat view of image + log. *)
Definition wflat_st (s : wmstate) : mstate :=
  MState (wm_regs s) (wflat (wm_img s) (wm_log s)) (wm_dev s).

Lemma wflat_st_regs s : sregs (wflat_st s) = wm_regs s.
Proof. reflexivity. Qed.
Lemma wflat_st_dev s : mdev (wflat_st s) = wm_dev s.
Proof. reflexivity. Qed.
Lemma wflat_st_mem s : mem (wflat_st s) = wflat (wm_img s) (wm_log s).
Proof. reflexivity. Qed.

(** The three state updates that leave the flat projection alone, or move it
    the way [exec] does. *)
Lemma wflat_st_ws s ws : wflat_st (wset_ws s ws) = wflat_st s.
Proof. reflexivity. Qed.
Lemma wflat_st_dev_set s d : wflat_st (wset_dev s d) = MState (sregs (wflat_st s)) (mem (wflat_st s)) d.
Proof. reflexivity. Qed.
Lemma wflat_st_reg_set s r v : wflat_st (wset_reg s r v) = set_reg (wflat_st s) r v.
Proof. reflexivity. Qed.

(** THE PINNED PREDICATE.  "The hart's own index already covers the latest
    write to byte [a]" — [w_vrNew ⊔ coh(a)] is exactly the hart's logical
    index ([WeakVProp.ws_view] / [WeakView.flr]), and [latest_ts] is the
    computed latest timestamp ([WeakMem.latest_ts_eq]).

    This is what owning [a ↦w{dq} v] at the hart's index gives: [wpt_at]
    hands out an element at timestamp [t] with [t ≤ flr (ws_view ws) a], and
    [wlat_lookup] says that element IS the latest write, i.e. [t = latest_ts].
    It is deliberately stated WITHOUT the vProp layer so that the bridge sits
    below it. *)
Definition pinned_read (s : wmstate) (a : Z) : Prop :=
  (latest_ts (wm_log s) a <= Nat.max (w_vrNew (wm_ws s)) (coh (wm_ws s) a))%nat.

(** A byte no message has ever written is pinned for free — which is every
    byte of kernel text and rodata, hence the whole fetch/decode path. *)
Lemma pinned_read_unwritten s a : latest_ts (wm_log s) a = 0%nat -> pinned_read s a.
Proof. rewrite /pinned_read => ->. lia. Qed.

(** An access kind that FORCES the latest write needs no pinning at all:
    [ak_coh] (fetch/walker) and [ak_latest] (the exclusive/AMO read half)
    both carry the latest-read side condition in [wbyte_ok] itself. *)
Definition ak_pins (ak : akinfo) : bool := ak_coh ak || ak_latest ak.

(* ====================================================================== *)
(** ** 3. One byte: the weak read IS the flat lookup *)

(** The byte the flat projection holds, in the log's own vocabulary. *)
Definition wbyte_flat (s : wmstate) (a : Z) : option (bv 8) :=
  log_byte (wimg s) (wm_log s) (latest_ts (wm_log s) a) a.

(** THE LATEST TIMESTAMP IS ALWAYS ADMISSIBLE, at every access kind: nothing
    above it writes [a] at all ([latest_ts_top]), so in particular nothing in
    the reader's coherence window does ([writes_in_clip] — note NO bound on
    the reader's floor is needed, which is what keeps [ws_bounded] out of the
    bridge). *)
Lemma wbyte_read_latest_ts s ak a :
  wbyte_read s ak a (latest_ts (wm_log s) a) = wbyte_flat s a.
Proof.
  rewrite /wbyte_read /wbyte_okb /wbyte_flat.
  assert (Htop : writes_inb (wm_log s) a (latest_ts (wm_log s) a)
                            (length (wm_log s)) = false)
    by (apply not_writes_inb, latest_ts_top).
  destruct (log_byte (wimg s) (wm_log s) (latest_ts (wm_log s) a) a)
    as [b|] eqn:Hv; [|reflexivity].
  destruct (ak_coh ak); [by rewrite Htop|].
  assert (Hrd : readableb (wimg s) (wm_log s) (wm_ws s)
                  (load_vpre (wm_ws s) (ak_sync ak)) a
                  (latest_ts (wm_log s) a) = true).
  { apply readableb_spec. split; [by exists b|].
    intros Hw. apply (latest_ts_top (wm_log s) a).
    eapply writes_in_mono_hi; [|apply writes_in_clip; exact Hw]. lia. }
  rewrite Hrd /=. destruct (ak_latest ak); by rewrite ?Htop.
Qed.

(** ... and the flat lookup IS that byte, on a wrap-free access. *)
Lemma wflat_byte s pa n j :
  wlog_wf (wm_log s) -> acc_wf pa n -> (j < N.to_nat n)%nat ->
  wflat (wm_img s) (wm_log s) !! pa_add pa j = wbyte_flat s (acc_addr pa j).
Proof.
  intros Hwf Hacc Hj.
  rewrite (wflat_lookup _ _ _ Hwf) /wbyte_flat /wimg (acc_wf_byte pa n j Hacc Hj) //.
Qed.

(** THE PINNING STEP: with the byte pinned (or the access kind forcing the
    latest read), an admissible timestamp can only be [latest_ts].  This is
    [WeakMem.readable_latest_pin] at the hart's own index. *)
Lemma wbyte_ok_pinned s ak a t b :
  (ak_pins ak = false -> pinned_read s a) ->
  wbyte_ok s ak a t b -> t = latest_ts (wm_log s) a.
Proof.
  intros Hpin [Hv Hadm]. rewrite /ak_pins in Hpin.
  assert (Hlat : latest (wimg s) (wm_log s) a (latest_ts (wm_log s) a)).
  { apply latest_ts_latest, (latest_ts_some (wimg s) (wm_log s) a t).
    by exists b. }
  destruct (ak_coh ak) eqn:Hcoh.
  { symmetry. apply (latest_ts_eq (wimg s) (wm_log s) a t).
    split; [by exists b|exact Hadm]. }
  destruct Hadm as [Hrd Hlt].
  destruct (ak_latest ak) eqn:Hlatk.
  { symmetry. apply (latest_ts_eq (wimg s) (wm_log s) a t).
    split; [by exists b|exact (Hlt eq_refl)]. }
  (* the genuinely weak arm: the hart's index pins the read *)
  specialize (Hpin eq_refl). rewrite /pinned_read in Hpin.
  eapply (readable_latest_pin (wimg s) (wm_log s) (wm_ws s)
            (load_vpre (wm_ws s) (ak_sync ak)) a); [exact Hlat| |exact Hrd].
  pose proof (load_vpre_vrNew (wm_ws s) (ak_sync ak)). lia.
Qed.

(* ====================================================================== *)
(** ** 4. A whole access: the read arm and the write arm *)

(** [mapM] over a range only looks at the range. *)
Local Lemma seq_cons (k n : nat) : seq k (S n) = k :: seq (S k) n.
Proof. reflexivity. Qed.

Lemma mapM_seq_ext {A} (f g : nat -> option A) (k n : nat) :
  (forall j, (k <= j < k + n)%nat -> f j = g j) ->
  mapM f (seq k n) = mapM g (seq k n).
Proof.
  revert k. induction n as [|n IH]; intros k Hfg; [reflexivity|].
  assert (Hk : f k = g k) by (apply Hfg; lia).
  assert (Hrest : mapM f (seq (S k) n) = mapM g (seq (S k) n)).
  { apply IH. intros j Hj. apply Hfg. lia. }
  rewrite (seq_cons k n) /= Hk Hrest //.
Qed.

(** THE READ ARM.  At the coherent timestamps — which is what a pinned read
    is forced to (§3) — the weak read and the flat read are the SAME partial
    function, [None] for [None]. *)
Lemma wread_bytes_read_bytes s ak pa n :
  wlog_wf (wm_log s) -> acc_wf pa n ->
  wread_bytes s ak pa n (coh_ts s pa n)
  = read_bytes (wflat (wm_img s) (wm_log s)) pa n.
Proof.
  intros Hwf Hacc. rewrite /wread_bytes /read_bytes.
  assert (Hlen : bool_decide (length (coh_ts s pa n) = N.to_nat n) = true)
    by (apply bool_decide_eq_true_2, coh_ts_length).
  assert (Hbytes : mapM (fun j : nat => wbyte_read s ak (acc_addr pa j)
                                          (coh_ts s pa n !!! j))
                        (seq 0 (N.to_nat n))
                   = mapM (fun j : nat => wflat (wm_img s) (wm_log s) !! pa_add pa j)
                          (seq 0 (N.to_nat n))).
  { apply mapM_seq_ext. intros j Hj.
    assert (Hjlt : (j < N.to_nat n)%nat) by lia.
    rewrite (coh_ts_lookup s pa n j Hjlt) wbyte_read_latest_ts.
    by rewrite (wflat_byte s pa n j Hwf Hacc Hjlt). }
  by rewrite Hlen Hbytes.
Qed.

(** THE WRITE ARM.  Appending the message and overwriting the flat map are
    the same map: [bytes_map]'s left-biased insert chain IS [write_bytes]'
    [foldr], key for key ([z_pa_acc_addr]) — and NO wrap-freedom is needed
    for that (both sides wrap identically); [acc_wf] is needed only to keep
    [wlog_wf], i.e. for the NEXT access. *)
Lemma bytes_map_union_foldr (f : nat -> bv 8) (pa : Arch.pa) (n k : nat)
    (mm : gmap Arch.pa (bv 8)) :
  bytes_map (acc_addr pa k) (map f (seq k n)) ∪ mm
  = foldr (fun j acc => <[pa_add pa j := f j]> acc) mm (seq k n).
Proof.
  revert k. induction n as [|n IH]; intros k; [by rewrite /= left_id_L|].
  rewrite (seq_cons k n) /= -insert_union_l z_pa_acc_addr.
  replace (acc_addr pa k + 1) with (acc_addr pa (S k))
    by (rewrite /acc_addr; lia).
  by rewrite IH.
Qed.

Lemma wflat_write tid s ak pa n (v : bv (8 * n)) :
  wflat (wm_img s) (wm_log (wwrite_post tid s ak pa n v))
  = write_bytes (wflat (wm_img s) (wm_log s)) pa n v.
Proof.
  rewrite wwrite_post_log wflat_app /msg_map /wwrite_msg /= /write_bytes
          -(acc_addr_0 pa).
  apply (bytes_map_union_foldr (fun j : nat => nth_byte v j) pa (N.to_nat n) 0).
Qed.

(** ... and the log stays [wflat]-describable. *)
Lemma wflat_write_wf tid s ak pa n (v : bv (8 * n)) :
  wlog_wf (wm_log s) -> acc_wf pa n ->
  wlog_wf (wm_log (wwrite_post tid s ak pa n v)).
Proof.
  intros Hwf Hacc. rewrite wwrite_post_log /wlog_wf Forall_app.
  split; [exact Hwf|apply Forall_singleton, (acc_wf_msg tid _ pa n v Hacc)].
Qed.

(* ====================================================================== *)
(** ** 5. [pinned_exec]: the run predicate

    The side conditions of a WHOLE run, collected along [wexec]'s own
    recursion (same dependent-match shape as [WeakExec.mchoice_free]).  Per
    RAM access: wrap-freedom, and — only where the access kind does not
    already force the latest read — pinnedness of the read footprint.  The
    successor states are the CANONICAL ones (reads at [coh_ts]); §3 is what
    says the actual run cannot use any others. *)

Fixpoint pinned_exec (tid : option nat) {X} (m : M X) (s : wmstate) {struct m}
    : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       | Interface.RegRead r _ =>
           fun k => pinned_exec tid (k (register_lookup r s.(wm_regs))) s
       | Interface.RegWrite r _ v => fun k => pinned_exec tid (k tt) (wset_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               forall w d',
                 dev_read s.(wm_dev) (Interface.ReadReq.pa req) n = Some (w, d') ->
                 pinned_exec tid (k (inl (w, None))) (wset_dev s d')
             else
               acc_wf (Interface.ReadReq.pa req) n /\
               (ak_pins (classify (Interface.ReadReq.access_kind req)) = false ->
                  forall j, (j < N.to_nat n)%nat ->
                    pinned_read s (acc_addr (Interface.ReadReq.pa req) j)) /\
               (forall w,
                  wread_bytes s (classify (Interface.ReadReq.access_kind req))
                    (Interface.ReadReq.pa req) n
                    (coh_ts s (Interface.ReadReq.pa req) n) = Some w ->
                  pinned_exec tid (k (inl (w, None)))
                    (wread_post s (classify (Interface.ReadReq.access_kind req))
                       (Interface.ReadReq.pa req)
                       (coh_ts s (Interface.ReadReq.pa req) n)))
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               forall d',
                 dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                           (Interface.WriteReq.value req) = Some d' ->
                 pinned_exec tid (k (inl None)) (wset_dev s d')
             else
               acc_wf (Interface.WriteReq.pa req) n /\
               pinned_exec tid (k (inl None))
                 (wwrite_post tid s
                    (classify (Interface.WriteReq.access_kind req))
                    (Interface.WriteReq.pa req) n (Interface.WriteReq.value req))
       | Interface.Barrier b =>
           fun k => pinned_exec tid (k tt) (wset_ws s (barrier_post s.(wm_ws) b))
       | Interface.InstrAnnounce _   => fun k => pinned_exec tid (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => pinned_exec tid (k tt) s
       | Interface.CacheOp _         => fun k => pinned_exec tid (k tt) s
       | Interface.TlbOp _           => fun k => pinned_exec tid (k tt) s
       | Interface.TakeException _   => fun k => pinned_exec tid (k tt) s
       | Interface.ReturnException _ => fun k => pinned_exec tid (k tt) s
       | Interface.TranslationStart _=> fun k => pinned_exec tid (k tt) s
       | Interface.TranslationEnd _  => fun k => pinned_exec tid (k tt) s
       | Interface.CycleCount        => fun k => pinned_exec tid (k tt) s
       | Interface.Message _         => fun k => pinned_exec tid (k tt) s
       | Interface.GetCycleCount     => fun k => pinned_exec tid (k 0%Z) s
       (* Choose / GenericFail / Discard / ExtraOutcome: both interpreters
          are stuck, so there is nothing to require *)
       | _ => fun _ => True
       end) k
  end.

(** THE TIMESTAMP-COLLAPSE STEP, at a whole access: with the footprint pinned
    (or the kind forcing it), the oracle has NO freedom — the timestamps it
    supplied ARE the coherent ones. *)
Lemma wread_pinned_ts s ak pa n ts w :
  (ak_pins ak = false ->
     forall j, (j < N.to_nat n)%nat -> pinned_read s (acc_addr pa j)) ->
  wread_ok s ak pa n ts w -> ts = coh_ts s pa n.
Proof.
  intros Hpin [Hlen Hbytes].
  apply (list_eq_same_length _ _ (N.to_nat n));
    [apply coh_ts_length|exact Hlen|].
  intros j t1 t2 Hj Ht1 Ht2.
  assert (Hjn : (N.of_nat j < n)%N) by lia.
  pose proof (Hbytes j Hjn) as Hok.
  rewrite (list_lookup_total_correct _ _ _ Ht1) in Hok.
  assert (Ht2' : t2 = latest_ts (wm_log s) (acc_addr pa j)).
  { rewrite -(list_lookup_total_correct _ _ _ Ht2).
    apply (coh_ts_lookup s pa n j Hj). }
  rewrite Ht2'. eapply wbyte_ok_pinned; [|exact Hok].
  intros Hp. by apply Hpin.
Qed.

(** The three post-state projections the induction needs. *)
Lemma wflat_st_read_post s ak pa ts :
  wflat_st (wread_post s ak pa ts) = wflat_st s.
Proof.
  rewrite /wflat_st wread_post_regs wread_post_img wread_post_log
          wread_post_dev //.
Qed.

Lemma wflat_st_write_post tid s ak pa n (v : bv (8 * n)) :
  wflat_st (wwrite_post tid s ak pa n v)
  = MState (sregs (wflat_st s)) (write_bytes (mem (wflat_st s)) pa n v)
           (mdev (wflat_st s)).
Proof. rewrite /wflat_st /= (wflat_write tid s ak pa n v) //. Qed.

Lemma wlog_wf_read_post s ak pa ts :
  wlog_wf (wm_log s) -> wlog_wf (wm_log (wread_post s ak pa ts)).
Proof. by rewrite wread_post_log. Qed.

(* ====================================================================== *)
(** ** 6. THE BRIDGE, direction 1: [wexec] ⟹ [exec]

    THE CONSUMPTION DIRECTION.  [WeakExec.wp_wexec_step]'s continuation hands
    a leaf a [wexec] fact at an oracle it did not choose; this turns it into
    an [exec] fact over the flat projection, which the leaf's EXISTING
    library lemma then pins by [exec]'s functionality
    ([RiscvExec.exec_run_det]).  Everything the leaf must know about the
    weak post-state — its registers, its devices, its flat memory — comes
    out of that identification.

    (The premises are ordered [pinned_exec] BEFORE [wlog_wf] on purpose: the
    induction instantiates the state from the pinnedness hypothesis, and the
    log-wellformedness of a post-state is then checked by conversion.) *)

Lemma exec_of_wexec_pinned tid {X} (m : M X) :
  forall s, pinned_exec tid m s -> wlog_wf (wm_log s) ->
  forall χ x s' χ', wexec tid m χ s = Some (x, s', χ') ->
    exec m (wflat_st s) = Some (x, wflat_st s').
Proof.
  induction m as [y|T oc k IH]; intros s Hp Hwf χ x s' χ' Hex.
  - simpl in Hex. by injection Hex as <- <- _.
  - destruct oc; simpl in Hp, Hex; try discriminate;
      try (exact (IH _ _ Hp Hwf _ _ _ _ Hex)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        simpl. rewrite Hd Hdr. exact (IH _ _ (Hp w0 d' eq_refl) Hwf _ _ _ _ Hex).
      * destruct Hp as (Hacc & Hpin & Hk).
        destruct (ak_coh (classify _)) eqn:Hcoh.
        -- destruct (wread_bytes _ _ _ _ _) as [w0|] eqn:Hrb; [|discriminate].
           pose proof (IH _ _ (Hk w0 eq_refl) (wlog_wf_read_post _ _ _ _ Hwf)
                          _ _ _ _ Hex) as Hiex.
           rewrite wflat_st_read_post in Hiex.
           rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hrb.
           simpl. rewrite Hd Hrb. exact Hiex.
        -- destruct χ as [|ts χ0]; [discriminate|].
           destruct (wread_bytes _ _ _ _ ts) as [w0|] eqn:Hrb; [|discriminate].
           pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin
                         (wread_bytes_spec _ _ _ _ _ _ Hrb)) as Hts.
           rewrite Hts in Hrb Hex.
           pose proof (IH _ _ (Hk w0 Hrb) (wlog_wf_read_post _ _ _ _ Hwf)
                          _ _ _ _ Hex) as Hiex.
           rewrite wflat_st_read_post in Hiex.
           rewrite (wread_bytes_read_bytes s _ _ _ Hwf Hacc) in Hrb.
           simpl. rewrite Hd Hrb. exact Hiex.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        simpl. rewrite Hd Hdw. exact (IH _ _ (Hp d' eq_refl) Hwf _ _ _ _ Hex).
      * destruct Hp as (Hacc & Hp).
        pose proof (IH _ _ Hp (wflat_write_wf _ _ _ _ _ _ Hwf Hacc)
                       _ _ _ _ Hex) as Hiex.
        rewrite wflat_st_write_post in Hiex.
        simpl. rewrite Hd. exact Hiex.
Qed.

(* ====================================================================== *)
(** ** 7. THE BRIDGE, direction 2: [exec] ⟹ [wexec]

    THE REDUCIBILITY DIRECTION.  [WeakExec.wp_wexec_step] also asks the leaf
    for ONE witness that the weak machine can step; on the pinned fragment
    that witness is manufactured from the [exec] fact the leaf already has,
    with the oracle built out of the coherent timestamps. *)

Lemma wexec_of_exec_pinned tid {X} (m : M X) :
  forall s, pinned_exec tid m s -> wlog_wf (wm_log s) ->
  forall x t', exec m (wflat_st s) = Some (x, t') ->
    exists χ s' χ', wexec tid m χ s = Some (x, s', χ') /\ wflat_st s' = t'.
Proof.
  induction m as [y|T oc k IH]; intros s Hp Hwf x t' Hex.
  - simpl in Hex. injection Hex as <- <-. by exists [], s, [].
  - destruct oc; simpl in Hp, Hex; try discriminate;
      try (exact (IH _ _ Hp Hwf _ _ Hex)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        destruct (IH _ _ (Hp w0 d' eq_refl) Hwf _ _ Hex) as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd Hdr.
      * destruct Hp as (Hacc & Hpin & Hk).
        destruct (read_bytes _ _ _) as [w0|] eqn:Hrd; [|discriminate].
        lazymatch type of Hpin with
        | ak_pins ?ak0 = false -> _ =>
            pose proof (wread_bytes_read_bytes s ak0 _ _ Hwf Hacc) as Heqrb
        end.
        rewrite Hrd in Heqrb.
        pose proof (Hk w0 Heqrb) as Hp2.
        lazymatch type of Hp2 with
        | pinned_exec _ _ ?sr =>
            assert (Hex2 : exec (k (inl (w0, None))) (wflat_st sr) = Some (x, t'))
              by (rewrite wflat_st_read_post; exact Hex)
        end.
        destruct (IH _ _ Hp2 (wlog_wf_read_post _ _ _ _ Hwf) _ _ Hex2)
          as (χ & s2 & χ' & Hw & Heq).
        lazymatch type of Hpin with
        | ak_pins ?ak0 = false -> _ => destruct (ak_coh ak0) eqn:Hcoh
        end.
        -- exists χ, s2, χ'. split; [|exact Heq].
           simpl. rewrite Hd Hcoh Heqrb. exact Hw.
        -- lazymatch type of Heqrb with
           | wread_bytes _ _ _ _ ?ts0 = _ => exists (ts0 :: χ), s2, χ'
           end. split; [|exact Heq].
           simpl. rewrite Hd Hcoh Heqrb. exact Hw.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        destruct (IH _ _ (Hp d' eq_refl) Hwf _ _ Hex) as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd Hdw.
      * destruct Hp as (Hacc & Hp).
        lazymatch type of Hp with
        | pinned_exec _ _ ?sw =>
            assert (Hex2 : exec (k (inl None)) (wflat_st sw) = Some (x, t'))
              by (rewrite wflat_st_write_post; exact Hex)
        end.
        destruct (IH _ _ Hp (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) _ _ Hex2)
          as (χ & s2 & χ' & Hw & Heq).
        exists χ, s2, χ'. split; [|exact Heq]. simpl. by rewrite Hd.
Qed.

(* ====================================================================== *)
(** ** 8. What the leaf applies

    The two directions packaged against ONE [exec] fact — which is exactly
    what an existing leaf lemma of the tree hands you.  Read it as: on the
    pinned fragment, the weak machine can step, and every way it steps
    agrees with the SC run on the value, the registers, the devices and the
    (flat) memory.  The TIMESTAMPS still vary; nothing observable does. *)

Lemma wexec_pinned_agree tid {X} (m : M X) s x0 t0 :
  pinned_exec tid m s -> wlog_wf (wm_log s) ->
  exec m (wflat_st s) = Some (x0, t0) ->
  (exists χ s0 χ', wexec tid m χ s = Some (x0, s0, χ')) /\
  (forall χ x s' χ', wexec tid m χ s = Some (x, s', χ') ->
     x = x0 /\ wm_regs s' = sregs t0 /\ wm_dev s' = mdev t0 /\
     wflat (wm_img s') (wm_log s') = mem t0).
Proof.
  intros Hp Hwf Hex. split.
  - destruct (wexec_of_exec_pinned tid m s Hp Hwf x0 t0 Hex)
      as (χ & s0 & χ' & Hw & _).
    by exists χ, s0, χ'.
  - intros χ x s' χ' Hw.
    pose proof (exec_of_wexec_pinned tid m s Hp Hwf χ x s' χ' Hw) as Hex'.
    rewrite Hex in Hex'. injection Hex' as Hx Ht.
    rewrite Hx Ht. by split_and!.
Qed.

(** The log stays [wflat]-describable across a pinned run, so the premise of
    the NEXT instruction's bridge is re-established. *)
Lemma wexec_pinned_wlog_wf tid {X} (m : M X) :
  forall s, pinned_exec tid m s -> wlog_wf (wm_log s) ->
  forall χ x s' χ', wexec tid m χ s = Some (x, s', χ') -> wlog_wf (wm_log s').
Proof.
  induction m as [y|T oc k IH]; intros s Hp Hwf χ x s' χ' Hex.
  - simpl in Hex. by injection Hex as <- <- _.
  - destruct oc; simpl in Hp, Hex; try discriminate;
      try (exact (IH _ _ Hp Hwf _ _ _ _ Hex)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        exact (IH _ _ (Hp w0 d' eq_refl) Hwf _ _ _ _ Hex).
      * destruct Hp as (Hacc & Hpin & Hk).
        destruct (ak_coh (classify _)) eqn:Hcoh.
        -- destruct (wread_bytes _ _ _ _ _) as [w0|] eqn:Hrb; [|discriminate].
           exact (IH _ _ (Hk w0 eq_refl) (wlog_wf_read_post _ _ _ _ Hwf)
                     _ _ _ _ Hex).
        -- destruct χ as [|ts χ0]; [discriminate|].
           destruct (wread_bytes _ _ _ _ ts) as [w0|] eqn:Hrb; [|discriminate].
           pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin
                         (wread_bytes_spec _ _ _ _ _ _ Hrb)) as Hts.
           rewrite Hts in Hrb Hex.
           exact (IH _ _ (Hk w0 Hrb) (wlog_wf_read_post _ _ _ _ Hwf)
                     _ _ _ _ Hex).
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        exact (IH _ _ (Hp d' eq_refl) Hwf _ _ _ _ Hex).
      * destruct Hp as (Hacc & Hp).
        exact (IH _ _ Hp (wflat_write_wf _ _ _ _ _ _ Hwf Hacc) _ _ _ _ Hex).
Qed.

(* ====================================================================== *)
(** ** 9. The connector: OWNERSHIP ⟹ PINNEDNESS

    [pinned_exec] is a pure side condition, and this is where the surface
    layer discharges it: a byte owned at the hart's index is pinned, because
    the [γlat] element IS the latest write ([WeakGhost.wlat_lookup]) and the
    points-to's receipt says the hart's floor covers its timestamp
    ([WeakVProp.wpt_at]).  An ERA-IMAGE byte ([wpt_img], timestamp 0 — all
    kernel text and rodata) is pinned with no receipt at all, which is what
    puts the whole fetch/decode path on the pinned fragment for free. *)
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import RiscvPtsto WeakGhost WeakView WeakVProp.

Section connector.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wpt_pinned_read σ (a : Z) (dq : dfrac) (v : bv 8) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (a ↦w{dq} v) (wm_ws σ) -∗ ⌜pinned_read σ a⌝.
  Proof.
    iIntros "Hi Hpt". rewrite wpt_at. iDestruct "Hpt" as (t) "[He %Ht]".
    iDestruct (wlat_lookup with "Hi He") as %Hlat.
    iPureIntro. rewrite /pinned_read (latest_val_ts _ _ _ _ _ Hlat).
    by rewrite flr_ws_view in Ht.
  Qed.

  (** The era-image case: no view, no receipt, no hypothesis about the hart. *)
  Lemma wpt_img_pinned_read σ (a : Z) (dq : dfrac) (v : bv 8) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt_img a dq v) (wm_ws σ) -∗ ⌜pinned_read σ a⌝.
  Proof.
    iIntros "Hi Hpt". rewrite wpt_img_at.
    iDestruct (wlat_lookup with "Hi Hpt") as %Hlat.
    iPureIntro. by apply pinned_read_unwritten, (latest_val_ts _ _ _ _ _ Hlat).
  Qed.

  (** THE ACCESS-FOOTPRINT FORM — what a load leaf actually feeds
      [pinned_exec]'s read arm: owning the [n] bytes of the access at the
      hart's index discharges the whole obligation.  (The [wlat_interp]
      authority is consumed once and the ∀ introduced before it is spent —
      the M2a recipe.) *)
  Lemma wpt_pinned_acc σ (pa : Arch.pa) (n : N) (dq : dfrac) (bs : list (bv 8)) :
    length bs = N.to_nat n ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    ([∗ list] j ↦ b ∈ bs, vwp_hold (acc_addr pa j ↦w{dq} b) (wm_ws σ)) -∗
    ⌜forall j, (j < N.to_nat n)%nat -> pinned_read σ (acc_addr pa j)⌝.
  Proof.
    intros Hlen. iIntros "Hi Hbs".
    rewrite bi.pure_forall. iIntros (j).
    rewrite bi.pure_impl. iIntros (Hj).
    assert (Hlk : bs !! j = Some (bs !!! j))
      by (apply list_lookup_lookup_total_lt; lia).
    iDestruct (big_sepL_lookup _ _ j _ Hlk with "Hbs") as "Hpt".
    by iApply (wpt_pinned_read with "Hi Hpt").
  Qed.

End connector.

(* ====================================================================== *)
(** ** 10. PROOF OF CONCEPT: an existing [exec] leaf, transferred

    [ExecCommon.exec_execute_ITYPE_ADDI] is an ordinary member of the
    tree's [exec]-level library ("if [rs1] reads [a] and writing [rd] lands
    in [s'], then [execute (ITYPE … ADDI)] retires there").  Its weak
    counterpart below is ONE [apply] of the bridge over it — no view
    reasoning, no re-peeling of the model, no new proof about the
    instruction.  That is the transfer story end to end. *)
Require Import ExecCommon.

Example wexec_execute_ITYPE_ADDI tid (imm : SailStdpp.Values.mword 12)
    (rs1 rd : regidx) (a : SailStdpp.Values.mword 64)
    (s : wmstate) (t' : mstate) :
  pinned_exec tid (execute (ITYPE (imm, rs1, rd, ADDI))) s ->
  wlog_wf (wm_log s) ->
  exec (rX_bits rs1) (wflat_st s) = Some (a, wflat_st s) ->
  exec (wX_bits rd (add_vec a (sign_extend' 64 imm))) (wflat_st s)
    = Some (tt, t') ->
  (* the weak machine can execute it ... *)
  (exists χ s0 χ', wexec tid (execute (ITYPE (imm, rs1, rd, ADDI))) χ s
                   = Some (RETIRE_SUCCESS, s0, χ')) /\
  (* ... and however it does, the result is the SC one *)
  (forall χ x s' χ',
     wexec tid (execute (ITYPE (imm, rs1, rd, ADDI))) χ s = Some (x, s', χ') ->
     x = RETIRE_SUCCESS /\ wm_regs s' = sregs t' /\ wm_dev s' = mdev t' /\
     wflat (wm_img s') (wm_log s') = mem t').
Proof.
  intros Hp Hwf Ha Hw.
  apply (wexec_pinned_agree tid _ s _ t' Hp Hwf).
  exact (exec_execute_ITYPE_ADDI imm rs1 rd a (wflat_st s) t' Ha Hw).
Qed.

(* ====================================================================== *)
(** ** 11. THE MERGED PEEL: [wstep_ok] (M3a, item 1)

    M2b left a leaf with TWO obligations over the same peeled instruction:
    [pinned_exec] (this file, §5 — the per-access side conditions of the
    transfer) and [WeakExec.mchoice_free] (the sufficient condition for
    [WeakExec.wexec_covers]).  Doing the same peel twice is pure overhead,
    and it is also more than necessary: [mchoice_free] demands
    choice-freedom of the continuation at EVERY possible read result,
    whereas on the PINNED fragment every admissible read returns the
    canonical one.  So the two merge into a single predicate — [pinned_exec]
    with the [Choose] arm turned from [True] into [False] — which is
    strictly WEAKER than their conjunction and still delivers everything.

    A leaf's obligation is now exactly ONE peel, and
    [wexec_leaf_agree] is the one lemma it applies: reducibility, the
    ∀-oracle agreement, the [wexec_covers] premise of
    [WeakExec.wp_wexec_step], and the [wlog_wf] of the successor, all off
    that single predicate plus the [exec] fact the SC library already
    supplies. *)
Require Import WeakExec.

Fixpoint wstep_ok (tid : option nat) {X} (m : M X) (s : wmstate) {struct m}
    : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       | Interface.RegRead r _ =>
           fun k => wstep_ok tid (k (register_lookup r s.(wm_regs))) s
       | Interface.RegWrite r _ v => fun k => wstep_ok tid (k tt) (wset_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               forall w d',
                 dev_read s.(wm_dev) (Interface.ReadReq.pa req) n = Some (w, d') ->
                 wstep_ok tid (k (inl (w, None))) (wset_dev s d')
             else
               acc_wf (Interface.ReadReq.pa req) n /\
               (ak_pins (classify (Interface.ReadReq.access_kind req)) = false ->
                  forall j, (j < N.to_nat n)%nat ->
                    pinned_read s (acc_addr (Interface.ReadReq.pa req) j)) /\
               (forall w,
                  wread_bytes s (classify (Interface.ReadReq.access_kind req))
                    (Interface.ReadReq.pa req) n
                    (coh_ts s (Interface.ReadReq.pa req) n) = Some w ->
                  wstep_ok tid (k (inl (w, None)))
                    (wread_post s (classify (Interface.ReadReq.access_kind req))
                       (Interface.ReadReq.pa req)
                       (coh_ts s (Interface.ReadReq.pa req) n)))
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               forall d',
                 dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                           (Interface.WriteReq.value req) = Some d' ->
                 wstep_ok tid (k (inl None)) (wset_dev s d')
             else
               acc_wf (Interface.WriteReq.pa req) n /\
               wstep_ok tid (k (inl None))
                 (wwrite_post tid s
                    (classify (Interface.WriteReq.access_kind req))
                    (Interface.WriteReq.pa req) n (Interface.WriteReq.value req))
       | Interface.Barrier b =>
           fun k => wstep_ok tid (k tt) (wset_ws s (barrier_post s.(wm_ws) b))
       | Interface.InstrAnnounce _   => fun k => wstep_ok tid (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => wstep_ok tid (k tt) s
       | Interface.CacheOp _         => fun k => wstep_ok tid (k tt) s
       | Interface.TlbOp _           => fun k => wstep_ok tid (k tt) s
       | Interface.TakeException _   => fun k => wstep_ok tid (k tt) s
       | Interface.ReturnException _ => fun k => wstep_ok tid (k tt) s
       | Interface.TranslationStart _=> fun k => wstep_ok tid (k tt) s
       | Interface.TranslationEnd _  => fun k => wstep_ok tid (k tt) s
       | Interface.CycleCount        => fun k => wstep_ok tid (k tt) s
       | Interface.Message _         => fun k => wstep_ok tid (k tt) s
       | Interface.GetCycleCount     => fun k => wstep_ok tid (k 0%Z) s
       (* THE ONLY ARM THAT DIFFERS FROM [pinned_exec]: a [Choose] is what
          breaks the [wrun] -> [wexec] bridge, so it is ruled out here. *)
       | Interface.Choose _          => fun _ => False
       (* GenericFail / Discard / ExtraOutcome: both interpreters are stuck,
          so there is nothing to require *)
       | _ => fun _ => True
       end) k
  end.

(** The merged predicate implies the transfer's side conditions ... *)
Lemma wstep_ok_pinned tid {X} (m : M X) :
  forall s, wstep_ok tid m s -> pinned_exec tid m s.
Proof.
  induction m as [y|T oc k IH]; intros s Hok; [exact I|].
  destruct oc; simpl in Hok |- *; try exact I;
    try (exact (IH _ _ Hok)).
  - (* MemRead *)
    destruct (dev_addr _).
    + intros w d' Hd. exact (IH _ _ (Hok w d' Hd)).
    + destruct Hok as (Hacc & Hpin & Hk).
      split_and!; [exact Hacc|exact Hpin|]. intros w Hw. exact (IH _ _ (Hk w Hw)).
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros d' Hd. exact (IH _ _ (Hok d' Hd)).
    + destruct Hok as (Hacc & Hp). split; [exact Hacc|exact (IH _ _ Hp)].
Qed.

(** ... and, on its own, the [wrun] -> [wexec] bridge.  This is the second
    half of the merge, and the reason the merged predicate does not have to
    carry [mchoice_free]'s ∀-over-read-results: at a pinned read the run
    CANNOT have used any timestamps but the canonical ones
    ([wread_pinned_ts]), so the canonical successor — the only one
    [wstep_ok] speaks about — is the one the run took. *)
Lemma wrun_wexec_wstep_ok tid {X} (m : M X) :
  forall s, wstep_ok tid m s ->
  forall x s', wrun tid m s x s' ->
    exists χ χ', wexec tid m χ s = Some (x, s', χ').
Proof.
  induction m as [y|T oc k IH]; intros s Hok x s' Hrun.
  - destruct Hrun as [-> ->]. by exists [], [].
  - destruct oc; simpl in Hok, Hrun;
      try (exact (IH _ _ Hok _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hok).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        destruct (IH _ _ (Hok w0 d' eq_refl) _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdr. exact Hex.
      * destruct Hrun as (w & ts & Hokr & Hrun).
        destruct Hok as (Hacc & Hpin & Hk).
        pose proof (wread_pinned_ts _ _ _ _ _ _ Hpin Hokr) as Hts.
        rewrite Hts in Hokr, Hrun.
        pose proof (wread_bytes_complete _ _ _ _ _ _ Hokr) as Hrb.
        destruct (IH _ _ (Hk w Hrb) _ _ Hrun) as (χ & χ' & Hex).
        lazymatch goal with
        | Hpin0 : ak_pins ?ak0 = false -> _ |- _ => destruct (ak_coh ak0) eqn:Hcoh
        end.
        -- exists χ, χ'. simpl. rewrite Hd Hcoh Hrb. exact Hex.
        -- lazymatch type of Hrb with
           | wread_bytes _ _ _ _ ?ts0 = _ => exists (ts0 :: χ), χ'
           end.
           simpl. rewrite Hd Hcoh Hrb. exact Hex.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        destruct (IH _ _ (Hok d' eq_refl) _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdw. exact Hex.
      * destruct Hok as (Hacc & Hok).
        destruct (IH _ _ Hok _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd. exact Hex.
Qed.

Lemma wstep_ok_covers tid {X} (m : M X) s :
  wstep_ok tid m s -> wexec_covers tid m s.
Proof. intros Hok x s' Hrun. by eapply wrun_wexec_wstep_ok. Qed.

(** THE ONE LEMMA A LEAF APPLIES.  One peel in, everything
    [WeakExec.wp_wexec_step] asks for out. *)
Lemma wexec_leaf_agree tid {X} (m : M X) s x0 t0 :
  wstep_ok tid m s -> wlog_wf (wm_log s) ->
  exec m (wflat_st s) = Some (x0, t0) ->
  wexec_covers tid m s /\
  (exists χ s0 χ', wexec tid m χ s = Some (x0, s0, χ')) /\
  (forall χ x s' χ', wexec tid m χ s = Some (x, s', χ') ->
     x = x0 /\ wm_regs s' = sregs t0 /\ wm_dev s' = mdev t0 /\
     wflat (wm_img s') (wm_log s') = mem t0 /\ wlog_wf (wm_log s')).
Proof.
  intros Hok Hwf Hex.
  pose proof (wstep_ok_pinned tid m s Hok) as Hp.
  destruct (wexec_pinned_agree tid m s x0 t0 Hp Hwf Hex) as [Hred Hag].
  split_and!.
  - by apply wstep_ok_covers.
  - exact Hred.
  - intros χ x s' χ' Hw.
    destruct (Hag χ x s' χ' Hw) as (? & ? & ? & ?). split_and!; try done.
    exact (wexec_pinned_wlog_wf tid m s Hp Hwf χ x s' χ' Hw).
Qed.
