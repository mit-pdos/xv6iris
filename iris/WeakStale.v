(** * WeakStale.v — the SC mirror with a STALE memory for unpinned reads (6a)

    THE GAP THIS CLOSES.  [WeakRacy.wstep_ok_racy] can now DESCRIBE the walk's
    blocked trace shape (the leaf slot read twice in one step — plain and
    racy, then exclusive and latest, with no write between): since the
    disjointness became the parameter [D], instantiating [D := fun _ _ => True]
    gives the exclusive re-read and the CAS write an arm.  What it cannot do
    is PRODUCE it.  Every producer we have
    ([WeakVarCert.wstep_ok_racy_{false,true}_of_confined]) supplies the
    continuation of an off-window read from a confined SC run at the memory
    PATCHED with the racy value [w] — and the peel demands that continuation at
    the coherence-LATEST word [lw], because that is what the weak machine's
    [ak_latest] read returns.  When [w <> lw] — which is the entire reason
    shape 4 exists — the producer cannot close.  [RiscvExec.exec] is
    KIND-BLIND, so one memory answers both reads with one value.

    THE ANSWER: give the mirror TWO memories, selected per read by the SAME
    bit the weak machine uses to decide pinnedness.

      [stale_mem ra rn w ak s := if ak_pins ak then mem s
                                 else write_bytes (mem s) ra rn w]

    [ak_pins = ak_coh || ak_latest] ([WeakBridge.v]) is exactly "this read
    returns the latest write whatever the reader's view is".  So under
    [exec_stale]:

      - the walk's PLAIN leaf read ([WeakFetchEff.wak_plain], [ak_pins =
        false]) reads the patched memory and returns the racy [w];
      - the CAS's [read_pte_exclusive] ([AkInfo false true false], [ak_pins =
        true]) reads the real memory and returns [lw], which is what the
        peel's off-window disjunct demands (the confined memory is included
        in [WeakBridge.wflat]);
      - OFF the window the two memories agree
        ([WeakRacy.read_bytes_patch_disj]), so no fact about a non-window
        access changes — which is what §3's TRANSFER makes precise, and what
        keeps this from being a mirror of the whole walk library.

    Design, the variant arithmetic, and why patching the memory for the WHOLE
    run is not merely unprovable but WRONG (it clobbers the D bit the sail
    fork's atomic recheck exists to preserve):
    claude-notes/design/weak-memory-walk-bridge.md §8.

    ======================= WHAT IS IN HERE =======================

    §1  [stale_mem] and [exec_stale] — [WeakCert.exec_eff] arm for arm, with
        the one changed RAM-read arm.
    §2  the composition kit: the [WeakEff] §1–§2 lemmas restated, so a script
        that walks a bind spine replays at [exec_stale].
    §3  THE TRANSFER, both directions: a run whose every UNPINNED read is
        disjoint from the window has [exec_stale … = exec_eff …].  This is
        what carries the existing library across; only the sub-runs that
        actually read the window need a mirrored proof.
    §4  the phase-[false] embedding: with [D := True] the phase-[false] peel
        IS [WeakBridge.wstep_ok], so the walk's post-racy tail is discharged
        by [WeakCert.wstep_eff_confined_pin] verbatim, with no post-racy
        producer of its own. *)
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
Require Import WeakExec.
Require Import WeakBridge.
Require Import WeakCert.
Require Import WeakEff.
Require Import WeakRacy.
Require Import WeakVarCert.
Require Import RiscvLang RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The stale memory and the mirror *)

(** The memory a read of kind [ak] sees.  A read the weak machine PINS
    ([ak_coh] or [ak_latest]) sees the real one; anything else may be stale,
    and the window is where staleness is allowed to show. *)
Definition stale_mem (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    (ak : akinfo) (s : mstate) : gmap Arch.pa (bv 8) :=
  if ak_pins ak then s.(mem) else write_bytes s.(mem) ra rn w.

Lemma stale_mem_pins ra rn w ak s :
  ak_pins ak = true -> stale_mem ra rn w ak s = s.(mem).
Proof. rewrite /stale_mem => -> //. Qed.

Lemma stale_mem_unpinned ra rn w ak s :
  ak_pins ak = false ->
  stale_mem ra rn w ak s = write_bytes s.(mem) ra rn w.
Proof. rewrite /stale_mem => -> //. Qed.

(** [WeakCert.exec_eff], arm for arm.  The ONLY difference is which memory
    the RAM read arm reads. *)
Fixpoint exec_stale (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    {X} (m : M X) (s : mstate) {struct m}
    : option (X * mstate * list weff) :=
  match m with
  | Interface.Ret y => Some (y, s, [])
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * mstate * list weff) with
       | Interface.RegRead r _ => fun k =>
           exec_stale ra rn w (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v => fun k =>
           exec_stale ra rn w (k tt) (set_reg s r v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (v, d') =>
                 exec_stale ra rn w (k (inl (v, None)))
                   (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match read_bytes
                     (stale_mem ra rn w
                        (classify (Interface.ReadReq.access_kind req)) s)
                     (Interface.ReadReq.pa req) n with
             | Some v =>
                 match exec_stale ra rn w (k (inl (v, None))) s with
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
             | Some d' => exec_stale ra rn w (k (inl None))
                            (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match exec_stale ra rn w (k (inl None))
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
       | Interface.InstrAnnounce _   => fun k => exec_stale ra rn w (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => exec_stale ra rn w (k tt) s
       | Interface.Barrier b         => fun k =>
           match exec_stale ra rn w (k tt) s with
           | Some (y, s', es) => Some (y, s', WEbar b :: es)
           | None => None
           end
       | Interface.CacheOp _         => fun k => exec_stale ra rn w (k tt) s
       | Interface.TlbOp _           => fun k => exec_stale ra rn w (k tt) s
       | Interface.TakeException _   => fun k => exec_stale ra rn w (k tt) s
       | Interface.ReturnException _ => fun k => exec_stale ra rn w (k tt) s
       | Interface.TranslationStart _=> fun k => exec_stale ra rn w (k tt) s
       | Interface.TranslationEnd _  => fun k => exec_stale ra rn w (k tt) s
       | Interface.CycleCount        => fun k => exec_stale ra rn w (k tt) s
       | Interface.Message _         => fun k => exec_stale ra rn w (k tt) s
       | Interface.GetCycleCount     => fun k => exec_stale ra rn w (k 0%Z) s
       | _ => fun _ => None
       end) k
  end.

(* ====================================================================== *)
(** ** 2. The composition kit ([WeakEff] §§1–2, restated)

    Same statements, same uses: a proof script that walks a bind spine
    through register reads and writes replays verbatim, and the one step per
    instruction that touches memory uses the trace-concatenating form. *)

Section kit.
  Context (ra : Arch.pa) (rn : N) (w : bv (8 * rn)).

  Lemma exec_stale_returnm {X} (x : X) s :
    exec_stale ra rn w (Defs.returnm x) s = Some (x, s, []).
  Proof. reflexivity. Qed.

  Lemma exec_stale_read_reg (r : register) s :
    exec_stale ra rn w (Defs.read_reg r : M _) s
    = Some (register_lookup r s.(sregs), s, []).
  Proof. reflexivity. Qed.

  Lemma exec_stale_write_reg (r : register) (v : type_of_register r) s :
    exec_stale ra rn w (Defs.write_reg r v : M _) s = Some (tt, set_reg s r v, []).
  Proof. reflexivity. Qed.

  Lemma exec_stale_bind {X Y} (m : M X) (f : X -> M Y) :
    forall s v st es y s' es',
      exec_stale ra rn w m s = Some (v, st, es) ->
      exec_stale ra rn w (f v) st = Some (y, s', es') ->
      exec_stale ra rn w (Defs.bind m f) s = Some (y, s', (es ++ es')%list).
  Proof.
    induction m as [y0 | T oc k IH]; intros s v st es y s' es' Hm Hf.
    - rewrite bind_Ret. simpl in Hm. injection Hm as <- <- <-. by rewrite Hf.
    - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
        try (exact (IH _ _ _ _ _ _ _ _ Hm Hf)).
      + (* MemRead *)
        destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
          exact (IH _ _ _ _ _ _ _ _ Hm Hf).
        * destruct (read_bytes _ _ _) as [v0|]; [|discriminate].
          destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-.
          rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
      + (* MemWrite *)
        destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
          exact (IH _ _ _ _ _ _ _ _ Hm Hf).
        * destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-.
          rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
      + (* Barrier *)
        destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hm as <- <- <-.
        rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
  Qed.

  (** The EQUALITY form.  [WeakEff]'s proof of it goes through
      [exec_eff_exec] to kill the [None] case; here there is no such bridge
      (the mirror does not agree with [RiscvExec.exec] at the window), so it
      is a direct induction — and the memory-touching arms are killed by the
      empty trace rather than by a semantic argument. *)
  Lemma exec_stale_bind_nil {X Y} (m : M X) (f : X -> M Y) s v st :
    exec_stale ra rn w m s = Some (v, st, []) ->
    exec_stale ra rn w (Defs.bind m f) s = exec_stale ra rn w (f v) st.
  Proof.
    revert s. induction m as [y0 | T oc k IH]; intros s Hm.
    - rewrite bind_Ret. simpl in Hm. by injection Hm as <- <-.
    - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
        try (exact (IH _ _ Hm)).
      + (* MemRead: a RAM read leaves a non-empty trace *)
        destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
          exact (IH _ _ Hm).
        * destruct (read_bytes _ _ _) as [v0|]; [|discriminate].
          destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|];
            discriminate.
      + (* MemWrite *)
        destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
          exact (IH _ _ Hm).
        * destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|];
            discriminate.
      + (* Barrier *)
        destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|];
          discriminate.
  Qed.

  Lemma exec_stale_bind0_nil {Y} (m : M unit) (n : M Y) s u st :
    exec_stale ra rn w m s = Some (u, st, []) ->
    exec_stale ra rn w (Defs.bind0 m n) s = exec_stale ra rn w n st.
  Proof.
    intros Hm. unfold Defs.bind0.
    rewrite (exec_stale_bind_nil m _ s u st Hm). by destruct u.
  Qed.

  Lemma exec_stale_bind_cons {X Y} (m : M X) (f : X -> M Y) s v st e y s' es' :
    exec_stale ra rn w m s = Some (v, st, [e]) ->
    exec_stale ra rn w (f v) st = Some (y, s', es') ->
    exec_stale ra rn w (Defs.bind m f) s = Some (y, s', (e :: es')%list).
  Proof. intros Hm Hf. exact (exec_stale_bind m f s v st [e] y s' es' Hm Hf). Qed.

  (** The composite cannot succeed where the tail does not.  (The [None] half
      of the equality form; [WeakEff] gets it from [exec_eff_exec], which the
      mirror has no analogue of.) *)
  Lemma exec_stale_bind_None {X Y} (m : M X) (f : X -> M Y) v st :
    exec_stale ra rn w (f v) st = None ->
    forall s es, exec_stale ra rn w m s = Some (v, st, es) ->
      exec_stale ra rn w (Defs.bind m f) s = None.
  Proof.
    intros Hf. induction m as [y0 | T oc k IH]; intros s es Hm.
    - rewrite bind_Ret. simpl in Hm. by injection Hm as <- <- <-.
    - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
        try (exact (IH _ _ _ Hm)).
      + (* MemRead *)
        destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
          exact (IH _ _ _ Hm).
        * destruct (read_bytes _ _ _) as [v0|]; [|discriminate].
          destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-. by rewrite (IH _ _ _ Hee).
      + (* MemWrite *)
        destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
          exact (IH _ _ _ Hm).
        * destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-. by rewrite (IH _ _ _ Hee).
      + (* Barrier *)
        destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hm as <- <- <-. by rewrite (IH _ _ _ Hee).
  Qed.

  Lemma exec_stale_bind_Some {X Y} (m : M X) (f : X -> M Y) s v st es :
    exec_stale ra rn w m s = Some (v, st, es) ->
    exec_stale ra rn w (Defs.bind m f) s
    = match exec_stale ra rn w (f v) st with
      | Some (y, s', es') => Some (y, s', (es ++ es')%list)
      | None => None
      end.
  Proof.
    intros Hm. destruct (exec_stale ra rn w (f v) st) as [[[y s'] es']|] eqn:Hf.
    - exact (exec_stale_bind m f s v st es y s' es' Hm Hf).
    - exact (exec_stale_bind_None m f v st Hf s es Hm).
  Qed.

End kit.

(* ====================================================================== *)
(** ** 3. THE TRANSFER

    The mirror differs from [WeakCert.exec_eff] only where an UNPINNED read
    meets the window.  A run that has none is the same run — which is what
    lets the walk library be reused for everything except the leaf read
    itself, instead of being mirrored wholesale.

    [acc_wf] is demanded alongside the disjointness because that is what
    [WeakRacy.read_bytes_patch_disj] needs; a caller reads both off the same
    confined footprint it already owns ([WeakCert.acc_wf_window]). *)

Definition trace_off_win (ra : Arch.pa) (rn : N) (es : list weff) : Prop :=
  forall (ak : akinfo) (pa : Arch.pa) (n : N),
    WEread ak pa n ∈ es -> ak_pins ak = false ->
    acc_wf pa n /\ racc_disj ra rn pa n.

Lemma trace_off_win_tail ra rn e es :
  trace_off_win ra rn (e :: es) -> trace_off_win ra rn es.
Proof.
  intros H ak pa n Hin. apply (H ak pa n), elem_of_cons. by right.
Qed.

Lemma trace_off_win_head ra rn ak pa n es :
  trace_off_win ra rn (WEread ak pa n :: es) -> ak_pins ak = false ->
  acc_wf pa n /\ racc_disj ra rn pa n.
Proof. intros H. apply (H ak pa n), elem_of_cons. by left. Qed.

(** A caller that has whole-trace disjointness (the [started] shape) loses
    nothing: [trace_off_win] only ever asks about the unpinned reads. *)
Lemma trace_off_win_of_all ra rn es :
  (forall ak pa n, WEread ak pa n ∈ es -> acc_wf pa n /\ racc_disj ra rn pa n) ->
  trace_off_win ra rn es.
Proof. intros H ak pa n Hin _. exact (H ak pa n Hin). Qed.

(** THE TRANSFER, forward: an [exec_eff] fact about a window-free run is an
    [exec_stale] fact.  This is the direction that reuses the library. *)
Lemma exec_stale_of_exec_eff (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    {X} (m : M X) :
  acc_wf ra rn ->
  forall s x t es,
    exec_eff m s = Some (x, t, es) ->
    trace_off_win ra rn es ->
    exec_stale ra rn w m s = Some (x, t, es).
Proof.
  intros Hracc.
  induction m as [y0 | T oc k IH]; intros s x tf es Hex Hoff.
  - simpl in Hex |- *. exact Hex.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hex Hoff)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hoff).
      * destruct (read_bytes s.(mem) _ _) as [v0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff (k _) s) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        assert (Hmem : read_bytes
                  (stale_mem ra rn w
                     (classify (Interface.ReadReq.access_kind t)) s)
                  (Interface.ReadReq.pa t) n = Some v0).
        { destruct (ak_pins (classify (Interface.ReadReq.access_kind t)))
            eqn:Hpin.
          - by rewrite (stale_mem_pins _ _ _ _ _ Hpin).
          - rewrite (stale_mem_unpinned _ _ _ _ _ Hpin).
            destruct (trace_off_win_head ra rn _ _ _ _ Hoff Hpin)
              as [Hacc Hdisj].
            by rewrite (read_bytes_patch_disj s.(mem) ra rn w _ n
                          Hracc Hacc Hdisj). }
        rewrite Hmem.
        rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
        reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hoff).
      * destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
        reflexivity.
    + (* Barrier *)
      destruct (exec_eff (k tt) s) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
      reflexivity.
Qed.

(** THE TRANSFER, backward: the direction the PRODUCER uses — the tail of a
    family member's run, once the racy read is behind, is an ordinary
    [exec_eff] run, so [WeakCert.wstep_eff_confined_pin] applies to it
    unchanged. *)
Lemma exec_eff_of_exec_stale (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    {X} (m : M X) :
  acc_wf ra rn ->
  forall s x t es,
    exec_stale ra rn w m s = Some (x, t, es) ->
    trace_off_win ra rn es ->
    exec_eff m s = Some (x, t, es).
Proof.
  intros Hracc.
  induction m as [y0 | T oc k IH]; intros s x tf es Hex Hoff.
  - simpl in Hex |- *. exact Hex.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hex Hoff)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hoff).
      * destruct (read_bytes (stale_mem _ _ _ _ _) _ _) as [v0|] eqn:Hrb;
          [|discriminate].
        destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hex as <- <- <-.
        assert (Hmem : read_bytes s.(mem) (Interface.ReadReq.pa t) n = Some v0).
        { destruct (ak_pins (classify (Interface.ReadReq.access_kind t)))
            eqn:Hpin.
          - by rewrite (stale_mem_pins _ _ _ _ _ Hpin) in Hrb.
          - rewrite (stale_mem_unpinned _ _ _ _ _ Hpin) in Hrb.
            destruct (trace_off_win_head ra rn _ _ _ _ Hoff Hpin)
              as [Hacc Hdisj].
            by rewrite (read_bytes_patch_disj s.(mem) ra rn w _ n
                          Hracc Hacc Hdisj) in Hrb. }
        rewrite Hmem.
        rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
        reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hoff).
      * destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hex as <- <- <-.
        rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
        reflexivity.
    + (* Barrier *)
      destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
        [|discriminate].
      injection Hex as <- <- <-.
      rewrite (IH _ _ _ _ _ Hee (trace_off_win_tail _ _ _ _ Hoff)).
      reflexivity.
Qed.

(** THE ONE ARM THAT IS NOT A TRANSFER: an unpinned read OF the window
    returns the racy word.  (The family member indexed by [w] returns [w] —
    which is what makes the family the right shape rather than merely a
    sound one, exactly as in [WeakVarCert] §4.) *)
Lemma read_bytes_stale_win (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    (ak : akinfo) (s : mstate) :
  acc_wf ra rn -> ak_pins ak = false ->
  read_bytes (stale_mem ra rn w ak s) ra rn = Some w.
Proof.
  intros Hracc Hpin. rewrite (stale_mem_unpinned _ _ _ _ _ Hpin).
  exact (read_bytes_of_bytes (write_bytes s.(mem) ra rn w) ra rn w
           (fun j Hj => write_bytes_lookup_at s.(mem) ra rn w j Hracc Hj)).
Qed.

(* ====================================================================== *)
(** ** 4. The phase-[false] embedding

    With the disjointness parameter at [True], the phase-[false] peel IS
    [WeakBridge.wstep_ok]: the off-window disjunct's first conjunct is
    vacuous, the racy disjunct is refuted by the phase, and the write arm
    differs only by the phase bit it already has.  So the walk's POST-RACY
    tail needs no producer of its own — [WeakCert.wstep_eff_confined_pin]
    (through §3's backward transfer) discharges it. *)

Definition wD_any : Arch.pa -> N -> Prop := fun _ _ => True.

Lemma wstep_ok_racy_false_of_wstep_ok (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) {X} (m : M X) :
  forall s, wstep_ok tid m s ->
    wstep_ok_racy tid ra rn rak Φ wD_any false m s.
Proof.
  induction m as [y0 | T oc k IH]; intros s Hok.
  - exact I.
  - destruct oc; simpl in Hok |- *;
      try (exact (IH _ _ Hok));
      try (exact Hok);
      try (exact I).
    + (* MemRead *)
      destruct (dev_addr _).
      * intros v d' Hdr. exact (IH _ _ (Hok v d' Hdr)).
      * destruct Hok as (Hacc & Hpin & Hk).
        split; [exact Hacc|]. left. split_and!.
        -- exact I.
        -- exact Hpin.
        -- intros v Hv. exact (IH _ _ (Hk v Hv)).
    + (* MemWrite *)
      destruct (dev_addr _).
      * intros d' Hdw. exact (IH _ _ (Hok d' Hdw)).
      * destruct Hok as (Hacc & Hk).
        split_and!; [reflexivity|exact Hacc|exact I|exact (IH _ _ Hk)].
Qed.

(** WHAT THE CAS RE-READ COSTS IN THE PEEL, in one sentence: nothing new.
    Its kind pins ([ak_pins (AkInfo false true false) = true]), so the
    off-window disjunct's pinnedness obligation is vacuous, [D] is [wD_any],
    and its continuation is demanded at [coh_ts] — the coherence-latest word,
    which is exactly what the mirror's REAL memory supplies (§1). The window
    read that does cost something is the PLAIN one, and it is the racy arm. *)

(* ====================================================================== *)
(** ** 5. THE PRODUCER

    [WeakVarCert.wstep_ok_racy_true_of_confined] with the family taken at
    [exec_stale] instead of at [exec_eff]-over-a-patched-memory.  Two things
    change, and they are the whole point:

    - a read of the WINDOW at a PINNING kind — the walk's CAS re-read — now
      has an arm.  It reads the mirror's REAL memory, so its value is the
      confined memory's, i.e. the coherence-latest word, which is exactly
      what the peel's off-window disjunct demands.  Under the old family (one
      patched memory per racy value) it returned the racy value instead, and
      that is precisely why shape 4 was unproducible;
    - the tail after the racy read goes to [WeakCert.wstep_eff_confined_pin]
      at the UNPATCHED memory (through §3's backward transfer and §4's
      embedding) rather than to a post-racy producer of its own.  With [D] at
      [wD_any] the phase-[false] peel IS [wstep_ok], so there is nothing else
      to prove.

    The trace premise is [trace_stale], the [WeakVarCert.trace_racy] analogue:
    before the racy read every read is either PINNED (any address) or
    disjoint; a RAM write is still refuted rather than unprovable (the peel's
    write arm demands [b = false]); and AFTER it, only the unpinned reads have
    to stay off the window — which is what admits the CAS pair. *)

Fixpoint trace_stale (rak : akinfo) (ra : Arch.pa) (rn : N) (es : list weff)
    : Prop :=
  match es with
  | [] => True
  | WEread ak pa n :: es' =>
      (ak_pins ak = true /\ trace_stale rak ra rn es')
      \/ (ak_pins ak = false /\ racc_disj ra rn pa n /\ trace_stale rak ra rn es')
      \/ (ak = rak /\ pa = ra /\ n = rn /\ trace_off_win ra rn es')
  | WEwrite _ _ _ _ :: _ => False
  | WEbar _ :: es' => trace_stale rak ra rn es'
  end.

(** The three eliminations, each keyed on data the MONAD fixes (the read's
    kind, address and width) rather than on the patch value — which is what
    lets the induction pick one arm while holding the whole family. *)
Lemma trace_stale_pin_tail rak ra rn ak pa n es :
  ak_pins rak = false -> ak_pins ak = true ->
  trace_stale rak ra rn (WEread ak pa n :: es) -> trace_stale rak ra rn es.
Proof.
  intros Hrk Hpin [[_ Ht]|[(Hnp & _ & _)|(Hak & _)]];
    [exact Ht|congruence|subst ak; congruence].
Qed.

Lemma trace_stale_disj_tail rak ra rn ak pa n es :
  (0 < rn)%N -> ak_pins ak = false -> racc_disj ra rn pa n ->
  trace_stale rak ra rn (WEread ak pa n :: es) -> trace_stale rak ra rn es.
Proof.
  intros Hrn Hnp Hd [[Hpin _]|[(_ & _ & Ht)|(_ & Hpa & Hn & _)]];
    [congruence|exact Ht|].
  subst pa n. by destruct (racc_disj_irrefl ra rn Hrn Hd).
Qed.

Lemma trace_stale_win rak ra rn ak pa n es :
  ak_pins ak = false -> ~ racc_disj ra rn pa n ->
  trace_stale rak ra rn (WEread ak pa n :: es) ->
  ak = rak /\ pa = ra /\ n = rn /\ trace_off_win ra rn es.
Proof.
  intros Hnp Hnd [[Hpin _]|[(_ & Hd & _)|H]];
    [congruence|by destruct (Hnd Hd)|exact H].
Qed.

(** Off the window, [trace_pin_off]'s weakening IS [WeakCert.trace_pin] —
    the [WeakVarCert.trace_pin_of_off] move, at [trace_off_win]. *)
Lemma trace_pin_of_off_win s ra rn es :
  trace_off_win ra rn es -> trace_pin_off s ra rn es -> trace_pin s es.
Proof.
  intros Hd Hp ak pa n Hin Hnp j Hj.
  exact (Hp ak pa n Hin Hnp (proj2 (Hd ak pa n Hin Hnp)) j Hj).
Qed.

Lemma wstep_ok_racy_true_of_stale (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) {X} (m : M X) :
  acc_wf ra rn ->
  (0 < rn)%N ->
  ak_pins rak = false ->
  (exists w0 : bv (8 * rn), Φ (fun j : nat => nth_byte w0 j)) ->
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (W : gset Arch.pa),
    wlog_wf (wm_log s) ->
    (forall a, a ∈ W -> pa_z a <> 0) ->
    (forall j : nat, (j < N.to_nat rn)%nat -> pa_add ra j ∈ W) ->
    dom mm ⊆ W ->
    mm ⊆ wflat (wm_img s) (wm_log s) ->
    (forall w : bv (8 * rn), Φ (fun j : nat => nth_byte w j) ->
       exists (x : X) (t' : mstate) (es : list weff),
         exec_stale ra rn w m (MState (wm_regs s) mm (wm_dev s))
           = Some (x, t', es) /\
         dom (mem t') ⊆ W /\
         trace_pin_off s ra rn es /\
         trace_stale rak ra rn es) ->
    wstep_ok_racy tid ra rn rak Φ wD_any true m s.
Proof.
  intros Hracc Hrn Hrk [w0 HΦ0].
  assert (Hrdw : forall (u : bv (8 * rn)) (mp : gmap Arch.pa (bv 8)),
            read_bytes (write_bytes mp ra rn u) ra rn = Some u).
  { intros u mp. apply read_bytes_of_bytes. intros j Hj.
    exact (write_bytes_lookup_at mp ra rn u j Hracc Hj). }
  induction m as [y|T oc k IH]; intros s mm W Hwf HW0 Hwin Hdom Hsub Hfam.
  - exact I.
  - destruct (Hfam w0 HΦ0) as (x0 & t0 & es0 & Hex0 & Hd0 & Hp0 & Hr0).
    destruct oc; simpl in Hex0, Hfam |- *; try discriminate;
      try (exact (IH _ s mm W Hwf HW0 Hwin Hdom Hsub Hfam)).
    + (* RegWrite *)
      apply (IH tt (wset_reg s reg regval) mm W Hwf HW0 Hwin Hdom Hsub).
      intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
      exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
      apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[wd dd]|] eqn:Hdr;
          rewrite ?Hd ?Hdr /= in Hex0; [|discriminate].
        intros wv d' Hdr'. rewrite ?Hdr in Hdr'. simplify_eq.
        apply (IH _ (wset_dev s d') mm W Hwf HW0 Hwin Hdom Hsub).
        intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
        rewrite ?Hd ?Hdr /= in Hex1.
        exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
        apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
      * (* RAM.  THREE arms, decided by the kind and the footprint. *)
        destruct (ak_pins (classify (Interface.ReadReq.access_kind t))) eqn:Hpin.
        -- (* PINNED — the CAS re-read's arm.  The mirror reads the REAL
              memory, so the value is the confined one whether or not the
              address is the window. *)
           rewrite (stale_mem_pins ra rn w0 _ _ Hpin) /= in Hex0.
           destruct (read_bytes mm (Interface.ReadReq.pa t) n) as [v0|] eqn:Hrb0;
             rewrite ?Hrb0 /= in Hex0; [|discriminate].
           assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                     pa_add (Interface.ReadReq.pa t) j ∈ W)
             by (intros j Hj; apply Hdom, (read_bytes_dom _ _ _ v0 Hrb0 j Hj)).
           assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
             by (apply (acc_wf_window W); [exact HW0|exact Hin]).
           destruct (exec_stale ra rn w0 (k (inl (v0, None)))
                       (MState (wm_regs s) mm (wm_dev s)))
             as [[[x1 t1] es1]|] eqn:Hee0; rewrite ?Hee0 /= in Hex0;
             [|discriminate].
           injection Hex0 as <- <- <-.
           assert (Hwrb : wread_bytes s
                            (classify (Interface.ReadReq.access_kind t))
                            (Interface.ReadReq.pa t) n
                            (coh_ts s (Interface.ReadReq.pa t) n) = Some v0).
           { rewrite (wread_bytes_read_bytes s _ _ n Hwf Hacc).
             exact (read_bytes_mono mm _ _ _ v0 Hsub Hrb0). }
           split; [exact Hacc|]. left. split_and!.
           ++ exact I.
           ++ intros Hnp. congruence.
           ++ intros v Hv. rewrite Hwrb in Hv. injection Hv as <-.
              apply (IH _ (wread_post s
                             (classify (Interface.ReadReq.access_kind t))
                             (Interface.ReadReq.pa t)
                             (coh_ts s (Interface.ReadReq.pa t) n)) mm W
                       (wlog_wf_read_post _ _ _ _ Hwf) HW0 Hwin Hdom
                       ltac:(by rewrite wread_post_img wread_post_log)).
              intros u Hu.
              destruct (Hfam u Hu) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
              rewrite ?Hd (stale_mem_pins ra rn u _ _ Hpin) /= ?Hrb0 /= in Hex2.
              destruct (exec_stale ra rn u (k (inl (v0, None)))
                          (MState (wm_regs s) mm (wm_dev s)))
                as [[[x3 t3] es3]|] eqn:Hee2;
                rewrite ?Hee2 /= in Hex2; [|discriminate].
              injection Hex2 as <- <- <-.
              exists x3, t3, es3. split_and!.
              ** by rewrite wread_post_regs wread_post_dev.
              ** exact Hd2.
              ** apply (trace_pin_off_mono s);
                   [apply wread_post_log|apply wread_post_ws_le|].
                 exact (trace_pin_off_tail s ra rn _ es3 Hp2).
              ** exact (trace_stale_pin_tail rak ra rn _ _ n es3 Hrk Hpin Hr2).
        -- rewrite (stale_mem_unpinned ra rn w0 _ _ Hpin) /= in Hex0.
           destruct (read_bytes (write_bytes mm ra rn w0)
                       (Interface.ReadReq.pa t) n) as [v0|] eqn:Hrb0;
             rewrite ?Hrb0 /= in Hex0; [|discriminate].
           assert (Hdomp : dom (write_bytes mm ra rn w0) ⊆ W)
             by (apply write_bytes_dom_sub; [exact Hdom|exact Hwin]).
           assert (Hin : forall j : nat, (j < N.to_nat n)%nat ->
                     pa_add (Interface.ReadReq.pa t) j ∈ W)
             by (intros j Hj; apply Hdomp, (read_bytes_dom _ _ _ v0 Hrb0 j Hj)).
           assert (Hacc : acc_wf (Interface.ReadReq.pa t) n)
             by (apply (acc_wf_window W); [exact HW0|exact Hin]).
           destruct (exec_stale ra rn w0 (k (inl (v0, None)))
                       (MState (wm_regs s) mm (wm_dev s)))
             as [[[x1 t1] es1]|] eqn:Hee0; rewrite ?Hee0 /= in Hex0;
             [|discriminate].
           injection Hex0 as <- <- <-.
           split; [exact Hacc|].
           assert (Hdec : racc_disj ra rn (Interface.ReadReq.pa t) n \/
                          ~ racc_disj ra rn (Interface.ReadReq.pa t) n)
             by (rewrite /racc_disj; lia).
           destruct Hdec as [Hdisj|Hndisj].
           ++ (* UNPINNED, OFF the window: [wstep_ok]'s own arm *)
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
              ** exact I.
              ** intros _ j Hj.
                 exact (trace_pin_off_head s ra rn _ _ _ es1 Hp0 Hpin Hdisj j Hj).
              ** intros v Hv. rewrite Hwrb in Hv. injection Hv as <-.
                 apply (IH _ (wread_post s
                                (classify (Interface.ReadReq.access_kind t))
                                (Interface.ReadReq.pa t)
                                (coh_ts s (Interface.ReadReq.pa t) n)) mm W
                          (wlog_wf_read_post _ _ _ _ Hwf) HW0 Hwin Hdom
                          ltac:(by rewrite wread_post_img wread_post_log)).
                 intros u Hu.
                 destruct (Hfam u Hu) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
                 rewrite ?Hd (stale_mem_unpinned ra rn u _ _ Hpin) /=
                         ?(Hrbu u) /= in Hex2.
                 destruct (exec_stale ra rn u (k (inl (v0, None)))
                             (MState (wm_regs s) mm (wm_dev s)))
                   as [[[x3 t3] es3]|] eqn:Hee2;
                   rewrite ?Hee2 /= in Hex2; [|discriminate].
                 injection Hex2 as <- <- <-.
                 exists x3, t3, es3. split_and!.
                 --- by rewrite wread_post_regs wread_post_dev.
                 --- exact Hd2.
                 --- apply (trace_pin_off_mono s);
                       [apply wread_post_log|apply wread_post_ws_le|].
                     exact (trace_pin_off_tail s ra rn _ es3 Hp2).
                 --- exact (trace_stale_disj_tail rak ra rn _ _ n es3 Hrn Hpin
                              Hdisj Hr2).
           ++ (* THE RACY READ.  The member indexed by [w] returns [w], and
                 its tail is an ordinary confined run at the UNPATCHED
                 memory — §3's backward transfer, then §4's embedding. *)
              right.
              destruct (trace_stale_win rak ra rn _ _ n es1 Hpin Hndisj Hr0)
                as (Hak & Hpa & Hn & _).
              subst n. rewrite Hpa Hak.
              split_and!; [reflexivity|reflexivity|reflexivity|reflexivity|].
              intros ts w Hread HΦw.
              destruct (Hfam w HΦw) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
              rewrite ?Hd (stale_mem_unpinned ra rn w _ _ Hpin) /= ?Hpa
                      ?(Hrdw w mm) /= in Hex2.
              destruct (exec_stale ra rn w (k (inl (w, None)))
                          (MState (wm_regs s) mm (wm_dev s)))
                as [[[x3 t3] es3]|] eqn:Hee2;
                rewrite ?Hee2 /= in Hex2; [|discriminate].
              injection Hex2 as <- <- <-.
              destruct (trace_stale_win rak ra rn _ ra rn es3 Hpin
                          ltac:(rewrite Hak in Hpin;
                                exact (racc_disj_irrefl ra rn Hrn)) Hr2)
                as (_ & _ & _ & Hoff3).
              apply (wstep_ok_racy_false_of_wstep_ok tid ra rn rak Φ).
              apply (wstep_eff_confined_pin tid (k (inl (w, None)))
                       (wread_post s rak ra ts) mm W x3 t3 es3
                       (wlog_wf_read_post _ _ _ _ Hwf) HW0).
              ** apply (trace_pin_mono s);
                   [apply wread_post_log|apply wread_post_ws_le|].
                 apply (trace_pin_of_off_win s ra rn es3 Hoff3).
                 exact (trace_pin_off_tail s ra rn _ es3 Hp2).
              ** exact Hdom.
              ** by rewrite wread_post_img wread_post_log.
              ** exact Hd2.
              ** rewrite wread_post_regs wread_post_dev.
                 exact (exec_eff_of_exec_stale ra rn w _ Hracc _ _ _ _ Hee2 Hoff3).
    + (* MemWrite: a RAM write before the racy read is REFUTED *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [dd|] eqn:Hdw;
          rewrite ?Hd ?Hdw /= in Hex0; [|discriminate].
        intros d' Hdw'. rewrite ?Hdw in Hdw'. simplify_eq.
        apply (IH _ (wset_dev s d') mm W Hwf HW0 Hwin Hdom Hsub).
        intros u Hu. destruct (Hfam u Hu) as (x1 & t1 & es1 & Hex1 & Hd1 & Hp1 & Hr1).
        rewrite ?Hd ?Hdw /= in Hex1.
        exists x1, t1, es1. split_and!; [exact Hex1|exact Hd1| |exact Hr1].
        apply (trace_pin_off_mono s); [reflexivity|reflexivity|exact Hp1].
      * exfalso.
        destruct (exec_stale ra rn w0 (k (inl None))
                    (MState (wm_regs s)
                       (write_bytes mm (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t))
                       (wm_dev s)))
          as [[[x1 t1] es1]|] eqn:Hee0;
          rewrite ?Hd ?Hee0 /= in Hex0; [|discriminate].
        injection Hex0 as <- <- <-. exact Hr0.
    + (* Barrier *)
      destruct (exec_stale ra rn w0 (k tt)
                  (MState (wm_regs s) mm (wm_dev s)))
        as [[[x1 t1] es1]|] eqn:Hee0; rewrite ?Hee0 /= in Hex0; [|discriminate].
      injection Hex0 as <- <- <-.
      apply (IH tt (wset_ws s (barrier_post (wm_ws s) b)) mm W Hwf HW0 Hwin
               Hdom Hsub).
      intros u Hu. destruct (Hfam u Hu) as (x2 & t2 & es2 & Hex2 & Hd2 & Hp2 & Hr2).
      destruct (exec_stale ra rn u (k tt) (MState (wm_regs s) mm (wm_dev s)))
        as [[[x3 t3] es3]|] eqn:Hee2; rewrite ?Hee2 /= in Hex2; [|discriminate].
      injection Hex2 as <- <- <-.
      exists x3, t3, es3. split_and!.
      * exact Hee2.
      * exact Hd2.
      * apply (trace_pin_off_mono s); [reflexivity|apply barrier_post_le|].
        exact (trace_pin_off_tail s ra rn _ es3 Hp2).
      * exact Hr2.
Qed.

(** The [wmem_restrict] instance — the shape a certificate carries. *)
Lemma wstep_ok_racy_true_of_stale_window (tid : option nat) (ra : Arch.pa)
    (rn : N) (rak : akinfo) (Φ : (nat -> bv 8) -> Prop) {X} (m : M X)
    (s : wmstate) (W : gset Arch.pa) :
  acc_wf ra rn ->
  (0 < rn)%N ->
  ak_pins rak = false ->
  (exists w0 : bv (8 * rn), Φ (fun j : nat => nth_byte w0 j)) ->
  wlog_wf (wm_log s) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall j : nat, (j < N.to_nat rn)%nat -> pa_add ra j ∈ W) ->
  (forall w : bv (8 * rn), Φ (fun j : nat => nth_byte w j) ->
     exists (x : X) (t' : mstate) (es : list weff),
       exec_stale ra rn w m
         (MState (wm_regs s) (wmem_restrict s W) (wm_dev s)) = Some (x, t', es) /\
       dom (mem t') ⊆ W /\
       trace_pin_off s ra rn es /\
       trace_stale rak ra rn es) ->
  wstep_ok_racy tid ra rn rak Φ wD_any true m s.
Proof.
  intros Hracc Hrn Hrk HΦ Hwf HW0 Hwin Hfam.
  exact (wstep_ok_racy_true_of_stale tid ra rn rak Φ m Hracc Hrn Hrk HΦ s
           (wmem_restrict s W) W Hwf HW0 Hwin (wmem_restrict_dom s W)
           (wmem_restrict_sub s W) Hfam).
Qed.
