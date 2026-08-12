(** * WeakEff.v — the effect-trace toolkit (M4-prep item (ii))

    WHAT THIS IS FOR.  [WeakCert] reduced a per-instruction step certificate
    to ONE obligation, [WeakCert.wP_eff tid es σ]: "the confined run succeeds
    with effect trace [es]", from which every [wQ_*] is view arithmetic over
    [es].  What it did NOT say is how a leaf OBTAINS that fact.  The SC side
    has an [exec]-level library lemma per instruction shape; the instrumented
    interpreter [WeakCert.exec_eff] is an arm-for-arm mirror of [exec], so the
    naive answer — "re-run the library lemma at [exec_eff]" — means mirroring
    the whole fetch/decode/execute chain, [RiscvTryStep.execR] and all.  That
    is the M4 sweep's single biggest cost item, and this file is what shrinks
    it.

    FOUR MOVES, in increasing order of payoff.

    §2  THE COMPOSITION KIT.  [exec_eff_bind_nil] / [exec_eff_bind0_nil] are
        DROP-IN replacements for [RiscvExec.exec_bind_Some] /
        [exec_bind0_Some]: an existing SC proof script that walks a bind spine
        through register reads and writes replays verbatim at [exec_eff], with
        no trace bookkeeping at all, because every one of those steps has an
        EMPTY trace.  [exec_eff_bind] is the general (trace-concatenating)
        form, for the one step per instruction that does touch memory.

    §3  THE MEMORY FRAME.  A run whose trace touches no byte neither reads nor
        writes memory, so it runs identically at ANY memory
        ([exec_eff_mem_frame]).  This is what transports a fact proved at one
        memory to the confined memory [WeakCert.wmem_restrict] that the
        certificate is stated at.

    §4  THE EMPTY-MEMORY DETECTOR, and it is the money lemma.
        [exec]'s RAM read arm returns [None] on a byte the map does not
        contain, and its RAM write arm GROWS the map's domain.  So if a
        program runs to completion at the EMPTY memory and ends with an empty
        domain, it performed no RAM access of positive width — a fact about
        the run that needs no walk of the program, only the SC library lemma
        one already has, instantiated at [∅].  [exec_eff_quiet_of_empty]
        packages that with §3: from ONE [exec] fact at the empty memory, the
        instrumented run at ANY memory succeeds, with the same value and
        registers, an unchanged memory, and a QUIET trace.

        THE CONSEQUENCE FOR M4: the decoder, every ALU/branch/control
        [execute], and the whole [try_step] wrapper are memory-free, so their
        [exec_eff] facts are FREE — no mirroring, no walk, one [apply].  What
        is left to mirror per instruction is exactly the memory-touching part:
        the fetch (once, shared) and the one load/store/AMO [execute] of the
        shape being ported.

    §5  QUIET TRACES AND [wQ_quiet].  A quiet trace appends only BYTE-LESS
        messages to the log (a zero-width write's [WeakInterp.wwrite_msg] has
        empty [wm_data]), so it changes no byte's latest write and only raises
        views — everything the state interpretation's [wlat_interp] conjunct
        needs.  [wQ_quiet] is the certificate-level [Q] of an instruction with
        no memory effect of its own, and it is what a BRANCH leaf carries.

    §6  THE CERTIFICATES, GENERALISED.  [WeakCert]'s four certificates pin the
        trace to a 2- or 3-element list beginning with THE fetch read.  That is
        stronger than the arithmetic needs, and it makes the fetch's exact
        trace a per-instruction obligation.  The versions here surround the
        instruction's one access with ARBITRARY QUIET prefixes and suffixes:
        reads and barriers only ever raise views, and all four [wQ_*]s are
        monotone in exactly that direction.  So the fetch no longer has to be
        pinned to one element — only shown quiet.

    NOTE ON ZERO-WIDTH ACCESSES.  The Sail interface's [MemRead]/[MemWrite]
    carry an arbitrary [n : N], and a zero-width access is invisible to [exec]
    (it reads nothing and writes nothing), so no argument over [exec] can rule
    one out.  Rather than pretend otherwise, [weff_quiet] ADMITS zero-width
    accesses and [wQ_quiet] is stated to tolerate them: they append a message
    that writes no byte, which is harmless to every consumer.  The generated
    model emits none, but nothing here depends on that.
*)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.base_logic.lib Require Import iprop ghost_map.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakViolation.
Require Import WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr.
Require Import WeakCert.
Require Import RiscvLang RiscvPtsto RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. Zero-width memory primitives

    Stated as their own lemmas rather than [subst]ed in place: the width of a
    [MemRead]/[MemWrite] outcome appears in the TYPE of its request and of the
    continuation, so substituting it inside the induction is a dependent
    rewrite; keeping the equation at the primitive avoids that entirely. *)

Lemma read_bytes_zero (mm mm' : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) :
  (n = 0)%N -> read_bytes mm pa n = read_bytes mm' pa n.
Proof. intros ->. reflexivity. Qed.

Lemma write_bytes_zero {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (v : bv w) :
  (n = 0)%N -> write_bytes mm pa n v = mm.
Proof. intros ->. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. The trivial arms of [exec_eff]

    Every non-memory outcome of the interface leaves the trace alone; these
    are the [exec_eff] twins of [RiscvExec.exec_read_reg] / [exec_write_reg] /
    [exec_returnm], and they are all [reflexivity]. *)

Lemma exec_eff_returnm {X} (x : X) s : exec_eff (Defs.returnm x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Lemma exec_eff_read_reg (r : register) s :
  exec_eff (Defs.read_reg r : M _) s = Some (register_lookup r s.(sregs), s, []).
Proof. reflexivity. Qed.

Lemma exec_eff_write_reg (r : register) (v : type_of_register r) s :
  exec_eff (Defs.write_reg r v : M _) s = Some (tt, set_reg s r v, []).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 2. THE COMPOSITION KIT *)

Lemma exec_eff_bind {X Y} (m : M X) (f : X -> M Y) :
  forall s v st es y s' es',
    exec_eff m s = Some (v, st, es) ->
    exec_eff (f v) st = Some (y, s', es') ->
    exec_eff (Defs.bind m f) s = Some (y, s', (es ++ es')%list).
Proof.
  induction m as [y0 | T oc k IH]; intros s v st es y s' es' Hm Hf.
  - rewrite bind_Ret. simpl in Hm. injection Hm as <- <- <-. by rewrite Hf.
  - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ _ _ _ _ Hm Hf)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ _ _ _ Hm Hf).
      * destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
        destruct (exec_eff (k _) s) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hm as <- <- <-.
        rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ _ _ _ Hm Hf).
      * destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hm as <- <- <-.
        rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
    + (* Barrier *)
      destruct (exec_eff (k tt) s) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hm as <- <- <-.
      rewrite (IH _ _ _ _ _ _ _ _ Hee Hf). reflexivity.
Qed.

Lemma exec_eff_bind_nil {X Y} (m : M X) (f : X -> M Y) s v st :
  exec_eff m s = Some (v, st, []) ->
  exec_eff (Defs.bind m f) s = exec_eff (f v) st.
Proof.
  intros Hm. destruct (exec_eff (f v) st) as [[[y s'] es']|] eqn:Hf.
  - exact (exec_eff_bind m f s v st [] y s' es' Hm Hf).
  - destruct (exec_eff (Defs.bind m f) s) as [[[y s'] es']|] eqn:Hb; [|reflexivity].
    exfalso.
    pose proof (exec_eff_exec _ _ _ _ _ Hb) as Hbe.
    pose proof (exec_eff_exec _ _ _ _ _ Hm) as Hme.
    rewrite exec_bind Hme in Hbe.
    destruct (exec_exec_eff _ _ _ _ Hbe) as [es0 Hee]. by rewrite Hee in Hf.
Qed.

Lemma exec_eff_bind0_nil {Y} (m : M unit) (n : M Y) s u st :
  exec_eff m s = Some (u, st, []) ->
  exec_eff (Defs.bind0 m n) s = exec_eff n st.
Proof.
  intros Hm. unfold Defs.bind0. rewrite (exec_eff_bind_nil m _ s u st Hm).
  by destruct u.
Qed.

(** The bind form for the ONE step of an instruction that touches memory. *)
Lemma exec_eff_bind_cons {X Y} (m : M X) (f : X -> M Y) s v st e y s' es' :
  exec_eff m s = Some (v, st, [e]) ->
  exec_eff (f v) st = Some (y, s', es') ->
  exec_eff (Defs.bind m f) s = Some (y, s', (e :: es')%list).
Proof. intros Hm Hf. exact (exec_eff_bind m f s v st [e] y s' es' Hm Hf). Qed.

(* ====================================================================== *)
(** ** 3. QUIET TRACES, and THE MEMORY FRAME *)

Definition weff_quiet (e : weff) : Prop :=
  match e with
  | WEbar _ => True
  | WEread _ _ n => (n = 0)%N
  | WEwrite _ _ n _ => (n = 0)%N
  end.

Definition quiet_trace (es : list weff) : Prop := Forall weff_quiet es.

Lemma quiet_trace_nil : quiet_trace [].
Proof. constructor. Qed.

Lemma quiet_trace_cons_inv e es :
  quiet_trace (e :: es) -> weff_quiet e /\ quiet_trace es.
Proof. intros H. by apply Forall_cons_1 in H. Qed.

Lemma quiet_trace_app es1 es2 :
  quiet_trace es1 -> quiet_trace es2 -> quiet_trace (es1 ++ es2).
Proof. intros H1 H2. by apply Forall_app. Qed.

Lemma quiet_trace_app_inv es1 es2 :
  quiet_trace (es1 ++ es2) -> quiet_trace es1 /\ quiet_trace es2.
Proof. intros H. by apply Forall_app in H. Qed.

(** A quiet run does not look at memory and does not change it. *)
Lemma exec_eff_mem_frame {X} (m : M X) :
  forall rs mm1 d x t' es,
    exec_eff m (MState rs mm1 d) = Some (x, t', es) ->
    quiet_trace es ->
    mem t' = mm1 /\
    forall mm2, exec_eff m (MState rs mm2 d)
                = Some (x, MState (sregs t') mm2 (mdev t'), es).
Proof.
  induction m as [y|T oc k IH]; intros rs mm1 d x t' es Hex Hq.
  - simpl in Hex. injection Hex as <- <- <-. split; [reflexivity|].
    intros mm2. reflexivity.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ _ _ Hex Hq)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        destruct (IH _ _ _ _ _ _ _ Hex Hq) as [Hm Hall].
        split; [exact Hm|]. intros mm2. exact (Hall mm2).
      * destruct (read_bytes mm1 _ n) as [w0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        destruct (quiet_trace_cons_inv _ _ Hq) as [Hn Hq0].
        destruct (IH _ _ _ _ _ _ _ Hee Hq0) as [Hm Hall].
        split; [exact Hm|]. intros mm2.
        rewrite -(read_bytes_zero mm1 mm2 _ n Hn) Hrb (Hall mm2). reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        destruct (IH _ _ _ _ _ _ _ Hex Hq) as [Hm Hall].
        split; [exact Hm|]. intros mm2. exact (Hall mm2).
      * destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        destruct (quiet_trace_cons_inv _ _ Hq) as [Hn Hq0].
        rewrite (write_bytes_zero mm1 _ n _ Hn) in Hee.
        destruct (IH _ _ _ _ _ _ _ Hee Hq0) as [Hm Hall].
        split; [exact Hm|]. intros mm2.
        rewrite (write_bytes_zero mm2 _ n _ Hn) (Hall mm2). reflexivity.
    + (* Barrier *)
      destruct (exec_eff (k tt) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      destruct (quiet_trace_cons_inv _ _ Hq) as [_ Hq0].
      destruct (IH _ _ _ _ _ _ _ Hee Hq0) as [Hm Hall].
      split; [exact Hm|]. intros mm2. rewrite (Hall mm2). reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. THE EMPTY-MEMORY DETECTOR *)

Lemma exec_eff_empty_quiet {X} (m : M X) :
  forall s x t' es,
    exec_eff m s = Some (x, t', es) ->
    mem s = ∅ -> dom (mem t') = ∅ ->
    quiet_trace es.
Proof.
  induction m as [y|T oc k IH]; intros s x t' es Hex Hms Hdom.
  - simpl in Hex. injection Hex as <- <- <-. constructor.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hex Hms Hdom)).
    + (* MemRead *)
      destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w0 d']|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hms Hdom).
      * destruct (read_bytes (mem s) _ n) as [w0|] eqn:Hrb; [|discriminate].
        destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        assert (Hn : (n = 0)%N).
        { destruct (N.eq_dec n 0%N) as [->|Hne]; [reflexivity|exfalso].
          assert (Hlt : (0 < N.to_nat n)%nat) by lia.
          pose proof (read_bytes_dom (mem s) _ n w0 Hrb 0%nat Hlt) as Hin.
          rewrite Hms dom_empty_L in Hin. by apply not_elem_of_empty in Hin. }
        constructor; [exact Hn|]. exact (IH _ _ _ _ _ Hee Hms Hdom).
    + (* MemWrite *)
      destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
        exact (IH _ _ _ _ _ Hex Hms Hdom).
      * destruct (exec_eff (k _) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
        injection Hex as <- <- <-.
        pose proof (exec_dom_mono _ _ _ _ (exec_eff_exec _ _ _ _ _ Hee)) as Hsub.
        simpl in Hsub.
        assert (Hn : (n = 0)%N).
        { destruct (N.eq_dec n 0%N) as [->|Hne]; [reflexivity|exfalso].
          assert (Hlt : (0 < N.to_nat n)%nat) by lia.
          lazymatch type of Hsub with
          | dom (write_bytes ?mm ?pa ?nn ?v) ⊆ _ =>
              pose proof (write_bytes_dom mm pa nn v 0%nat Hlt) as Hin
          end.
          apply Hsub in Hin. rewrite Hdom in Hin.
          by apply not_elem_of_empty in Hin. }
        constructor; [exact Hn|].
        refine (IH _ _ _ _ _ Hee _ Hdom).
        simpl. rewrite (write_bytes_zero (mem s) _ n _ Hn). exact Hms.
    + (* Barrier *)
      destruct (exec_eff (k tt) _) as [[[x0 t0] es0]|] eqn:Hee; [|discriminate].
      injection Hex as <- <- <-.
      constructor; [exact I|]. exact (IH _ _ _ _ _ Hee Hms Hdom).
Qed.

(** THE MONEY LEMMA.  From ONE [exec] fact at the empty memory: the
    instrumented run at ANY memory succeeds with the same value, the same
    registers and device state, an UNCHANGED memory, and a QUIET trace.

    This is what makes the decoder, every register-only [execute] and the
    whole [try_step] wrapper free at [exec_eff]: their SC library lemmas are
    stated at an arbitrary state, so instantiating one at [MState rs ∅ d]
    costs a single [apply]. *)
Lemma exec_eff_quiet_of_empty {X} (m : M X) rs d x t' :
  exec m (MState rs ∅ d) = Some (x, t') ->
  dom (mem t') = ∅ ->
  exists es, quiet_trace es /\
    forall mm, exec_eff m (MState rs mm d)
               = Some (x, MState (sregs t') mm (mdev t'), es).
Proof.
  intros Hex Hdom.
  destruct (exec_exec_eff _ _ _ _ Hex) as [es Hee].
  assert (Hq : quiet_trace es)
    by exact (exec_eff_empty_quiet m (MState rs ∅ d) x t' es Hee eq_refl Hdom).
  exists es. split; [exact Hq|].
  intros mm.
  destruct (exec_eff_mem_frame m rs ∅ d x t' es Hee Hq) as [_ Hall].
  exact (Hall mm).
Qed.

(* ====================================================================== *)
(** ** 5. WHAT A QUIET TRACE DOES TO THE STATE

    A quiet trace appends only BYTE-LESS messages: a zero-width write's
    [WeakInterp.wwrite_msg] carries an empty [wm_data], so [msg_byte] is
    [None] everywhere.  Such an append changes no byte's latest write, which
    is exactly what the state interpretation's [wlat_interp] conjunct needs;
    and every effect only raises views.  [wQ_quiet] packages the two, and it
    is the certificate-level [Q] of an instruction with no memory effect of
    its own — a branch, a jump, an ALU operation. *)

Definition qmsg (m : wmsg) : Prop := forall a, msg_byte m a = None.
Definition qmsgs (l : list wmsg) : Prop := Forall qmsg l.

Lemma wwrite_msg_qmsg tid k (pa : Arch.pa) (n : N) {w : N} (v : bv w) :
  (n = 0)%N -> qmsg (wwrite_msg tid k pa n v).
Proof.
  intros -> a. rewrite /msg_byte /wwrite_msg /=.
  by destruct (bool_decide (pa_z pa ≤ a)).
Qed.

Lemma weff_apply_quiet_log tid s e :
  weff_quiet e ->
  exists l, wm_log (weff_apply tid s e) = (wm_log s ++ l)%list /\ qmsgs l.
Proof.
  destruct e as [ak pa n|ak pa n v|b]; intros Hq.
  - exists []. rewrite weff_apply_read wread_post_log app_nil_r.
    split; [reflexivity|constructor].
  - eexists [wwrite_msg tid _ pa n v].
    rewrite weff_apply_write /wwrite_post /=.
    split; [reflexivity|]. constructor; [|constructor].
    exact (wwrite_msg_qmsg tid _ pa n v Hq).
  - exists []. rewrite weff_apply_bar app_nil_r. split; [reflexivity|constructor].
Qed.

Lemma weffs_quiet_log tid s es :
  quiet_trace es ->
  exists l, wm_log (weffs tid s es) = (wm_log s ++ l)%list /\ qmsgs l.
Proof.
  revert s. induction es as [|e es IH]; intros s Hq.
  - exists []. rewrite weffs_nil app_nil_r. split; [reflexivity|constructor].
  - destruct (quiet_trace_cons_inv _ _ Hq) as [He Hes].
    destruct (weff_apply_quiet_log tid s e He) as (l1 & Hl1 & Hq1).
    destruct (IH (weff_apply tid s e) Hes) as (l2 & Hl2 & Hq2).
    exists (l1 ++ l2)%list. rewrite weffs_cons Hl2 Hl1 -app_assoc.
    split; [reflexivity|]. by apply Forall_app.
Qed.

(** The certificate-level [Q] of a memory-effect-free instruction. *)
Definition wQ_quiet : wmstate -> wmstate -> Prop :=
  fun s s' =>
    wm_img s' = wm_img s /\
    (exists l, wm_log s' = (wm_log s ++ l)%list /\ qmsgs l) /\
    ws_le (wm_ws s) (wm_ws s').

Lemma wcert_quiet (cid : nat) (pc : SailStdpp.Values.mword 64) (es : list weff) :
  quiet_trace es -> wstep_cert cid pc (wP_eff (Some cid) es) wQ_quiet.
Proof.
  intros Hq. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  rewrite /wQ_quiet. split_and!.
  - exact Hi.
  - destruct (weffs_quiet_log (Some cid) s es Hq) as (l & Hl' & Hql).
    exists l. rewrite Hl Hl'. split; [reflexivity|exact Hql].
  - rewrite Hws. apply weffs_ws_le.
Qed.

(** A quiet append preserves the latest-write authority: no element's byte was
    written, so [WeakGhost.wlat_agree_app]'s side condition is immediate.  This
    is the whole "give the state interpretation back" obligation of a leaf
    whose instruction has no memory effect. *)
Section quiet_interp.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma qmsgs_not_writes_in (log l : list wmsg) (a : Z) :
    qmsgs l ->
    ¬ writes_in (log ++ l) a (length log) (length (log ++ l)).
  Proof.
    intros Hq (t & Hlo & Hhi & m & Hm & [b Hb]).
    assert (Hge : (length log ≤ t - 1)%nat) by lia.
    rewrite lookup_app_r in Hm; [|exact Hge].
    apply (Forall_lookup_1 _ _ _ _ Hq) in Hm.
    by rewrite Hm in Hb.
  Qed.

  Lemma wlat_interp_quiet_app (img : gmap Arch.pa (bv 8)) (log l : list wmsg) :
    qmsgs l ->
    (wlat_interp img log : iProp Σ) -∗ wlat_interp img ((log ++ l)%list).
  Proof.
    iIntros (Hq) "Hi". iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    iExists m, mc. iFrame "Hauth Hc". iSplitR.
    - iPureIntro. apply (wlat_agree_app _ _ _ _ Hag).
      intros a _. exact (qmsgs_not_writes_in log l a Hq).
    - iPureIntro. apply wcds_agree_app; [|exact Hagc].
      intros a _ mg Hmg. by apply (proj1 (Forall_forall _ _) Hq mg Hmg).
  Qed.

  (** …and at the shape a leaf meets it: [wQ_quiet] says the successor's log
      is such an append. *)
  Lemma wlat_interp_wQ_quiet (s s' : wmstate) :
    wQ_quiet s s' ->
    (wlat_interp (wm_img s) (wm_log s) : iProp Σ) -∗
    wlat_interp (wm_img s') (wm_log s').
  Proof.
    iIntros ((Hi & (l & Hl & Hql) & _)) "H". rewrite Hi Hl.
    by iApply wlat_interp_quiet_app.
  Qed.

End quiet_interp.

(* ====================================================================== *)
(** ** 6. THE CERTIFICATES, GENERALISED OVER WRITE-FREE SURROUNDINGS

    [WeakCert]'s four certificates pin the trace to a 2- or 3-element list
    whose FIRST element is the fetch read.  Nothing in their arithmetic needs
    that: a read or a barrier only ever RAISES views and leaves the log alone,
    and all four [wQ_*] are monotone in exactly that direction.  So the same
    certificates hold with the instruction's own access surrounded by ARBITRARY
    WRITE-FREE traces — which is what lets the fetch (and any translation or
    check the model performs on the way) be discharged wholesale instead of
    element by element. *)

Definition weff_nowrite (e : weff) : Prop :=
  match e with WEwrite _ _ _ _ => False | _ => True end.

Definition nowrite_trace (es : list weff) : Prop := Forall weff_nowrite es.

Lemma nowrite_trace_cons_inv e es :
  nowrite_trace (e :: es) -> weff_nowrite e /\ nowrite_trace es.
Proof. intros H. by apply Forall_cons_1 in H. Qed.

Lemma weff_apply_nowrite_log tid s e :
  weff_nowrite e -> wm_log (weff_apply tid s e) = wm_log s.
Proof.
  destruct e as [ak pa n|ak pa n v|b]; intros He.
  - apply wread_post_log.
  - destruct He.
  - reflexivity.
Qed.

Lemma weffs_nowrite_log tid s es :
  nowrite_trace es -> wm_log (weffs tid s es) = wm_log s.
Proof.
  revert s. induction es as [|e es IH]; intros s He; [reflexivity|].
  destruct (nowrite_trace_cons_inv _ _ He) as [He1 He2].
  rewrite weffs_cons (IH _ He2). exact (weff_apply_nowrite_log tid s e He1).
Qed.

(** [w_relp] is MONOTONE along a write-free suffix: only a store clears the
    release-pending flag, and a read leaves it alone while a [pw ∧ sw] fence
    can only set it.  This is what lets [wcert_fence_gen] certify the release
    fence's arming through a write-free tail (φ-upgrade §1). *)
Lemma weff_apply_nowrite_relp tid s e :
  weff_nowrite e -> w_relp (wm_ws s) = true ->
  w_relp (wm_ws (weff_apply tid s e)) = true.
Proof.
  destruct e as [ak pa n|ak pa n v|b]; intros He Hr.
  - rewrite weff_apply_read. by rewrite wread_post_relp.
  - destruct He.
  - rewrite weff_apply_bar wm_ws_wset_ws /barrier_post.
    destruct b; simpl; rewrite ?Hr; reflexivity.
Qed.

Lemma weffs_nowrite_relp tid s es :
  nowrite_trace es -> w_relp (wm_ws s) = true ->
  w_relp (wm_ws (weffs tid s es)) = true.
Proof.
  revert s. induction es as [|e es IH]; intros s He Hr; [exact Hr|].
  destruct (nowrite_trace_cons_inv _ _ He) as [He1 He2].
  rewrite weffs_cons. apply IH; [exact He2|].
  by apply weff_apply_nowrite_relp.
Qed.

(** The view side: a write-free suffix cannot lose a floor already reached. *)
Lemma flr_ws_le (ws ws' : wstate) (a : Z) :
  ws_le ws ws' -> (flr (ws_view ws) a ≤ flr (ws_view ws') a)%nat.
Proof. intros Hle. by apply (view_sqsubseteq_spec _ _), ws_view_mono. Qed.

Lemma weffs_flr_mono tid s es (a : Z) :
  (flr (ws_view (wm_ws s)) a ≤ flr (ws_view (wm_ws (weffs tid s es))) a)%nat.
Proof. apply flr_ws_le, weffs_ws_le. Qed.

Lemma weffs_view_mono tid s es (V : view) :
  V ⊑ ws_view (wm_ws s) -> V ⊑ ws_view (wm_ws (weffs tid s es)).
Proof. intros HV. etrans; [exact HV|]. apply ws_view_mono, weffs_ws_le. Qed.

(** *** 6a. A memory-effect-free instruction (branch / jump / ALU)

    The strict form: no write of ANY width, so the log is unchanged on the
    nose (compare [wQ_quiet], which tolerates the zero-width residue the
    empty-memory detector cannot see). *)

Definition wQ_pure : wmstate -> wmstate -> Prop :=
  fun s s' =>
    wm_img s' = wm_img s /\ wm_log s' = wm_log s /\ ws_le (wm_ws s) (wm_ws s').

Lemma wQ_pure_quiet s s' : wQ_pure s s' -> wQ_quiet s s'.
Proof.
  intros (Hi & Hl & Hws). split_and!; [exact Hi| |exact Hws].
  exists []. rewrite app_nil_r. split; [exact Hl|constructor].
Qed.

Lemma wcert_nowrite (cid : nat) (pc : SailStdpp.Values.mword 64) (es : list weff) :
  nowrite_trace es -> wstep_cert cid pc (wP_eff (Some cid) es) wQ_pure.
Proof.
  intros Hnw. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  rewrite /wQ_pure. split_and!.
  - exact Hi.
  - rewrite Hl. exact (weffs_nowrite_log (Some cid) s es Hnw).
  - rewrite Hws. apply weffs_ws_le.
Qed.

Lemma weffs_app tid s es1 es2 :
  weffs tid s (es1 ++ es2)%list = weffs tid (weffs tid s es1) es2.
Proof. rewrite /weffs foldl_app //. Qed.

(** *** 6b. [fence] with write-free surroundings *)

Lemma wcert_fence_gen (cid : nat) (pc : SailStdpp.Values.mword 64)
    (pre post : list weff) (b : barrier_kind) :
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff (Some cid) (pre ++ WEbar b :: post)) (wQ_fence b).
Proof.
  intros Hpre Hpost. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  rewrite /wQ_fence /wV_fence Hws weffs_app weffs_cons weff_apply_bar.
  split.
  - etrans; [apply barrier_post_mono, weffs_ws_le|].
    etrans; [|apply (weffs_ws_le (Some cid) _ post)].
    rewrite wm_ws_wset_ws. reflexivity.
  - intros Ha. apply weffs_nowrite_relp; [exact Hpost|].
    rewrite wm_ws_wset_ws. by apply barrier_post_relp.
Qed.

(** *** 6c. The 4-byte STORE with write-free surroundings *)

Lemma wcert_store_gen (cid : nat) (pc : SailStdpp.Values.mword 64)
    (pre post : list weff) (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff (Some cid) (pre ++ WEwrite akw ea 4 v :: post))
    (wQ_store (Some cid) ea v).
Proof.
  intros Hpre Hpost. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  set (s1 := weffs (Some cid) s pre).
  assert (Hl1 : wm_log s1 = wm_log s)
    by exact (weffs_nowrite_log (Some cid) s pre Hpre).
  set (s2 := weff_apply (Some cid) s1 (WEwrite akw ea 4 v)).
  assert (Hl2 : wm_log s2
                = (wm_log s ++ [wwrite_msg (Some cid)
                     (wm_class_of akw (wm_ws s1)) ea 4 v])%list).
  { subst s2. rewrite weff_apply_write /wwrite_post /= Hl1. reflexivity. }
  assert (Hlpost : wm_log (weffs (Some cid) s2 post) = wm_log s2)
    by exact (weffs_nowrite_log (Some cid) s2 post Hpost).
  assert (Hls' : wm_log s'
                 = (wm_log s ++ [wwrite_msg (Some cid)
                      (wm_class_of akw (wm_ws s1)) ea 4 v])%list).
  { rewrite Hl weffs_app weffs_cons -/s1 -/s2 Hlpost Hl2. reflexivity. }
  rewrite /wQ_store /wV_store.
  split_and!; [exact Hi| |exact Hle|].
  { eexists. split; [exact Hls'|]. intros Hr. apply wm_class_of_relp.
    subst s1. by apply weffs_nowrite_relp. }
  intros j Hj.
  (* the floor reached at the store's own step survives the write-free tail *)
  assert (Hstep : (S (length (wm_log s))
                   ≤ flr (ws_view (wm_ws s2)) (acc_addr ea j))%nat).
  { subst s2. rewrite weff_apply_write wwrite_post_ws Hl1 flr_ws_view /acc_addr.
    etrans; [|apply Nat.le_max_r].
    exact (store_post_run_coh (wm_ws s1) (ak_sync akw) (pa_z ea) (N.to_nat 4)
             (S (length (wm_log s))) j Hj). }
  etrans; [exact Hstep|].
  rewrite Hws weffs_app weffs_cons -/s1 -/s2.
  apply flr_ws_le, weffs_ws_le.
Qed.

(** *** 6d. The 4-byte plain LOAD with write-free surroundings *)

Lemma wcert_load_gen (cid : nat) (pc : SailStdpp.Values.mword 64)
    (pre post : list weff) (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff (Some cid) (pre ++ WEread akl ea 4 :: post)) (wQ_load ea).
Proof.
  intros Hcoh Hpre Hpost. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  set (s1 := weffs (Some cid) s pre).
  assert (Hl1 : wm_log s1 = wm_log s)
    by exact (weffs_nowrite_log (Some cid) s pre Hpre).
  set (s2 := weff_apply (Some cid) s1 (WEread akl ea 4)).
  assert (Hl2 : wm_log s2 = wm_log s)
    by (subst s2; rewrite weff_apply_read wread_post_log; exact Hl1).
  assert (Hlpost : wm_log (weffs (Some cid) s2 post) = wm_log s2)
    by exact (weffs_nowrite_log (Some cid) s2 post Hpost).
  assert (Hls' : wm_log s' = wm_log s).
  { rewrite Hl weffs_app weffs_cons -/s1 -/s2 Hlpost Hl2. reflexivity. }
  rewrite /wQ_load /wV_load. split_and!; [exact Hi|exact Hls'|].
  intros j Hj.
  assert (Hcts : coh_ts s1 ea 4 = coh_ts s ea 4)
    by exact (coh_ts_log s1 s ea 4 Hl1).
  assert (Hgain : view_byte (acc_addr ea j) (latest_ts (wm_log s) (acc_addr ea j))
                  ⊑ ws_view (wm_ws s2)).
  { subst s2. rewrite weff_apply_read Hcts
      (wread_post_ws_weak s1 akl ea (coh_ts s ea 4) Hcoh) /acc_addr.
    rewrite -(coh_ts_lookup s ea 4 j Hj).
    apply (load_post_run_gain (fun a t => view_byte a t) (wm_ws s1)
             (ak_sync akl) (pa_z ea) (coh_ts s ea 4) j).
    - intros w a t. apply load_byte_gain.
    - rewrite coh_ts_length. exact Hj. }
  etrans; [exact Hgain|].
  rewrite Hws weffs_app weffs_cons -/s1 -/s2.
  apply ws_view_mono, weffs_ws_le.
Qed.

(** *** 6e. [amoswap.w.aq] with write-free surroundings

    The read half and the write half of an AMO are adjacent in the trace (the
    model emits them back to back), so only the OUTER surroundings are
    generalised here. *)

Lemma wcert_amo_aq_gen (cid : nat) (pc : SailStdpp.Values.mword 64)
    (pre post : list weff) (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true -> ak_latest akw = true ->
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff (Some cid) (pre ++ WEread aka ea 4 :: WEwrite akw ea 4 v :: post))
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync Hlat Hpre Hpost. apply wstep_cert_eff.
  intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  set (s1 := weffs (Some cid) s pre).
  assert (Hl1 : wm_log s1 = wm_log s)
    by exact (weffs_nowrite_log (Some cid) s pre Hpre).
  assert (Hcts : coh_ts s1 ea 4 = coh_ts s ea 4)
    by exact (coh_ts_log s1 s ea 4 Hl1).
  set (s2 := weff_apply (Some cid) s1 (WEread aka ea 4)).
  assert (Hl2 : wm_log s2 = wm_log s)
    by (subst s2; rewrite weff_apply_read wread_post_log; exact Hl1).
  assert (Hws2 : wm_ws s2
                 = load_post_run (wm_ws s1) true (pa_z ea) (coh_ts s ea 4)).
  { subst s2. rewrite weff_apply_read Hcts
      (wread_post_ws_weak s1 aka ea (coh_ts s ea 4) Hcoh) Hsync. reflexivity. }
  set (s3 := weff_apply (Some cid) s2 (WEwrite akw ea 4 v)).
  assert (Hl3 : wm_log s3
                = (wm_log s ++ [wwrite_msg (Some cid)
                     (wm_class_of akw (wm_ws s2)) ea 4 v])%list).
  { subst s3. rewrite weff_apply_write /wwrite_post /= Hl2. reflexivity. }
  assert (Hlpost : wm_log (weffs (Some cid) s3 post) = wm_log s3)
    by exact (weffs_nowrite_log (Some cid) s3 post Hpost).
  assert (Hsplit : wm_log s' = wm_log (weffs (Some cid) s3 post) /\
                   wm_ws s' = wm_ws (weffs (Some cid) s3 post)).
  { rewrite Hl Hws !weffs_app !weffs_cons -/s1 -/s2 -/s3. by split. }
  destruct Hsplit as [Hls' Hwss'].
  assert (Hexcl : wm_class_of akw (wm_ws s2) = WCexcl)
    by (unfold wm_class_of; by rewrite Hlat).
  rewrite /wQ_amo_aq. split_and!;
    [| |by rewrite Hls' Hlpost Hl3 Hexcl].
  - rewrite /wQ_store /wV_store. split_and!.
    + exact Hi.
    + eexists. split; [rewrite Hls' Hlpost Hl3; reflexivity|].
      intros Hr. rewrite Hexcl. discriminate.
    + exact Hle.
    + intros j Hj.
      assert (Hstep : (S (length (wm_log s))
                       ≤ flr (ws_view (wm_ws s3)) (acc_addr ea j))%nat).
      { subst s3. rewrite weff_apply_write wwrite_post_ws Hl2 flr_ws_view /acc_addr.
        etrans; [|apply Nat.le_max_r].
        exact (store_post_run_coh (wm_ws s2) (ak_sync akw) (pa_z ea) (N.to_nat 4)
                 (S (length (wm_log s))) j Hj). }
      etrans; [exact Hstep|]. rewrite Hwss'. apply flr_ws_le, weffs_ws_le.
  - rewrite /wV_amo_aq. intros j Hj.
    assert (Hgain : view_scl (latest_ts (wm_log s) (acc_addr ea j))
                    ⊑ ws_view (wm_ws s2)).
    { rewrite Hws2 -(coh_ts_lookup s ea 4 j Hj).
      apply (load_post_run_gain (fun _ t => view_scl t) (wm_ws s1)
               true (pa_z ea) (coh_ts s ea 4) j).
      - intros w a t. apply amo_acq_gain.
      - rewrite coh_ts_length. exact Hj. }
    etrans; [exact Hgain|].
    rewrite Hwss'.
    etrans; [|apply ws_view_mono, (weffs_ws_le (Some cid) s3 post)].
    apply ws_view_mono. subst s3. apply weff_apply_ws_le.
Qed.

(* ====================================================================== *)
(** ** 7. A MEASURED MIRROR: the [try_step] wrapper at [exec_eff]

    The claim §2 makes — that an existing SC proof script replays at
    [exec_eff] by renaming its bind lemmas — is worth one measurement rather
    than an assertion, and this is it: [RiscvExec.exec_riscv_step_hart_active]
    (the whole [try_step] wrapper: the privilege read, [should_inc_minstret],
    the [minstret_increment] write, the hart-active gate, the PC tick and the
    conditional [minstret] bump) mirrored line for line.  Every step of the
    wrapper is register-only, so the WHOLE trace is [run_hart_active]'s, and
    the script differs from the original only in the lemma names and the one
    [app_nil_r].

    This is the outermost layer of the M4 shared skeleton.  What remains
    below it is [run_hart_active] (an [execR]-level mirror), the fetch, and
    the one memory-touching [execute] per instruction shape; the decoder and
    every register-only [execute] are §4's, i.e. free. *)

Lemma exec_eff_bind_Some {X Y} (m : M X) (f : X -> M Y) s v st es :
  exec_eff m s = Some (v, st, es) ->
  exec_eff (Defs.bind m f) s
  = match exec_eff (f v) st with
    | Some (y, s', es') => Some (y, s', (es ++ es')%list)
    | None => None
    end.
Proof.
  intros Hm. destruct (exec_eff (f v) st) as [[[y s'] es']|] eqn:Hf.
  - exact (exec_eff_bind m f s v st es y s' es' Hm Hf).
  - destruct (exec_eff (Defs.bind m f) s) as [[[y s'] es']|] eqn:Hb;
      [|reflexivity].
    exfalso.
    pose proof (exec_eff_exec _ _ _ _ _ Hb) as Hbe.
    pose proof (exec_eff_exec _ _ _ _ _ Hm) as Hme.
    rewrite exec_bind Hme in Hbe.
    destruct (exec_exec_eff _ _ _ _ Hbe) as [es0 Hee]. by rewrite Hee in Hf.
Qed.

Lemma exec_eff_tick_pc s :
  exec_eff (tick_pc tt) s
  = Some (tt, set_reg s PC (register_lookup nextPC s.(sregs)), []).
Proof.
  unfold tick_pc.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg nextPC s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg PC _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg PC _)).
  reflexivity.
Qed.

Section StepHartActiveEff.
  Context (s s_exec : mstate) (retval : SailStdpp.Values.mword 32) (b : bool)
          (es : list weff).

  Hypothesis Hsi :
    exec_eff (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s, []).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec_eff (run_hart_active 0) s_a
      = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec, es).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.

  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_eff_riscv_step_hart_active :
    exec_eff (riscv_step false) s = Some (tt, s_final, es).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _
              (_ : exec_eff (try_step 0 false) s = Some (false, s_final, es))).
    { cbn beta iota. rewrite exec_eff_returnm. cbn match.
      by rewrite app_nil_r. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    cbn beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_eff_bind0_nil _ _ _ _ _
               (exec_eff_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hha). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    erewrite exec_eff_bind_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind_nil.
            2:{ apply exec_eff_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        apply exec_eff_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    erewrite exec_eff_bind0_nil.
    2:{ apply exec_eff_tick_pc. }
    erewrite exec_eff_bind_nil.
    2:{ unfold Defs.and_boolM.
        erewrite exec_eff_bind_nil.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_eff_read_reg minstret_increment). }
    change (get_config_rvfi tt) with false.
    replace (register_lookup minstret_increment
               (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs))
      with b.
    2:{ rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - erewrite exec_eff_bind0_nil.
      2:{ erewrite exec_eff_bind0_nil.
          2:{ erewrite exec_eff_bind_nil.
              2:{ apply (exec_eff_read_reg minstret). }
              apply exec_eff_write_reg. }
          cbn beta iota. reflexivity. }
      cbn beta iota. rewrite exec_eff_returnm. cbn match.
      by rewrite app_nil_r.
    - erewrite exec_eff_bind0_nil.
      2:{ erewrite exec_eff_bind0_nil.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      cbn beta iota. rewrite exec_eff_returnm. cbn match.
      by rewrite app_nil_r.
  Qed.

End StepHartActiveEff.
