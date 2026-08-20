(** * WeakMem.v — the promise-free view machine (M0 model spike)

    This is the M0 spike of the RVWMO model described in
    [claude-notes/design/weak-memory.md]: the Promising-RISC-V machine shape
    with the promise machinery deliberately omitted (every store appends at the
    end of the global log), and with syntactic dependency tracking (ppo 9–13)
    dropped.

    DELIBERATELY DEPENDENCY-FREE.  This file imports only stdpp: no Iris, no
    Sail.  The machine types are abstracted for the spike —

      - addresses are [Z]       (the real machine instantiates at [Arch.pa]),
      - bytes are [bv 8]        (as in the tree today),
      - agents are [nat]        (the real machine instantiates at [CPU]).

    Nothing below inspects an agent identifier, and addresses are used only as
    [gmap] keys and under [Z.le]/[Z.sub], so the instantiation at [Arch.pa]
    needs exactly: [EqDecision], [Countable], and a [pa_add]-flavoured
    "byte i of a message" arithmetic (see [msg_byte]).  Beware the
    [gmap Arch.pa _] Countable trap recorded in the durable notes: a file that
    also imports [SailStdpp.Values] elaborates the key type's [Countable]
    instance differently, so the eventual instantiation must NOT write
    [gmap Arch.pa (bv 8)] as an explicit binder type in a Sail-importing file.
*)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.

Local Open Scope Z_scope.

(** Agents (harts, DMA engines).  Abstract in the spike. *)
Notation agent := nat.

(** REGISTERS.  Abstract exactly as [agent] is: nothing below inspects a
    register name, it is only a [gmap] key ([w_regv]), so the event
    language may instantiate it at whatever names its [RegWrite] nodes
    carry (D2, deps design §2.1).  Only GPRs ever acquire a nonzero view,
    by construction of the label vocabulary (deviation D-4).

    ONLY PARSING, so that [nat] keeps printing as [agent] (the pre-existing
    notation) rather than flipping to [wreg] in every goal.

    IT IS SPELLED [wreg], NOT [register]: [Riscv.rv64d_types] exports its own
    [register] type, and a [Notation register := nat] here would shadow it in
    every Sail-importing consumer ([WeakInterp]'s [register_lookup] was the
    first casualty). *)
Notation wreg := nat (only parsing).

(** THE DEPENDENCY SOURCE VOCABULARY (deps design §2.2).  A label names its
    dependency SOURCES; the MACHINE looks the views up.  [pstep] therefore
    stays VIEW-BLIND: it emits names, never timestamps, which is what keeps
    [ts_oblivious]/[pcls_obl]/[lat_free_prog]/[pdev_ok] unaffected in shape.

      [DReg r] — a general-purpose register (PARM's [rmap] entry);
      [DLdRes]  — THIS INSTRUCTION'S LOAD RESULT (PARM's [res] of
                  [step_load], banked in [w_ldv] and reset by [LInstr]). *)
Inductive dsrc := DReg (r : wreg) | DLdRes.

Global Instance dsrc_eq_dec : EqDecision dsrc.
Proof. solve_decision. Defined.

(** The era-initial image is a PARTIAL FUNCTION on [Z], not a [gmap Z _].
    M1's interpreter ([WeakInterp.v]) keeps the image in the tree's own
    [gmap Arch.pa (bv 8)] form and converts at the seam ([WeakInterp.img_z]),
    so a [gmap Z _] here would force a key-space [kmap] — and with it exactly
    the [gmap Arch.pa _] Countable trap the header warns about.  A function
    parameter costs nothing (the litmus image is still built as a [gmap] and
    read through one lambda) and makes the seam a definition, not a theorem. *)
Definition image : Type := Z → option (bv 8).

(* ------------------------------------------------------------------ *)
(** ** Messages and the global write log *)

(** THE MESSAGE CLASS (M6 D-M6-6).  An INERT syntactic tag recording how the
    write was issued, so that Layer 2's classification is a FUNCTION of the
    machine state rather than a ghost existential (see
    [claude-notes/projects/weak-memory-m6.md], W3).  No rule of any machine in
    this tree inspects it — it exists only for the M6 statements, exactly like
    [wm_tid].

      - [WCexcl]  — the write half of an exclusive/[ak_latest] access
                    (the walker's CAS, an AMO): SCexcl.
      - [WCrel]   — a release-class publication: the store is an [.rl] store,
                    or it is the first store after a [pw ∧ sw] fence
                    ([w_relp], the RISC-V [fence rw,w; sd flag] idiom): SCfenced.
      - [WCplain] — everything else, i.e. the [↦w{1}]-owned stores: SCowned. *)
Inductive wm_class := WCplain | WCrel | WCexcl.

Global Instance wm_class_eq_dec : EqDecision wm_class.
Proof. solve_decision. Defined.

(** One write event.  It covers the byte range [wm_pa, wm_pa + |wm_data|).
    [wm_tid] names the AGENT that appended the message; every agent of the
    composed machine — harts AND the disk — has an index, so [None] is now
    only the never-used boot-era slot (the DMA-tid unification, seam 1a of
    [claude-notes/completed/weak-memory-lift.md]: [WeakLang.wmsgs_of_map]
    stamps [Some WeakLang.n_disk], matching the disk's index in
    [WeakCompose.xv6_ps]).  Predicates that used to exempt [wm_tid = None]
    are re-keyed on IS-A-HART ([tid_hart] below).  [wm_ak] is the inert class
    field above; it is LAST so that positional literals that predate it fail
    loudly rather than silently permuting. *)
Record wmsg := WMsg {
  wm_pa   : Z;
  wm_data : list (bv 8);
  wm_tid  : option agent;
  wm_ak   : wm_class;
}.
Add Printing Constructor wmsg.

Global Instance wmsg_eq_dec : EqDecision wmsg.
Proof. solve_decision. Defined.

(** The byte message [m] writes at address [a] (None if [a] is outside its
    range). *)
Definition msg_byte (m : wmsg) (a : Z) : option (bv 8) :=
  if bool_decide (wm_pa m ≤ a)
  then wm_data m !! Z.to_nat (a - wm_pa m)
  else None.

(* ------------------------------------------------------------------ *)
(** ** The two tid-space notions both towers share

    [tid_hart nh t] — "[t] is one of the first [nh] agents", i.e. A HART.
    The DMA-tid unification (seam 1a) gives the disk an ordinary agent index
    ([nh] itself), so "is a hart" — not "[wm_tid = None]" — is what every
    ownership/publication invariant is keyed on.  The bound is a PARAMETER
    here because [WeakMem] is deliberately stdpp-only and knows no [NCPU];
    [WeakLang.tid_is_hart] and [WeakCompose] fix it at [RiscvLang.NCPU]. *)
Definition tid_hart (nh : nat) (t : option agent) : Prop :=
  ∃ i : agent, t = Some i ∧ (i < nh)%nat.

Lemma tid_hart_ne_disk nh t : tid_hart nh t → t ≠ Some nh.
Proof. intros (i & -> & Hlt) [= ->]. lia. Qed.

Lemma tid_hart_none nh : ¬ tid_hart nh None.
Proof. by intros (i & ? & _). Qed.

(** *** PUBLICATION, PURELY OVER THE LOG (φ-upgrade §1b, delta 1).

    [wpublished log tid p] — "position [p] has been published by agent
    [tid]": a LATER message of the SAME agent is release-class.  Since
    [WeakMem.store_post] raises the storing agent's [w_pub] to the store's
    own timestamp whenever the store is release-class, and [w_pub] only ever
    grows, this IMPLIES the watermark reading — and it is a predicate of the
    LOG ALONE, which is what lets the Iris-side C/D/S invariant keep
    [wlat_interp]'s arity AND what lets Layer 1 ([WeakRobustMain.pub_of])
    spell publication without reaching into the agent vector.

    IT LIVES HERE, not in [WeakGhost] or [WeakRobustMain], because BOTH
    towers must mean the same thing by it: the φ export produces
    [WeakGhost.no_violation] (stated with this predicate) and Layer 1
    consumes [WeakRobust.violation cls_of pub_of] (also stated with it), and
    the lift's whole job is to identify the two. *)
Definition wpublished (log : list wmsg) (tid : option agent) (p : nat) : Prop :=
  ∃ (q : nat) (mq : wmsg),
    (p ≤ q)%nat ∧ log !! q = Some mq ∧ wm_tid mq = tid ∧ wm_ak mq = WCrel.

Lemma wpublished_app log ms tid p :
  wpublished log tid p → wpublished (log ++ ms) tid p.
Proof.
  intros (q & mq & Hle & Hq & Ht & Hk). exists q, mq. split_and!; try done.
  rewrite lookup_app_l //. by eapply lookup_lt_Some.
Qed.

(** Memory is an era-initial image plus an append-only log.  Timestamp 0 is the
    image; timestamp [i+1] is log entry [i].  [log_byte img log t a] is the
    value timestamp [t] writes at byte [a], or None if [t] does not write [a].

    One shared total order over all writes is exactly what multi-copy atomicity
    licenses (design doc, Decision 1). *)
Definition log_byte (img : image) (log : list wmsg) (t : nat) (a : Z)
    : option (bv 8) :=
  match t with
  | O => img a
  | S i => m ← log !! i; msg_byte m a
  end.

Lemma log_byte_0 img log a : log_byte img log 0 a = img a.
Proof. done. Qed.

Lemma log_byte_S img log i a :
  log_byte img log (S i) a = (log !! i) ≫= (λ m, msg_byte m a).
Proof. done. Qed.

(** A timestamp that writes anything is within the log. *)
Lemma log_byte_bounded img log t a :
  is_Some (log_byte img log t a) → (t ≤ length log)%nat.
Proof.
  destruct t as [|i]; [lia|]. rewrite log_byte_S.
  intros [v Hv]. destruct (log !! i) as [m|] eqn:Hm; simplify_eq/=.
  apply lookup_lt_Some in Hm. lia.
Qed.

(** The log is append-only, so old timestamps keep their values. *)
Lemma log_byte_app img log l t a :
  (t ≤ length log)%nat → log_byte img (log ++ l) t a = log_byte img log t a.
Proof.
  destruct t as [|i]; [done|]. intros ?.
  rewrite !log_byte_S lookup_app_l //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [writes_in]: some timestamp in a half-open view window writes a byte *)

(** [writes_in log a lo hi] — some timestamp [t] with [lo < t ≤ hi] writes
    byte [a].  Since [t > lo ≥ 0], the image is never consulted, which is why
    this does not mention [img]. *)
Definition writes_in (log : list wmsg) (a : Z) (lo hi : nat) : Prop :=
  ∃ t : nat, (lo < t)%nat ∧ (t ≤ hi)%nat ∧
             ∃ m, log !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a).

(** The bridge to [log_byte] at any image. *)
Lemma writes_in_log_byte img log a lo hi :
  writes_in log a lo hi ↔
  ∃ t : nat, (lo < t)%nat ∧ (t ≤ hi)%nat ∧ is_Some (log_byte img log t a).
Proof.
  split.
  - intros (t & Hlo & Hhi & m & Hm & [v Hv]).
    exists t. split_and!; [done|done|].
    destruct t as [|i]; [lia|]. rewrite log_byte_S.
    replace (S i - 1)%nat with i in Hm by lia. rewrite Hm /=. exists v. exact Hv.
  - intros (t & Hlo & Hhi & Hs).
    exists t. split_and!; [done|done|].
    destruct t as [|i]; [lia|]. rewrite log_byte_S in Hs.
    destruct (log !! i) as [m|] eqn:Hm; simpl in Hs; [|by destruct Hs].
    exists m. replace (S i - 1)%nat with i by lia. by split.
Qed.

Lemma writes_in_mono log a lo hi lo' hi' :
  (lo' ≤ lo)%nat → (hi ≤ hi')%nat → writes_in log a lo hi → writes_in log a lo' hi'.
Proof. intros ?? (t & ? & ? & ?). exists t. split_and!; [lia|lia|done]. Qed.

Lemma writes_in_mono_hi log a lo hi hi' :
  (hi ≤ hi')%nat → writes_in log a lo hi → writes_in log a lo hi'.
Proof. intros. by eapply writes_in_mono. Qed.

Lemma writes_in_app log l a lo hi :
  writes_in log a lo hi → writes_in (log ++ l) a lo hi.
Proof.
  intros (t & ? & ? & m & Hm & ?). exists t. split_and!; [done|done|].
  exists m. rewrite lookup_app_l //. apply lookup_lt_Some in Hm. lia.
Qed.

(** A write in a window that predates the extension was already there. *)
Lemma writes_in_app_inv log l a lo hi :
  (hi ≤ length log)%nat → writes_in (log ++ l) a lo hi → writes_in log a lo hi.
Proof.
  intros Hle (t & ? & ? & m & Hm & ?). exists t. split_and!; [done|done|].
  assert ((log ++ l) !! (t - 1)%nat = log !! (t - 1)%nat) as Heq.
  { apply lookup_app_l. lia. }
  exists m. rewrite -Heq. by split.
Qed.

(** Any witness is inside the log, so the window may be clipped to it. *)
Lemma writes_in_clip log a lo hi :
  writes_in log a lo hi → writes_in log a lo (Nat.min hi (length log)).
Proof.
  intros (t & ? & ? & m & Hm & ?).
  pose proof (lookup_lt_Some _ _ _ Hm) as Hlt.
  exists t. split_and!; [done|lia|]. exists m. by split.
Qed.

Lemma not_writes_in_clip log a lo hi :
  ¬ writes_in log a lo (Nat.min hi (length log)) → ¬ writes_in log a lo hi.
Proof. intros Hn Hw. apply Hn, writes_in_clip, Hw. Qed.

(* ------------------------------------------------------------------ *)
(** ** Deciding [writes_in] by reflection

    Every concrete side condition of the model — a litmus verdict, and every
    admissibility check the functional interpreter [WeakInterp.wexec] performs
    — is "no message in this window writes this byte" over a concrete log.
    Reflect it once, here, so both consumers share the decision procedure. *)

Definition msg_writesb (m : wmsg) (a : Z) : bool :=
  match msg_byte m a with Some _ => true | None => false end.

Lemma msg_writesb_true m a : msg_writesb m a = true ↔ is_Some (msg_byte m a).
Proof.
  rewrite /msg_writesb. destruct (msg_byte m a) as [v|].
  - split; [intros _; by eexists|done].
  - split; [done|by intros [? ?]].
Qed.

Lemma msg_writesb_false m a : msg_writesb m a = false ↔ msg_byte m a = None.
Proof. rewrite /msg_writesb. by destruct (msg_byte m a). Qed.

Definition writes_inb (log : list wmsg) (a : Z) (lo hi : nat) : bool :=
  existsb (λ t, bool_decide (lo < t)%nat && bool_decide (t ≤ hi)%nat &&
                match log !! (t - 1)%nat with
                | Some m => msg_writesb m a
                | None => false
                end)
          (seq 1 (length log)).

Lemma writes_inb_spec log a lo hi :
  writes_in log a lo hi ↔ writes_inb log a lo hi = true.
Proof.
  rewrite /writes_inb existsb_exists. split.
  - intros (t & Hlo & Hhi & m & Hm & Hs).
    pose proof (lookup_lt_Some _ _ _ Hm) as Hlt.
    exists t. split.
    + apply elem_of_list_In, elem_of_seq. lia.
    + rewrite Hm /msg_writesb. destruct Hs as [v Hv]. rewrite Hv /=.
      rewrite andb_true_r andb_true_iff.
      split; by apply bool_decide_eq_true_2.
  - intros (t & Ht & Hb). apply elem_of_list_In, elem_of_seq in Ht.
    rewrite !andb_true_iff in Hb. destruct Hb as [[H1 H2] H3].
    apply bool_decide_eq_true_1 in H1. apply bool_decide_eq_true_1 in H2.
    destruct (log !! (t - 1)%nat) as [m|] eqn:Hm; [|done].
    exists t. split_and!; [done|done|]. exists m. split; [done|].
    rewrite /msg_writesb in H3. destruct (msg_byte m a) as [v|]; [|done].
    by exists v.
Qed.

Lemma not_writes_in_compute log a lo hi :
  writes_inb log a lo hi = false → ¬ writes_in log a lo hi.
Proof. intros Hb Hw. apply writes_inb_spec in Hw. by rewrite Hw in Hb. Qed.

Lemma writes_in_compute log a lo hi :
  writes_inb log a lo hi = true → writes_in log a lo hi.
Proof. apply writes_inb_spec. Qed.

Lemma not_writes_inb log a lo hi :
  writes_inb log a lo hi = false ↔ ¬ writes_in log a lo hi.
Proof.
  split; [apply not_writes_in_compute|].
  intros Hn. destruct (writes_inb log a lo hi) eqn:Hb; [|done].
  by destruct Hn; apply writes_in_compute.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The per-agent weak state *)

(** THE AGENT-LOCAL RESERVATION of the RMW split (design
    [claude-notes/design/weak-memory-rmw-split.md] §3): what an [LExLoad]
    banks and the matching [LExStore]'s fulfil consumes.

    [rv_ts] holds the read half's per-byte timestamps POSITIONALLY from
    [rv_base] (byte [j] at [rv_base + j]) — the vocabulary
    [WeakPromise.excl_ok_ts] consumes; values are NOT carried (the log at
    [(b, ts)] has them).  [rv_view] is the read half's banked post-view
    ([ldv_of ws aq (srcs_view ws asrc) base tvs.*1]), which the write
    half's [fulfil_vpre] must dominate (deviation D-2, PARM's exbank-view
    contribution). *)
Record wresv := WResv {
  rv_base : Z;
  rv_ts   : list nat;
  rv_view : nat;
}.
Add Printing Constructor wresv.

Global Instance wresv_eq_dec : EqDecision wresv.
Proof. solve_decision. Defined.

(** The Promising-RISC-V thread state minus promises, minus register views,
    minus the exclusives bank (design doc, Decisions 1 and 3). *)
Record wstate := WState {
  w_coh   : gmap Z nat;         (* per-byte coherence floor; default 0 *)
  w_vrOld : nat;                (* max post-view of past loads  *)
  w_vwOld : nat;                (* max post-view of past stores *)
  w_vrNew : nat;                (* pre-view floor for future loads  *)
  w_vwNew : nat;                (* pre-view floor for future stores *)
  w_vRel  : nat;                (* release view; inert until .rl appears *)
  w_fwd   : gmap Z (nat * nat); (* forward bank: timestamp + fwd view *)
  (* THE TWO M6 INERT COMPONENTS (D-M6-6, revised semantics 2026-08-12).
     Read by NO rule of any machine in this tree; they exist so that
     "published" is a total function of the state.

     [w_pub]  — the publication watermark: every log position [p] with
                [S p ≤ w_pub] of this agent is PUBLISHED.  Raised to the
                store's own timestamp at a store taken with [w_relp] set, and
                at an [rl] store.  Raising it at the FENCE instead would leave
                the flag store itself — the very message racy readers read —
                forever unpublished.
     [w_relp] — pending release: SET by a [pw ∧ sw] fence, CLEARED by the
                agent's next store (which is the publication).  It TOGGLES, so
                it is deliberately absent from [ws_le]. *)
  w_pub   : nat;
  w_relp  : bool;
  (* THE THREE DEPENDENCY COMPONENTS (D2, deps design §2.1).  Machine-owned
     timestamps computed from the labels' NAMES, exactly like [w_vwNew] —
     [ts_oblivious]-safe, because no label carries any of them.

     [w_regv] — PARM's [rmap] views: the view of each register.  It is
                ASSIGNED by [regw_post] (PARM's [step_assign] overwrites
                [rmap[lhs]]), so it is NOT monotone and is deliberately
                absent from [ws_le] — see the note there.
     [w_vcap] — PARM's [vcap]: the control/address-capture view.  Only ever
                JOINED, so it IS monotone and IS in [ws_le].
     [w_ldv]  — the post-view of the current instruction's most recent load
                (PARM's [res] view).  RESET by [instr_post] ([LInstr]), so
                like [w_relp] it is not monotone and stays out of [ws_le]. *)
  w_regv  : gmap wreg nat;
  w_vcap  : nat;
  w_ldv   : nat;
  (* THE TWO RMW-SPLIT COMPONENTS (design
     [claude-notes/design/weak-memory-rmw-split.md] §3).  Both are INERT in
     the additive slice S1: nothing but [ws_init] writes them and no step
     function reads them; the machine arms that do land in S2.

     [w_res]   — the agent-local reservation: [Some R] between an [LExLoad]
                 and its matching [LExStore].  SET by the exclusive read
                 (superseding), CLEARED by the agent's own store fulfil and
                 by [LInstr].  Like [w_fwd]/[w_regv]/[w_ldv] it is set and
                 cleared rather than joined, so it is deliberately absent
                 from [ws_le]; it IS in [ws_bounded], so that
                 [fulfil_vpre] can dominate [rv_view].
     [w_tbank] — the W-TV translation bank: the view banked by the
                 translation of the access in flight.  Also non-monotone
                 (it is rebanked per access), hence also out of [ws_le]
                 and in [ws_bounded]. *)
  w_res   : option wresv;
  w_tbank : nat;
}.
Add Printing Constructor wstate.

(** Coherence lookup with default 0. *)
Definition coh (ws : wstate) (a : Z) : nat := default 0%nat (w_coh ws !! a).

(** Register-view lookup with default 0 — the TOTAL accessor every rule
    below uses ([w_regv] is a [gmap] so that [ws_init] is [∅]). *)
Definition regv (ws : wstate) (r : wreg) : nat :=
  default 0%nat (w_regv ws !! r).

(** THE VIEW OF A DEPENDENCY SOURCE, and of a source LIST — PARM's
    [sem_expr], whose view is the join of the views of the registers the
    expression reads (deps design §2.3', row [step_assign]/[sem_expr]). *)
Definition dsrc_view (ws : wstate) (s : dsrc) : nat :=
  match s with DReg r => regv ws r | DLdRes => w_ldv ws end.

Definition srcs_view (ws : wstate) (srcs : list dsrc) : nat :=
  foldr (λ s v, Nat.max (dsrc_view ws s) v) 0%nat srcs.

(** THE INSTANCE FACT.  A label with no operands has view [0] — and it holds
    BY CONVERSION, which is what lets the D2 event language (whose labels all
    carry [asrc = dsrc = []]) reuse every dependency-free step function
    verbatim: [foo_d ws … (srcs_view ws []) … = foo ws …] by [reflexivity]. *)
Lemma srcs_view_nil ws : srcs_view ws [] = 0%nat.
Proof. done. Qed.

Lemma srcs_view_cons ws s l :
  srcs_view ws (s :: l) = Nat.max (dsrc_view ws s) (srcs_view ws l).
Proof. done. Qed.

Definition ws_init : wstate :=
  {| w_coh := ∅; w_vrOld := 0; w_vwOld := 0; w_vrNew := 0; w_vwNew := 0;
     w_vRel := 0; w_fwd := ∅; w_pub := 0; w_relp := false;
     w_regv := ∅; w_vcap := 0; w_ldv := 0;
     w_res := None; w_tbank := 0 |}.

Lemma regv_init r : regv ws_init r = 0%nat.
Proof. rewrite /regv /ws_init /= lookup_empty //. Qed.

Lemma srcs_view_init l : srcs_view ws_init l = 0%nat.
Proof.
  induction l as [|s l IH]; [done|].
  rewrite srcs_view_cons IH Nat.max_0_r.
  destruct s as [r|]; [|done]. rewrite /dsrc_view regv_init //.
Qed.

Lemma coh_init a : coh ws_init a = 0%nat.
Proof. done. Qed.

Lemma coh_upd_eq m vrO vwO vrN vwN vR fwd pb rp rg vc ld rs tb a n :
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
         w_pub := pb; w_relp := rp;
         w_regv := rg; w_vcap := vc; w_ldv := ld;
         w_res := rs; w_tbank := tb |} a = n.
Proof. rewrite /coh /= lookup_insert //. Qed.

Lemma coh_upd_ne m vrO vwO vrN vwN vR fwd pb rp rg vc ld rs tb a a' n :
  a' ≠ a →
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
         w_pub := pb; w_relp := rp;
         w_regv := rg; w_vcap := vc; w_ldv := ld;
         w_res := rs; w_tbank := tb |} a'
  = default 0%nat (m !! a').
Proof. intros ?. rewrite /coh /= lookup_insert_ne //. Qed.

(* ------------------------------------------------------------------ *)
(** ** Readability *)

(** [readable img log ws vpre a t]: the agent in state [ws] with load pre-view
    [vpre] may read timestamp [t] for byte [a].  Two conditions:
    (i) [t] writes [a]; (ii) no timestamp strictly between [t] and the agent's
    floor [vpre ⊔ coh(a)] writes [a] — i.e. [t] is not stale relative to
    anything the agent has already observed. *)
Definition readable (img : image) (log : list wmsg) (ws : wstate)
    (vpre : nat) (a : Z) (t : nat) : Prop :=
  is_Some (log_byte img log t a) ∧
  ¬ writes_in log a t (Nat.max vpre (coh ws a)).

(** The decision procedure [WeakInterp.wexec] checks a read with. *)
Definition readableb (img : image) (log : list wmsg) (ws : wstate)
    (vpre : nat) (a : Z) (t : nat) : bool :=
  match log_byte img log t a with
  | Some _ => negb (writes_inb log a t (Nat.max vpre (coh ws a)))
  | None => false
  end.

Lemma readableb_spec img log ws vpre a t :
  readableb img log ws vpre a t = true ↔ readable img log ws vpre a t.
Proof.
  rewrite /readableb /readable. destruct (log_byte img log t a) as [v|] eqn:Hv.
  - rewrite negb_true_iff not_writes_inb. split.
    + intros ?. split; [by eexists|done].
    + by intros [_ ?].
  - split; [done|]. by intros [[? ?] _].
Qed.

(** Readability is ANTI-monotone in the pre-view: a smaller floor admits more
    timestamps.  NOTE what is deliberately absent: readability is NOT
    downward-closed in [t] (a smaller timestamp can be blocked by an
    intervening write to [a]), and it is NOT upward-closed in [t] either
    (a larger timestamp need not write [a] at all).  These two are exactly the
    coherence constraints, so there is no monotonicity lemma in [t] to state. *)
Lemma readable_anti_vpre img log ws vpre vpre' a t :
  (vpre' ≤ vpre)%nat → readable img log ws vpre a t → readable img log ws vpre' a t.
Proof.
  intros Hle [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(** THE WORKHORSE of the litmus proofs: if the agent's pre-view already covers
    a write to [a], the era-initial image is no longer readable. *)
Lemma readable_not_init img log ws vpre a t :
  readable img log ws vpre a t → writes_in log a 0 vpre → t ≠ 0%nat.
Proof.
  intros [_ Hn] Hw ->. apply Hn. eapply writes_in_mono_hi; [|done]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Coherent (latest) reads

    Two consumers: the AMO/exclusive read half, whose atomicity constraint is
    exactly this side condition, and the reads the design doc declares
    coherent — instruction fetch and the page-table walker (Decision 6).
    [latest] pins the timestamp uniquely ([latest_unique]), so a coherent read
    is deterministic even though it is stated relationally. *)

Definition latest (img : image) (log : list wmsg) (a : Z) (t : nat) : Prop :=
  is_Some (log_byte img log t a) ∧ ¬ writes_in log a t (length log).

Lemma latest_unique img log a t t' :
  latest img log a t → latest img log a t' → t = t'.
Proof.
  intros [Ht Hnt] [Ht' Hnt'].
  destruct (decide (t < t')%nat) as [Hlt|?].
  { exfalso. apply Hnt. apply (writes_in_log_byte img). exists t'.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht'). }
  destruct (decide (t' < t)%nat) as [Hlt'|?].
  { exfalso. apply Hnt'. apply (writes_in_log_byte img). exists t.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht). }
  lia.
Qed.

(** A latest timestamp is readable at any pre-view: nothing above it writes
    [a] at all, so in particular nothing in the agent's window does. *)
Lemma latest_readable img log ws vpre a t :
  (Nat.max vpre (coh ws a) ≤ length log)%nat →
  latest img log a t → readable img log ws vpre a t.
Proof.
  intros Hle [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(** The COMPUTED latest timestamp: the index (+1) of the last message writing
    [a], or 0 (the era-initial image) if none does. *)
Definition latest_ts_acc (log : list wmsg) (a : Z) : nat * nat :=
  foldl (λ p m, (S p.1, if msg_writesb m a then S p.1 else p.2)) (0%nat, 0%nat) log.

Definition latest_ts (log : list wmsg) (a : Z) : nat := (latest_ts_acc log a).2.

Lemma latest_ts_acc_fst log a : (latest_ts_acc log a).1 = length log.
Proof.
  rewrite /latest_ts_acc. induction log as [|m l IH] using rev_ind; [done|].
  rewrite foldl_app /= IH length_app /=. lia.
Qed.

Lemma latest_ts_nil a : latest_ts [] a = 0%nat.
Proof. done. Qed.

Lemma latest_ts_app log m a :
  latest_ts (log ++ [m]) a =
  (if msg_writesb m a then S (length log) else latest_ts log a).
Proof.
  rewrite /latest_ts /latest_ts_acc foldl_app /=.
  rewrite -/(latest_ts_acc log a) latest_ts_acc_fst.
  by destruct (msg_writesb m a).
Qed.

Lemma latest_ts_le log a : (latest_ts log a ≤ length log)%nat.
Proof.
  induction log as [|m l IH] using rev_ind; [done|].
  rewrite latest_ts_app length_app /=. destruct (msg_writesb m a); lia.
Qed.

(** Nothing above [latest_ts] writes [a] — unconditionally, including the
    "nothing writes [a] at all" case, where [latest_ts = 0]. *)
Lemma latest_ts_top log a : ¬ writes_in log a (latest_ts log a) (length log).
Proof.
  induction log as [|m l IH] using rev_ind.
  { intros (t & ? & ? & ?). simpl in *. lia. }
  rewrite latest_ts_app length_app /=.
  destruct (msg_writesb m a) eqn:Hm.
  - intros (t & ? & ? & ?). lia.
  - intros (t & Hlo & Hhi & mm & Hmm & Hs).
    destruct (decide (t ≤ length l)%nat) as [Hle|Hgt].
    + apply IH. exists t. split_and!; [done|done|]. exists mm.
      rewrite lookup_app_l in Hmm; [lia|]. by split.
    + assert (t = S (length l)) as -> by lia.
      replace (S (length l) - 1)%nat with (length l) in Hmm by lia.
      rewrite lookup_app_r in Hmm; [lia|].
      rewrite Nat.sub_diag /= in Hmm. simplify_eq.
      apply msg_writesb_false in Hm. rewrite Hm in Hs. by destruct Hs.
Qed.

Lemma latest_ts_latest img log a :
  is_Some (log_byte img log (latest_ts log a) a) → latest img log a (latest_ts log a).
Proof. intros ?. split; [done|apply latest_ts_top]. Qed.

(** [latest_ts] is either 0 (nothing in the log writes [a]) or the index of a
    message that does. *)
Lemma latest_ts_writes log a :
  latest_ts log a = 0%nat ∨
  ∃ i m, latest_ts log a = S i ∧ log !! i = Some m ∧ is_Some (msg_byte m a).
Proof.
  induction log as [|m l IH] using rev_ind; [by left|].
  rewrite latest_ts_app. destruct (msg_writesb m a) eqn:Hm.
  - right. exists (length l), m. split_and!; [done| |].
    + rewrite lookup_app_r; [lia|]. rewrite Nat.sub_diag //.
    + by apply msg_writesb_true.
  - destruct IH as [Hz|(i & m' & Hr & Hlk & Hs)]; [by left|].
    right. exists i, m'. split_and!; [exact Hr| |exact Hs].
    rewrite lookup_app_l; [|exact Hlk]. by apply lookup_lt_Some in Hlk.
Qed.

(** If ANY timestamp holds a value for [a], then so does [latest_ts]. *)
Lemma latest_ts_some img log a t :
  is_Some (log_byte img log t a) →
  is_Some (log_byte img log (latest_ts log a) a).
Proof.
  intros Ht. destruct (latest_ts_writes log a) as [Hz|(i & m & Hr & Hlk & Hs)].
  - rewrite Hz log_byte_0. destruct t as [|i]; [exact Ht|exfalso].
    apply (latest_ts_top log a). rewrite Hz.
    apply (writes_in_log_byte img). exists (S i).
    split_and!; [lia|exact (log_byte_bounded _ _ _ _ Ht)|exact Ht].
  - rewrite Hr log_byte_S Hlk /=. exact Hs.
Qed.

(** Hence [latest_ts] IS the latest timestamp whenever one exists — the fact
    that makes a coherent read deterministic. *)
Lemma latest_ts_eq img log a t : latest img log a t → latest_ts log a = t.
Proof.
  intros Hl. apply (latest_unique img log a);
    [|exact Hl].
  split; [exact (latest_ts_some img log a t (proj1 Hl))|apply latest_ts_top].
Qed.

(** SC DEGENERACY.  An agent whose read floor already covers the whole log has
    no read choice: readability collapses to [latest]. *)
Lemma readable_all_seen img log ws vpre a t :
  (length log ≤ vpre)%nat → readable img log ws vpre a t → latest img log a t.
Proof.
  intros Hall [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The step functions *)

(** Loads.  Pre-view [vpre = vrNew ⊔ (aq ? vRel)]. *)
Definition load_vpre (ws : wstate) (aq : bool) : nat :=
  Nat.max (w_vrNew ws) (if aq then w_vRel ws else 0%nat).

(** PARM's full read [view_pre] (Promising.v:841):
    [view(addr) ⊔ vrn ⊔ (ord ≥ acquire ? vrel)].  [vaddr] is the ADDRESS
    dependency view [V(asrc)], supplied by the machine's read arm from the
    label's operand names.

    THE ARGUMENT IS FIRST INSIDE THE [Nat.max] ON PURPOSE: [Nat.max 0 x]
    reduces to [x] by [iota], so [load_vpre_d ws aq 0 ≡ load_vpre ws aq] BY
    CONVERSION.  Every [_d] function below follows the same discipline, which
    is what makes the dependency-free names honest INSTANCES (and not merely
    propositionally equal copies) — see [srcs_view_nil]. *)
Definition load_vpre_d (ws : wstate) (aq : bool) (vaddr : nat) : nat :=
  Nat.max vaddr (load_vpre ws aq).

Lemma load_vpre_d_0 ws aq : load_vpre_d ws aq 0%nat = load_vpre ws aq.
Proof. done. Qed.

Lemma load_vpre_load_vpre_d ws aq vaddr :
  (load_vpre ws aq ≤ load_vpre_d ws aq vaddr)%nat.
Proof. rewrite /load_vpre_d. lia. Qed.

(** THE FORWARD BANK, wired into the read view at M1 (design doc, Decision 3).

    A load that reads the timestamp the agent's own last store to [a] left in
    the bank is FORWARDED: it takes the view the bank recorded instead of the
    timestamp itself.  Any other timestamp contributes [t] as before.

    WHAT THE BANK RECORDS (corrected 2026-08-17, deps design §2.3′ D-7).
    Promising-ARM/RISC-V banks [FwdItem.mk ts (join view_loc view_val) ex]:
    the store's ADDRESS and DATA dependency views, which is RVWMO ppo 12 —
    "a load that reads an intermediate store inherits that store's syntactic
    dependencies", and nothing else.  In a machine with no register views
    (today's) that join is [0], so [store_post] banks [0]; the dependency
    track (D2) will replace it by [V(asrc) ⊔ V(dsrc)].
    M1 banked [w_vwNew ws] — the store's FENCE FLOOR — instead, and described
    it as "the weakest sound choice".  That was the wrong polarity: the fence
    floor is ≥ PARM's value, so it makes the forwarded read's post-view LARGER
    and hence REMOVES hardware behaviours (e.g. [fence rw,w; st x; ld x (fwd);
    fence r,r; ld y] ordered [ld y] after the pre-fence accesses in our
    machine but not in RVWMO).  Smaller is the sound direction here: a
    forwarded read is the one place where the model deliberately declines to
    inherit ordering, and [0] is exactly PARM's dependency-free value.

    FAITHFULNESS TO PROMISING-ARM'S [read_view] — CORRECTED BY THE D2 D-5
    AUDIT (deps design §2.3' D-5b).  PARM's [FwdItem.read_view]
    (Promising.v:529) takes the banked view iff
    [fwd.ts = t ∧ ¬(fwd.ex ∧ (arch = riscv ∨ ord ≥ acquire_pc))], which AT
    [arch = riscv] is [fwd.ts = t ∧ ¬fwd.ex]: the READ ORDER plays NO role,
    and what disables forwarding is that the BANKED STORE was the write half
    of an exclusive.  Ours tests [aq] instead and records no [ex], so it
    deviates in BOTH directions:
    - STRONGER on an acquire load that would have forwarded a PLAIN store
      (the banked view is below the banked timestamp — the store's own EXT —
      so taking [t] raises the post-view);
    - WEAKER on any load forwarding an EXCLUSIVE store.
    Both are vacuous for xv6, whose only acquires are [amoswap.w.aq] (an
    exclusive read, which would have to forward its own earlier exclusive
    store).  Making the rule faithful means an [ex] flag in [w_fwd]'s payload
    and dropping the [aq] test; D2 deliberately does neither, and the earlier
    header claim that "PARM does the same" is retracted here. *)
Definition fwd_view (ws : wstate) (aq : bool) (a : Z) (t : nat) : nat :=
  if aq then t
  else match w_fwd ws !! a with
       | Some (tf, vf) => if bool_decide (t = tf) then vf else t
       | None => t
       end.

Lemma fwd_view_aq ws a t : fwd_view ws true a t = t.
Proof. done. Qed.

Lemma fwd_view_miss ws aq a t : w_fwd ws !! a = None → fwd_view ws aq a t = t.
Proof. rewrite /fwd_view. destruct aq; [done|]. by move=> ->. Qed.

Lemma fwd_view_empty ws aq a t : w_fwd ws = ∅ → fwd_view ws aq a t = t.
Proof. intros H. apply fwd_view_miss. rewrite H lookup_empty //. Qed.

Lemma fwd_view_hit ws a t tf vf :
  w_fwd ws !! a = Some (tf, vf) → t = tf → fwd_view ws false a t = vf.
Proof.
  intros Hf ->. rewrite /fwd_view Hf. case_bool_decide; [done|congruence].
Qed.

(** The post-view update at an explicitly supplied pre-view (so that a
    multi-byte load computes [vpre] ONCE, from the pre-load state).

    [vpost] is the FORWARDED view; the COHERENCE floor still takes the raw
    timestamp [t] (PARM updates [coh] with the timestamp, not the read view —
    forwarding weakens ordering, never coherence).  That split is what keeps
    every [coh] fact of the spike literally true while the vrOld/vrNew floors
    become forwarding-sensitive. *)
(** THE PER-BYTE READ UPDATE.  It is UNCHANGED by D2 except for [w_ldv]:
    the ADDRESS dependency view enters a load only through its PRE-VIEW
    ([load_vpre_d], threaded by [load_post_bytes_d]) and through [w_vcap]
    (raised once, by the run-level wrapper [load_post_run_d]) — never
    per byte.  Keeping [vaddr] OUT of this function is what lets every
    generic fold lemma below, all of which quantify over an arbitrary
    [vpre], serve the dependency-carrying machine verbatim. *)
Definition load_post_at (ws : wstate) (aq : bool) (vpre : nat) (a : Z) (t : nat)
    : wstate :=
  let vpost := Nat.max vpre (fwd_view ws aq a t) in
  {| w_coh   := <[a := Nat.max (coh ws a) (Nat.max vpost t)]> (w_coh ws);
     w_vrOld := Nat.max (w_vrOld ws) vpost;
     w_vwOld := w_vwOld ws;
     w_vrNew := if aq then Nat.max (w_vrNew ws) vpost else w_vrNew ws;
     w_vwNew := if aq then Nat.max (w_vwNew ws) vpost else w_vwNew ws;
     w_vRel  := w_vRel ws;
     w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;
     w_relp  := w_relp ws;
     w_regv  := w_regv ws;
     w_vcap  := w_vcap ws;
     (* PARM: [res := (val, view_post)] ([Local.read]'s [RES]).  JOINED, not
        assigned, so that a MULTI-BYTE load (deviation D-1) banks the MAX
        post-view over its bytes; [instr_post] ([LInstr]) resets it at every
        instruction start, so nothing accumulates across instructions, and
        [ldv_of] below computes it from a zeroed bank for the RMW. *)
     w_ldv   := Nat.max (w_ldv ws) vpost;
     (* THE RMW SPLIT (S2) + A2-s3: A PLAIN LOAD CLEARS THE AGENT'S OWN
        RESERVATION (the clear-on-own-load rule, design
        weak-memory-srvwmo.md stage 2 / A2-s3).  ISA-legal (a reservation
        may be invalidated at any time; the LR/SC forward-progress
        guarantee itself excludes loads inside constrained loops), and no
        real window contains a plain load — the AMO's and the walker's
        windows are register-only — so the machine loses no behaviour any
        kernel proof consumes.  What it buys is T2's re-fusion: a
        load-dirtied window starves [PFExStore] (the retry arm spins), so
        the pending-pair invariant's [w_res = Some R] guard dies exactly
        where the fused counterpart stops existing.  The exclusive read's
        arm still sets [w_res] at the RUN level ([exload_post_run_d]),
        superseding this clear. *)
     w_res   := None;
     (* W-TV, THE TRANSLATION BANK (W2b condition 2).  Every read byte BANKS
        its own contribution, and the contribution is [fwd_view] — the
        forwarded timestamp — NOT the byte's post-view [vpost]: [vpost]
        carries [vpre], hence [w_vrNew], and joining that into the next
        access's [w_vcap] would drag a fence floor into every fulfil's EXT
        (the audit's [wtv_ldv_leaks_vrNew] probe, which is also why the bank
        is NOT [w_ldv]).  The bank is CONSUMED at the next access node's
        [ctrl_post] and RESET by [instr_post]. *)
     w_tbank := Nat.max (w_tbank ws) (fwd_view ws aq a t) |}.

Definition load_post (ws : wstate) (aq : bool) (a : Z) (t : nat) : wstate :=
  load_post_at ws aq (load_vpre ws aq) a t.

(** Stores.  Promise-free: the timestamp is always the log's fresh top, so the
    store rule has no admissibility condition to check. *)
(** [w_pub]/[w_relp] (M6, inert): a store taken with the release-pending flag
    set — or an [.rl] store — PUBLISHES, raising the watermark to its own
    timestamp; the flag is cleared either way.

    IDEMPOTENCE NOTE.  [store_post_bytes] folds [store_post] per byte at the
    SAME timestamp [t], so the FIRST byte performs the raise and clears
    [w_relp]; every later byte sees [w_relp = false] and (unless [rl]) leaves
    [w_pub] alone.  With [rl] the later bytes redo [Nat.max _ t], which is
    idempotent.  Net effect over a whole access: exactly one raise to [t] iff
    the access publishes — which is what [published p := S p ≤ w_pub] needs. *)
(** THE PER-BYTE WRITE UPDATE, dependency-carrying.  [vf] is the view the
    FORWARD BANK records — PARM's [FwdItem.mk ts (join view_loc view_val) ex]
    (Promising.v:909), i.e. [V(asrc) ⊔ V(dsrc)]; deviation D-7 fixed the [0]
    that stood here while the machine had no register views.  [w_vcap] is NOT
    raised here: PARM raises it once per access ([vcap ⊔= view_loc]), which is
    what the run-level wrapper [store_post_run_d] does. *)
Definition store_post_d (ws : wstate) (rl : bool) (vf : nat)
    (a : Z) (t : nat) : wstate :=
  {| w_coh   := <[a := Nat.max (coh ws a) t]> (w_coh ws);
     w_vrOld := w_vrOld ws;
     w_vwOld := Nat.max (w_vwOld ws) t;
     w_vrNew := w_vrNew ws;
     w_vwNew := w_vwNew ws;
     w_vRel  := if rl then Nat.max (w_vRel ws) t else w_vRel ws;
     (* THE FORWARD BANK.  The recorded view is PARM's [FwdItem] view, i.e.
        the store's ADDRESS/DATA dependency views [V(asrc) ⊔ V(dsrc)] (RVWMO
        ppo 12); today's machine has no register views, so that is [0].  D2
        (the dependency track) replaces the [0] by [V(asrc) ⊔ V(dsrc)].
        It is deliberately NOT [w_vwNew ws] (the store's fence floor): that
        was the M1 choice and it is LARGER than PARM's, i.e. it REMOVES
        hardware behaviours (design doc deps §2.3′ D-7, fixed 2026-08-17). *)
     w_fwd   := <[a := (t, vf)]> (w_fwd ws);
     w_pub   := if (w_relp ws || rl)%bool then Nat.max (w_pub ws) t
                else w_pub ws;
     w_relp  := false;
     w_regv  := w_regv ws;
     w_vcap  := w_vcap ws;
     w_ldv   := w_ldv ws;
     (* THE RMW SPLIT (S2).  A STORE CLEARS THE AGENT'S OWN RESERVATION
        (design §3, the clear-on-own-store rule): a same-agent store to the
        byte between an exclusive read and its conditional write must make
        [w_res = Some R] at the write REFUTE that case, which is what turns
        the L2 no-store window into a theorem.  It is done PER BYTE rather
        than once per run so that every generic fold lemma — and every
        consumer that unfolds [store_post_bytes] — keeps its shape; the two
        agree on every access the machine can take, since a message in the
        log always has [data ≠ []] ([WPPromise]).
        [w_tbank] rides through: a store BANKS nothing (W-TV banks reads). *)
     w_res   := None;
     w_tbank := w_tbank ws |}.

Definition store_post (ws : wstate) (rl : bool) (a : Z) (t : nat) : wstate :=
  {| w_coh   := <[a := Nat.max (coh ws a) t]> (w_coh ws);
     w_vrOld := w_vrOld ws;
     w_vwOld := Nat.max (w_vwOld ws) t;
     w_vrNew := w_vrNew ws;
     w_vwNew := w_vwNew ws;
     w_vRel  := if rl then Nat.max (w_vRel ws) t else w_vRel ws;
     w_fwd   := <[a := (t, 0%nat)]> (w_fwd ws);
     w_pub   := if (w_relp ws || rl)%bool then Nat.max (w_pub ws) t
                else w_pub ws;
     w_relp  := false;
     w_regv  := w_regv ws;
     w_vcap  := w_vcap ws;
     w_ldv   := w_ldv ws;
     (* THE RMW SPLIT (S2): see [store_post_d]. *)
     w_res   := None;
     w_tbank := w_tbank ws |}.

Lemma store_post_d_0 ws rl a t :
  store_post_d ws rl 0%nat a t = store_post ws rl a t.
Proof. done. Qed.

(** FENCE pred,succ.  [pr]/[pw] are R/W ∈ pred; [sr]/[sw] are R/W ∈ succ.
    [fence.tso] = [fence r,r ; fence rw,w]. *)
Definition fence_post (ws : wstate) (pr pw sr sw : bool) : wstate :=
  let v1 := Nat.max (if pr then w_vrOld ws else 0%nat)
                    (if pw then w_vwOld ws else 0%nat) in
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws;
     w_vwOld := w_vwOld ws;
     w_vrNew := if sr then Nat.max (w_vrNew ws) v1 else w_vrNew ws;
     w_vwNew := if sw then Nat.max (w_vwNew ws) v1 else w_vwNew ws;
     w_vRel  := w_vRel ws;
     w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;
     (* M6, inert: a [pw ∧ sw] fence ([fence rw,w]) ARMS the next store as the
        publication of everything it covers. *)
     w_relp  := if (pw && sw)%bool then true else w_relp ws;
     (* PARM's [Local.dmb] touches neither [rmap] nor [vcap]; [isb]
        ([vrn ⊔= vcap]) has no RISC-V counterpart (deps design §2.3'). *)
     w_regv  := w_regv ws;
     w_vcap  := w_vcap ws;
     w_ldv   := w_ldv ws;
     (* A2-s3: A REAL FENCE CLEARS THE RESERVATION (clear-on-own-fence,
        the twin of [load_post_at]'s clear-on-own-load — see the rationale
        there).  This is what makes [lr; fence; sc] machine-unreachable:
        the fused alphabet has no counterpart for it (the re-fusion
        obstacle of 2026-08-19), so the machine starving the conditional
        write is exactly the T1/T2 equality's sound direction.  The
        ALL-FALSE fence is exempt: it is [fence.i]'s inert rendering
        ([WeakEvInst] (D2)), [LSilent] in the wp-machine LTS
        ([WeakSailLTS]), and both tiers depend on it being the identity
        ([fence_post_id]). *)
     w_res   := if (pr || pw || sr || sw)%bool then None else w_res ws;
     w_tbank := w_tbank ws |}.

Lemma fence_post_id ws : fence_post ws false false false false = ws.
Proof. rewrite /fence_post /=. by destruct ws. Qed.

(* ------------------------------------------------------------------ *)
(** ** The three DEPENDENCY-ONLY label effects (deps design §2.3)

    None of them touches memory, the log or any memory view: they only move
    the register/control/load-result bookkeeping, so every machine's arm for
    them is [LSilent]'s arm with a different [wstate] update. *)

(** [LRegW rd srcs]: PARM's [step_assign] — [rmap[lhs] := (val, view of the
    expression)].  An ASSIGNMENT, not a join: a register that is overwritten
    with a dependency-free value LOSES its view.  (This is why [w_regv] is
    not in [ws_le]; see the note there.) *)
Definition regw_post (ws : wstate) (rd : wreg) (v : nat) : wstate :=
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws; w_vwOld := w_vwOld ws;
     w_vrNew := w_vrNew ws; w_vwNew := w_vwNew ws;
     w_vRel  := w_vRel ws;  w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;   w_relp  := w_relp ws;
     w_regv  := <[rd := v]> (w_regv ws);
     w_vcap  := w_vcap ws;  w_ldv   := w_ldv ws;
     (* [LRegW] does NOT clear the reservation: the AMO's [rd] write fires
        between its exclusive read and its conditional write (RMW split
        §3). *)
     w_res   := w_res ws;   w_tbank := w_tbank ws |}.

(** [LCtrl srcs]: PARM's [Local.control] — [vcap ⊔= ctrl]. *)
Definition ctrl_post (ws : wstate) (v : nat) : wstate :=
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws; w_vwOld := w_vwOld ws;
     w_vrNew := w_vrNew ws; w_vwNew := w_vwNew ws;
     w_vRel  := w_vRel ws;  w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;   w_relp  := w_relp ws;
     w_regv  := w_regv ws;
     w_vcap  := Nat.max v (w_vcap ws);
     w_ldv   := w_ldv ws;
     (* [LCtrl] does NOT clear the reservation either (RMW split §3). *)
     w_res   := w_res ws;   w_tbank := w_tbank ws |}.

(** *** [ctrl_post] is transparent to everything but [w_vcap]

    Stated here, next to the definition, because the run-level wrappers below
    ([load_post_run] &c.) all end in a [ctrl_post] and every field fact about
    them peels it with one of these. *)

Lemma ctrl_post_coh ws v a : coh (ctrl_post ws v) a = coh ws a.
Proof. done. Qed.
Lemma ctrl_post_vrOld ws v : w_vrOld (ctrl_post ws v) = w_vrOld ws.
Proof. done. Qed.
Lemma ctrl_post_vwOld ws v : w_vwOld (ctrl_post ws v) = w_vwOld ws.
Proof. done. Qed.
Lemma ctrl_post_vrNew ws v : w_vrNew (ctrl_post ws v) = w_vrNew ws.
Proof. done. Qed.
Lemma ctrl_post_vwNew ws v : w_vwNew (ctrl_post ws v) = w_vwNew ws.
Proof. done. Qed.
Lemma ctrl_post_vRel ws v : w_vRel (ctrl_post ws v) = w_vRel ws.
Proof. done. Qed.
Lemma ctrl_post_fwd ws v : w_fwd (ctrl_post ws v) = w_fwd ws.
Proof. done. Qed.
Lemma ctrl_post_pub ws v : w_pub (ctrl_post ws v) = w_pub ws.
Proof. done. Qed.
Lemma ctrl_post_relp ws v : w_relp (ctrl_post ws v) = w_relp ws.
Proof. done. Qed.
Lemma ctrl_post_regv ws v r : regv (ctrl_post ws v) r = regv ws r.
Proof. done. Qed.
Lemma ctrl_post_ldv ws v : w_ldv (ctrl_post ws v) = w_ldv ws.
Proof. done. Qed.
Lemma ctrl_post_res ws v : w_res (ctrl_post ws v) = w_res ws.
Proof. done. Qed.
Lemma ctrl_post_tbank ws v : w_tbank (ctrl_post ws v) = w_tbank ws.
Proof. done. Qed.
Lemma ctrl_post_vcap ws v : w_vcap (ctrl_post ws v) = Nat.max v (w_vcap ws).
Proof. done. Qed.

(** [LInstr]: instruction start.  Resets the load-result bank, which is what
    scopes [DLdRes] to ONE instruction. *)
Definition instr_post (ws : wstate) : wstate :=
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws; w_vwOld := w_vwOld ws;
     w_vrNew := w_vrNew ws; w_vwNew := w_vwNew ws;
     w_vRel  := w_vRel ws;  w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;   w_relp  := w_relp ws;
     w_regv  := w_regv ws;  w_vcap  := w_vcap ws;
     w_ldv   := 0%nat;
     (* THE RMW SPLIT (S2) + W-TV.  Instruction start is BOTH the
        reservation's GC point (RMW split §3: an [LExLoad] and its
        conditional write live in one instruction, so a reservation that
        crosses a boundary is dead) AND the translation bank's reset (W2b
        condition 1: without it the next instruction's fetch would consume
        this instruction's data-read views). *)
     w_res   := None;       w_tbank := 0%nat |}.

Lemma regv_regw_post_eq ws rd v : regv (regw_post ws rd v) rd = v.
Proof. rewrite /regv /regw_post /= lookup_insert //. Qed.

Lemma regv_regw_post_ne ws rd v r : r ≠ rd → regv (regw_post ws rd v) r = regv ws r.
Proof. intros ?. rewrite /regv /regw_post /= lookup_insert_ne //. Qed.

(** Multi-byte accesses are per-byte folds.  [vpre] is computed once from the
    PRE-load state, which is why [load_post_at] takes it explicitly: folding
    [load_post] itself would let an acquire load's own [vrNew] update raise the
    pre-view of its later bytes. *)
Definition load_post_bytes_d (ws : wstate) (aq : bool) (vaddr : nat)
    (ats : list (Z * nat)) : wstate :=
  foldl (λ w at_, load_post_at w aq (load_vpre_d ws aq vaddr) at_.1 at_.2)
        ws ats.

Definition load_post_bytes (ws : wstate) (aq : bool) (ats : list (Z * nat))
    : wstate :=
  foldl (λ w at_, load_post_at w aq (load_vpre ws aq) at_.1 at_.2) ws ats.

Lemma load_post_bytes_d_0 ws aq ats :
  load_post_bytes_d ws aq 0%nat ats = load_post_bytes ws aq ats.
Proof. done. Qed.

Definition store_post_bytes_d (ws : wstate) (rl : bool) (vf : nat)
    (as_ : list Z) (t : nat) : wstate :=
  foldl (λ w a, store_post_d w rl vf a t) ws as_.

Definition store_post_bytes (ws : wstate) (rl : bool) (as_ : list Z) (t : nat)
    : wstate :=
  foldl (λ w a, store_post w rl a t) ws as_.

Lemma store_post_bytes_d_0 ws rl as_ t :
  store_post_bytes_d ws rl 0%nat as_ t = store_post_bytes ws rl as_ t.
Proof. done. Qed.

(** The CONTIGUOUS instances the interpreter uses: byte [j] of an access whose
    base byte address is [base] lives at [base + j] (see [WeakInterp.acc_addr]
    for why the seam is spelled additively rather than through the model's own
    [pa_add]). *)
Definition load_run_ats (base : Z) (ts : list nat) : list (Z * nat) :=
  zip_with (λ j t, (base + Z.of_nat j, t)) (seq 0 (length ts)) ts.

(** THE RUN-LEVEL READ.  The [ctrl_post] wrapper is PARM's
    [vcap ⊔= view(addr)], applied ONCE per access rather than per byte
    (per-byte would be the same join, but hoisting it keeps every per-byte
    lemma dependency-free), joined with W-TV's TRANSLATION BANK.

    W-TV, THE CONSUMPTION SIDE (W2b conditions 4/5).  [w_tbank] is PRODUCED
    by [load_post_at] and RESET by [instr_post]; it is CONSUMED here, by
    every run-level access, which joins it into [w_vcap] alongside the
    address view.  Three things about the shape, none accidental:

    1. THE BANK IS READ AT THE ENTRY STATE ([w_tbank ws], not the bank of
       the folded post-state): the node consumes what the translation of the
       access in flight banked, and a load's own byte-banking must not feed
       its own consumption (W2b condition 4).
    2. THE NON-[_d] TIER CARRIES THE BANK TOO (option α).  The
       dependency-free names ARE the [_d] ones at operand view [0], and
       [Nat.max 0 x] is [x] by conversion, so [load_post_run_d_0] /
       [store_post_run_d_0] stay EXACT equalities — which is what keeps the
       ~20 [_0] call sites ([WeakSailLTS]'s [pf_load]/[pf_store]/[pf_rmw],
       [WeakSailComplete], [WeakSailLTS2], [WeakEvCapstone],
       [WeakPromiseBridge]) and [WeakPromiseBridge.cfg_match]'s per-agent
       [wstate] EQUALITY with the axiomatic tier textually unchanged.  The
       price is that the AXIOMATIC tier ([WeakAxiomatic.mstep], which steps
       with [load_post_run]) consumes the bank as well; the T1 completeness
       invariant does not constrain [w_vcap]/[w_tbank], so it does not see
       this.
    3. THE ERASURE ([WeakErase]) DOES NOT RELATE [w_vcap] any more: the
       erased run maps [LInstr] to [LSilent], so it never resets the bank
       and its [w_vcap] can OVERTAKE the instance's.  Nothing in the pf
       fragment reads [w_vcap] (there is no [fulfil_ok] there at all), so
       the erasure runs on [ws_le_nc] — see the note at [ws_le_nc] below.

    The l-side mirror ([WeakRobustProv]: [l_tbank] + the [lrel] conjunct
    [w_tbank w = lval σ (l_tbank S)]) mirrors production, reset AND
    consumption. *)
Definition load_post_run_d (ws : wstate) (aq : bool) (vaddr : nat) (base : Z)
    (ts : list nat) : wstate :=
  ctrl_post (load_post_bytes_d ws aq vaddr (load_run_ats base ts))
            (Nat.max vaddr (w_tbank ws)).

Definition load_post_run (ws : wstate) (aq : bool) (base : Z) (ts : list nat)
    : wstate :=
  ctrl_post
    (load_post_bytes ws aq
       (zip_with (λ j t, (base + Z.of_nat j, t)) (seq 0 (length ts)) ts))
    (w_tbank ws).

Definition store_run_as (base : Z) (n : nat) : list Z :=
  map (λ j : nat, base + Z.of_nat j) (seq 0 n).

Definition store_post_run_d (ws : wstate) (rl : bool) (vaddr vdata : nat)
    (base : Z) (n : nat) (t : nat) : wstate :=
  ctrl_post
    (store_post_bytes_d ws rl (Nat.max vaddr vdata) (store_run_as base n) t)
    (Nat.max vaddr (w_tbank ws)).

Definition store_post_run (ws : wstate) (rl : bool) (base : Z) (n : nat)
    (t : nat) : wstate :=
  ctrl_post
    (store_post_bytes ws rl (map (λ j : nat, base + Z.of_nat j) (seq 0 n)) t)
    (w_tbank ws).

(** The dependency-free names ARE the [_d] functions at operand view [0].
    At the BYTE level this is conversion; at the RUN level it stays
    conversion too, because [Nat.max 0 v] reduces to [v] — the [ctrl_post_0]
    peel the pre-W-TV wrappers needed is gone with the [vaddr]-only
    argument. *)
Lemma ctrl_post_0 ws : ctrl_post ws 0%nat = ws.
Proof. by destruct ws. Qed.

Lemma load_post_run_d_0 ws aq base ts :
  load_post_run_d ws aq 0%nat base ts = load_post_run ws aq base ts.
Proof. done. Qed.

Lemma store_post_run_d_0 ws rl base n t :
  store_post_run_d ws rl 0%nat 0%nat base n t = store_post_run ws rl base n t.
Proof. done. Qed.

(** The bank equations: no run-level access CHANGES the bank (the fold's
    per-byte banking is the load's, and [ctrl_post] is transparent), and the
    bank it consumed is below the control view it produced — the [vcapat]
    producer of W2b condition 5. *)
Lemma load_post_run_d_tbank_vcap ws aq vaddr base ts :
  (w_tbank ws ≤ w_vcap (load_post_run_d ws aq vaddr base ts))%nat.
Proof. rewrite /load_post_run_d ctrl_post_vcap. lia. Qed.

Lemma store_post_run_d_tbank_vcap ws rl vaddr vdata base n t :
  (w_tbank ws ≤ w_vcap (store_post_run_d ws rl vaddr vdata base n t))%nat.
Proof. rewrite /store_post_run_d ctrl_post_vcap. lia. Qed.

(** THE EXCLUSIVE-BANK VIEW (PARM's [Exbank.view], deviation D-2): the read
    half's own [view_post], i.e. the max post-view over the bytes of a load
    run — computed FROM A ZEROED [w_ldv] so that it is exactly this access's
    result view and not a join with whatever the instruction loaded before. *)
Definition ws_ldv0 (ws : wstate) : wstate := instr_post ws.

Definition ldv_of (ws : wstate) (aq : bool) (vaddr : nat) (base : Z)
    (ts : list nat) : nat :=
  w_ldv (load_post_run_d (ws_ldv0 ws) aq vaddr base ts).

(* ------------------------------------------------------------------ *)
(** ** THE EXCLUSIVE READ'S POST-STATE (RMW split S2, design §3/§4)

    [LExLoad]'s read semantics are [LLoad]'s at [lat = false] — literally
    [load_post_run_d] at the same arguments — PLUS the agent-local
    reservation.  Nothing else about the load changes, which is what makes
    every fold/monotonicity/boundedness fact about [load_post_run_d]
    available here through one record-update wrapper.

    THE RESERVATION SUPERSEDES: an exclusive read overwrites whatever
    [w_res] held (design §3's "superseding" row), it does not join. *)
Definition ws_res_set (ws : wstate) (r : option wresv) : wstate :=
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws; w_vwOld := w_vwOld ws;
     w_vrNew := w_vrNew ws; w_vwNew := w_vwNew ws;
     w_vRel  := w_vRel ws;  w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;   w_relp  := w_relp ws;
     w_regv  := w_regv ws;  w_vcap  := w_vcap ws;  w_ldv := w_ldv ws;
     w_res   := r;          w_tbank := w_tbank ws |}.

(** Every projection but [w_res] is transparent, BY CONVERSION. *)
Lemma ws_res_set_coh ws r a : coh (ws_res_set ws r) a = coh ws a.
Proof. done. Qed.
Lemma ws_res_set_vrOld ws r : w_vrOld (ws_res_set ws r) = w_vrOld ws.
Proof. done. Qed.
Lemma ws_res_set_vwOld ws r : w_vwOld (ws_res_set ws r) = w_vwOld ws.
Proof. done. Qed.
Lemma ws_res_set_vrNew ws r : w_vrNew (ws_res_set ws r) = w_vrNew ws.
Proof. done. Qed.
Lemma ws_res_set_vwNew ws r : w_vwNew (ws_res_set ws r) = w_vwNew ws.
Proof. done. Qed.
Lemma ws_res_set_vRel ws r : w_vRel (ws_res_set ws r) = w_vRel ws.
Proof. done. Qed.
Lemma ws_res_set_fwd ws r : w_fwd (ws_res_set ws r) = w_fwd ws.
Proof. done. Qed.
Lemma ws_res_set_pub ws r : w_pub (ws_res_set ws r) = w_pub ws.
Proof. done. Qed.
Lemma ws_res_set_relp ws r : w_relp (ws_res_set ws r) = w_relp ws.
Proof. done. Qed.
Lemma ws_res_set_regv ws r x : regv (ws_res_set ws r) x = regv ws x.
Proof. done. Qed.
Lemma ws_res_set_vcap ws r : w_vcap (ws_res_set ws r) = w_vcap ws.
Proof. done. Qed.
Lemma ws_res_set_ldv ws r : w_ldv (ws_res_set ws r) = w_ldv ws.
Proof. done. Qed.
Lemma ws_res_set_tbank ws r : w_tbank (ws_res_set ws r) = w_tbank ws.
Proof. done. Qed.
Lemma ws_res_set_res ws r : w_res (ws_res_set ws r) = r.
Proof. done. Qed.

Lemma ws_res_set_none ws : ws_res_set ws (w_res ws) = ws.
Proof. by destruct ws. Qed.

(** THE EXCLUSIVE READ, at the run level.  It takes the TIMESTAMP COLUMN
    [ts] (not the label's [(t, v)] pairs), exactly as [load_post_run_d]
    does — the reservation banks only timestamps, which is all
    [WeakPromise.excl_ok_ts] consumes, and taking the column keeps the
    function usable by a replay that remaps timestamps
    ([WeakRobustProv.aev_post]).  [rv_view] is the read half's own banked
    post-view [ldv_of], which the conditional write's [fulfil_vpre] must
    dominate (deviation D-2). *)
Definition exload_post_run_d (ws : wstate) (aq : bool) (vaddr : nat)
    (base : Z) (ts : list nat) : wstate :=
  ws_res_set (load_post_run_d ws aq vaddr base ts)
    (Some (WResv base ts (ldv_of ws aq vaddr base ts))).

Lemma exload_post_run_d_res ws aq vaddr base ts :
  w_res (exload_post_run_d ws aq vaddr base ts)
  = Some (WResv base ts (ldv_of ws aq vaddr base ts)).
Proof. done. Qed.

(** *** WHAT EACH ACCESS DOES TO [w_res], AS AN EQUATION

    The per-byte clears ([load_post_at], [store_post_d]) mean an access
    clears the reservation exactly when it has AT LEAST ONE BYTE; a
    zero-width run folds nothing and leaves [w_res] alone.  Both facts are
    needed by the T2 replay ([WeakRobustProv.aevs_post_res]), which must
    show the replayed fold and the recorded one take the SAME branch — they
    do, because the two differ only in the timestamps, never in the length. *)
Lemma ws_init_res : w_res ws_init = None.
Proof. done. Qed.

Lemma load_post_bytes_d_res ws aq vaddr ats :
  ats ≠ [] → w_res (load_post_bytes_d ws aq vaddr ats) = None.
Proof.
  induction ats as [|a ats _] using rev_ind; [done|].
  intros _. by rewrite /load_post_bytes_d foldl_app.
Qed.

Lemma store_post_bytes_d_res ws rl vf as_ t :
  as_ ≠ [] → w_res (store_post_bytes_d ws rl vf as_ t) = None.
Proof.
  induction as_ as [|a as_ _] using rev_ind; [done|].
  intros _. by rewrite /store_post_bytes_d foldl_app.
Qed.

Lemma load_post_run_d_res ws aq vaddr base ts :
  w_res (load_post_run_d ws aq vaddr base ts)
  = match ts with [] => w_res ws | _ :: _ => None end.
Proof.
  rewrite /load_post_run_d /ctrl_post /=.
  destruct ts as [|t ts]; [done|].
  by apply load_post_bytes_d_res.
Qed.

Lemma store_post_run_d_res ws rl vaddr vdata base n t :
  w_res (store_post_run_d ws rl vaddr vdata base n t)
  = match n with 0%nat => w_res ws | S _ => None end.
Proof.
  rewrite /store_post_run_d /ctrl_post /=.
  destruct n as [|n]; [done|].
  by apply store_post_bytes_d_res.
Qed.

Lemma fence_post_res ws pr pw sr sw :
  w_res (fence_post ws pr pw sr sw)
  = if (pr || pw || sr || sw)%bool then None else w_res ws.
Proof. done. Qed.

(** THE RESERVATION'S BANKED VIEW as a TOTAL function of the state — the
    form a fulfil-pre-view function can consume without an existential
    ([WeakRobustAcyc.fulfil_vext]).  [0] with no reservation, which is the
    neutral element of the join it enters. *)
Definition res_view (ws : wstate) : nat :=
  match w_res ws with Some R => rv_view R | None => 0%nat end.

Lemma res_view_some ws R : w_res ws = Some R → res_view ws = rv_view R.
Proof. rewrite /res_view. by move=> ->. Qed.


(* ------------------------------------------------------------------ *)
(** ** Monotonicity: every step function only raises views *)

(** NOTE [w_relp] is NOT ordered: it TOGGLES (set by a fence, cleared by the
    next store), so there is no conjunct for it.  [w_pub] only ever grows.

    THE D2 FINDING (deps design §2.1, correcting the stage brief).  TWO of
    the three new components are NOT monotone either, so they get no conjunct:

      - [w_ldv] is RESET by [instr_post] ([LInstr], every instruction start);
      - [w_regv] is ASSIGNED by [regw_post] ([LRegW rd srcs]) — PARM's
        [step_assign] OVERWRITES [rmap[lhs]], so a register loaded from a
        dependency-free expression LOSES the view it had.  A pointwise-[≤]
        conjunct for [w_regv] would therefore be FALSE of the machine: the
        program [r1 := ld x; r1 := 0] lowers [regv _ r1] from the load's
        post-view to [0].  Monotonicity of the register views is not merely
        unproven, it is refuted, and the stage brief's "regv-pointwise"
        conjunct is dropped for that reason.

    [w_vcap] IS monotone (both [load_post_at_d] and [store_post_d] JOIN into
    it, and [ctrl_post] joins) and it IS a memory-ordering floor — it enters
    [WeakPromise.fulfil_vpre] — so it is the one new conjunct.

    THE TWO RMW-SPLIT COMPONENTS JOIN THE SAME NON-MONOTONE CLUB, for the
    same reason: [w_res] is SET by an exclusive read (superseding a previous
    reservation) and CLEARED by a store fulfil / [LInstr], and [w_tbank] is
    REBANKED per access.  Neither gets a conjunct here; both ARE in
    [ws_bounded]. *)
Definition ws_le (w1 w2 : wstate) : Prop :=
  (∀ a, (coh w1 a ≤ coh w2 a)%nat) ∧
  (w_vrOld w1 ≤ w_vrOld w2)%nat ∧ (w_vwOld w1 ≤ w_vwOld w2)%nat ∧
  (w_vrNew w1 ≤ w_vrNew w2)%nat ∧ (w_vwNew w1 ≤ w_vwNew w2)%nat ∧
  (w_vRel  w1 ≤ w_vRel  w2)%nat ∧ (w_pub w1 ≤ w_pub w2)%nat ∧
  (w_vcap  w1 ≤ w_vcap  w2)%nat.

Global Instance ws_le_refl : Reflexive ws_le.
Proof. intros w. rewrite /ws_le. split_and!; auto with lia. Qed.

Global Instance ws_le_trans : Transitive ws_le.
Proof.
  intros w1 w2 w3 (?&?&?&?&?&?&?) (?&?&?&?&?&?&?).
  rewrite /ws_le; split_and!; try lia. intros a. etrans; eauto.
Qed.

(** The projections.  (Lifted from [WeakAxiomatic]/[WeakRobustAcyc], which
    proved them locally while this file was frozen.) *)
Lemma ws_le_coh w1 w2 a : ws_le w1 w2 → (coh w1 a ≤ coh w2 a)%nat.
Proof. by intros (H & _). Qed.

Lemma ws_le_vrOld w1 w2 : ws_le w1 w2 → (w_vrOld w1 ≤ w_vrOld w2)%nat.
Proof. by intros (_ & ? & _). Qed.

Lemma ws_le_vwOld w1 w2 : ws_le w1 w2 → (w_vwOld w1 ≤ w_vwOld w2)%nat.
Proof. by intros (_ & _ & ? & _). Qed.

Lemma ws_le_vrNew w1 w2 : ws_le w1 w2 → (w_vrNew w1 ≤ w_vrNew w2)%nat.
Proof. by intros (_ & _ & _ & ? & _). Qed.

Lemma ws_le_vwNew w1 w2 : ws_le w1 w2 → (w_vwNew w1 ≤ w_vwNew w2)%nat.
Proof. by intros (_ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_vRel w1 w2 : ws_le w1 w2 → (w_vRel w1 ≤ w_vRel w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_vcap w1 w2 : ws_le w1 w2 → (w_vcap w1 ≤ w_vcap w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & _ & _ & ?). Qed.

Lemma ws_le_pub w1 w2 : ws_le w1 w2 → (w_pub w1 ≤ w_pub w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & _ & ? & _). Qed.

(** [ctrl_post] only RAISES the control view — stated here (rather than with
    the other dependency-only effects below) because every run-level wrapper
    ends in one, so the run-level monotonicity facts need it. *)
Lemma ctrl_post_le ws v : ws_le ws (ctrl_post ws v).
Proof. rewrite /ws_le /ctrl_post /=. split_and!; auto with lia. Qed.

(** [ws_le_nc] — [ws_le] MINUS the [w_vcap] conjunct ("no control view").

    W-TV's consumption (see [load_post_run_d]) made [w_vcap] the one monotone
    component an ERASURE cannot relate: [WeakErase]'s erased run maps
    [LInstr] to [LSilent], so it never resets [w_tbank], and its stale bank
    feeds a [w_vcap] that OVERTAKES the instance's at the next access.
    [WeakErase.er_ws] therefore runs on this relation.  It costs no consumer:
    the pf fragment has NO [fulfil_ok] at all, so the whole fulfil pre-view —
    [w_vcap], [w_vwNew], [rv_view] — never appears in a side condition
    there. *)
Definition ws_le_nc (w1 w2 : wstate) : Prop :=
  (∀ a, (coh w1 a ≤ coh w2 a)%nat) ∧
  (w_vrOld w1 ≤ w_vrOld w2)%nat ∧ (w_vwOld w1 ≤ w_vwOld w2)%nat ∧
  (w_vrNew w1 ≤ w_vrNew w2)%nat ∧ (w_vwNew w1 ≤ w_vwNew w2)%nat ∧
  (w_vRel  w1 ≤ w_vRel  w2)%nat ∧ (w_pub w1 ≤ w_pub w2)%nat.

Global Instance ws_le_nc_refl : Reflexive ws_le_nc.
Proof. intros w. rewrite /ws_le_nc. split_and!; auto with lia. Qed.

Global Instance ws_le_nc_trans : Transitive ws_le_nc.
Proof.
  intros w1 w2 w3 (?&?&?&?&?&?&?) (?&?&?&?&?&?&?).
  rewrite /ws_le_nc; split_and!; try lia. intros a. etrans; eauto.
Qed.

Lemma ws_le_ws_le_nc w1 w2 : ws_le w1 w2 → ws_le_nc w1 w2.
Proof. by intros (?&?&?&?&?&?&?&?). Qed.

Lemma ws_le_nc_coh w1 w2 a : ws_le_nc w1 w2 → (coh w1 a ≤ coh w2 a)%nat.
Proof. by intros (H & _). Qed.

Lemma ws_le_nc_vrOld w1 w2 : ws_le_nc w1 w2 → (w_vrOld w1 ≤ w_vrOld w2)%nat.
Proof. by intros (_ & ? & _). Qed.

Lemma ws_le_nc_vwOld w1 w2 : ws_le_nc w1 w2 → (w_vwOld w1 ≤ w_vwOld w2)%nat.
Proof. by intros (_ & _ & ? & _). Qed.

Lemma ws_le_nc_vrNew w1 w2 : ws_le_nc w1 w2 → (w_vrNew w1 ≤ w_vrNew w2)%nat.
Proof. by intros (_ & _ & _ & ? & _). Qed.

Lemma ws_le_nc_vwNew w1 w2 : ws_le_nc w1 w2 → (w_vwNew w1 ≤ w_vwNew w2)%nat.
Proof. by intros (_ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_nc_vRel w1 w2 : ws_le_nc w1 w2 → (w_vRel w1 ≤ w_vRel w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_nc_pub w1 w2 : ws_le_nc w1 w2 → (w_pub w1 ≤ w_pub w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & _ & ?). Qed.

Lemma ctrl_post_mono w1 w2 v1 v2 :
  ws_le w1 w2 → (v1 ≤ v2)%nat → ws_le (ctrl_post w1 v1) (ctrl_post w2 v2).
Proof.
  intros Hle Hv. rewrite /ws_le /ctrl_post /=.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HR & Hpub & Hvc).
  split_and!; try lia. intros a. apply Hcoh.
Qed.

Lemma load_post_at_le ws aq vpre a t : ws_le ws (load_post_at ws aq vpre a t).
Proof.
  rewrite /ws_le /load_post_at /=. split_and!; try (destruct aq; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. lia.
  - rewrite coh_upd_ne //.
Qed.

Lemma load_post_le ws aq a t : ws_le ws (load_post ws aq a t).
Proof. apply load_post_at_le. Qed.

Lemma store_post_le ws rl a t : ws_le ws (store_post ws rl a t).
Proof.
  rewrite /ws_le /store_post /=.
  split_and!; try (destruct rl, (w_relp ws); simpl; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. lia.
  - rewrite coh_upd_ne //.
Qed.

Lemma fence_post_le ws pr pw sr sw : ws_le ws (fence_post ws pr pw sr sw).
Proof.
  rewrite /ws_le /fence_post /=.
  split_and!; try (destruct sr; destruct sw; lia).
  intros a. apply Nat.le_refl.
Qed.

(** ... and so do the multi-byte folds, which is what the interpreter's
    read/write arms actually build ([WeakInterp.wrun_ws_le]). *)
Lemma load_post_fold_le aq vpre ats ws :
  ws_le ws (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats).
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws; [reflexivity|].
  etrans; [apply load_post_at_le|apply IH].
Qed.

Lemma load_post_bytes_le ws aq ats : ws_le ws (load_post_bytes ws aq ats).
Proof. apply load_post_fold_le. Qed.

Lemma load_post_run_le ws aq base ts : ws_le ws (load_post_run ws aq base ts).
Proof.
  rewrite /load_post_run. etrans; [apply load_post_bytes_le|apply ctrl_post_le].
Qed.

Lemma store_post_fold_le rl t as_ ws :
  ws_le ws (foldl (λ w a, store_post w rl a t) ws as_).
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [reflexivity|].
  etrans; [apply store_post_le|apply IH].
Qed.

Lemma store_post_bytes_le ws rl as_ t : ws_le ws (store_post_bytes ws rl as_ t).
Proof. apply store_post_fold_le. Qed.

Lemma store_post_run_le ws rl base n t : ws_le ws (store_post_run ws rl base n t).
Proof.
  rewrite /store_post_run.
  etrans; [apply store_post_bytes_le|apply ctrl_post_le].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The individual view facts the litmus proofs consume *)

Lemma load_vpre_vrNew ws aq : (w_vrNew ws ≤ load_vpre ws aq)%nat.
Proof. rewrite /load_vpre. lia. Qed.

(** The read floor is the FORWARDED view, not the timestamp: a load that reads
    back the agent's own store gains only the view that store banked.  The
    [_nofwd] corollaries are what a consumer with an empty forward bank (any
    agent that has not stored to [a]) uses, and are the M0 statements. *)
Lemma load_post_at_vrOld ws aq vpre a t :
  (fwd_view ws aq a t ≤ w_vrOld (load_post_at ws aq vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma load_post_vrOld ws aq a t :
  (fwd_view ws aq a t ≤ w_vrOld (load_post ws aq a t))%nat.
Proof. apply load_post_at_vrOld. Qed.

Lemma load_post_at_vrOld_nofwd ws aq vpre a t :
  w_fwd ws = ∅ → (t ≤ w_vrOld (load_post_at ws aq vpre a t))%nat.
Proof.
  intros H. rewrite -{1}(fwd_view_empty ws aq a t H). apply load_post_at_vrOld.
Qed.

Lemma load_post_vrOld_nofwd ws aq a t :
  w_fwd ws = ∅ → (t ≤ w_vrOld (load_post ws aq a t))%nat.
Proof. apply load_post_at_vrOld_nofwd. Qed.

(** No step function ever CHANGES the bank except [store_post], which is what
    lets "this agent has never stored to [a]" be an invariant. *)
Lemma load_post_at_fwd ws aq vpre a t :
  w_fwd (load_post_at ws aq vpre a t) = w_fwd ws.
Proof. done. Qed.

Lemma load_post_fwd ws aq a t : w_fwd (load_post ws aq a t) = w_fwd ws.
Proof. done. Qed.

Lemma fence_post_fwd ws pr pw sr sw :
  w_fwd (fence_post ws pr pw sr sw) = w_fwd ws.
Proof. done. Qed.

Lemma load_post_fold_fwd aq vpre ats ws :
  w_fwd (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) = w_fwd ws.
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws; [done|].
  by rewrite /= IH load_post_at_fwd.
Qed.

Lemma load_post_bytes_fwd ws aq ats :
  w_fwd (load_post_bytes ws aq ats) = w_fwd ws.
Proof. apply load_post_fold_fwd. Qed.

Lemma load_post_run_fwd ws aq base ts :
  w_fwd (load_post_run ws aq base ts) = w_fwd ws.
Proof. rewrite /load_post_run ctrl_post_fwd. apply load_post_bytes_fwd. Qed.

(** THE MULTI-BYTE READ GAIN.  [load_post_vrOld_nofwd] says a single
    non-forwarded byte read of timestamp [t] leaves [t ≤ w_vrOld]; this is the
    same fact for the FOLD the interpreter actually builds
    ([WeakInterp.wread_post]), and it is what turns "the load returned byte
    [b]" into "the timestamp [b] came from is covered by my read floor" — the
    reader half of every fence-mediated handoff.

    The side condition is per-BYTE ([w_fwd ws !! a = None], "this hart has not
    stored to that byte"), not the global [w_fwd ws = ∅] the M0 corollary
    used: a hart that has stored elsewhere still reads a foreign flag
    unforwarded. *)
Lemma load_post_fold_vrOld aq vpre ats ws a t :
  (a, t) ∈ ats → w_fwd ws !! a = None →
  (t ≤ w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws Hin Hfwd.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin].
  - (* the head IS our byte: the step raises [w_vrOld] past [t], the rest of
       the fold only raises it further *)
    simpl.
    etrans; [|apply (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t))].
    rewrite /load_post_at /= (fwd_view_miss ws aq a t Hfwd). lia.
  - apply IH; [exact Hin|]. by rewrite load_post_at_fwd.
Qed.

Lemma load_post_bytes_vrOld ws aq ats a t :
  (a, t) ∈ ats → w_fwd ws !! a = None →
  (t ≤ w_vrOld (load_post_bytes ws aq ats))%nat.
Proof. apply load_post_fold_vrOld. Qed.

Lemma load_post_run_vrOld ws aq base ts j :
  (j < length ts)%nat → w_fwd ws !! (base + Z.of_nat j)%Z = None →
  (ts !!! j ≤ w_vrOld (load_post_run ws aq base ts))%nat.
Proof.
  intros Hj Hfwd. rewrite /load_post_run ctrl_post_vrOld.
  apply (load_post_bytes_vrOld _ _ _ (base + Z.of_nat j)%Z);
    [|exact Hfwd].
  apply elem_of_list_lookup_2 with j.
  destruct (lookup_lt_is_Some_2 ts j Hj) as [t Ht].
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht /=.
  by rewrite (list_lookup_total_correct ts j t Ht).
Qed.

Lemma load_post_at_coh ws aq vpre a t :
  (t ≤ coh (load_post_at ws aq vpre a t) a)%nat.
Proof. rewrite /load_post_at coh_upd_eq. lia. Qed.

Lemma load_post_coh ws aq a t : (t ≤ coh (load_post ws aq a t) a)%nat.
Proof. apply load_post_at_coh. Qed.

(** An ACQUIRE load raises the read AND write pre-view floors — this is what
    makes [MP+amoswap.aq]-style reader-side ordering work with no fence. *)
Lemma load_post_at_vrNew_aq ws vpre a t :
  (t ≤ w_vrNew (load_post_at ws true vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma load_post_vrNew_aq ws a t : (t ≤ w_vrNew (load_post ws true a t))%nat.
Proof. apply load_post_at_vrNew_aq. Qed.

Lemma load_post_at_vwNew_aq ws vpre a t :
  (t ≤ w_vwNew (load_post_at ws true vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma store_post_coh ws rl a t : (t ≤ coh (store_post ws rl a t) a)%nat.
Proof. rewrite /store_post coh_upd_eq. lia. Qed.

Lemma store_post_vwOld ws rl a t : (t ≤ w_vwOld (store_post ws rl a t))%nat.
Proof. rewrite /store_post /=. lia. Qed.

Lemma store_post_vRel_rl ws a t : (t ≤ w_vRel (store_post ws true a t))%nat.
Proof. rewrite /store_post /=. lia. Qed.

(** A succ-R fence with pred-R delivers the past loads' floor to future loads.
    (The pred-W half is the one that constrains nothing in a promise-free
    machine — see the design doc's FENCE note.) *)
Lemma fence_post_vrNew_r ws pw sw :
  (w_vrOld ws ≤ w_vrNew (fence_post ws true pw true sw))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vrNew_w ws pr sw :
  (w_vwOld ws ≤ w_vrNew (fence_post ws pr true true sw))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vwNew_r ws pw sr :
  (w_vrOld ws ≤ w_vwNew (fence_post ws true pw sr true))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vwNew_w ws pr sr :
  (w_vwOld ws ≤ w_vwNew (fence_post ws pr true sr true))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Own-write read-back *)

(** THE COLLAPSE LEMMA — the pure heart of the M2 load rule.  If [t] is the
    LATEST write to [a] and the reader's FLOOR (its load pre-view joined with
    its coherence floor for [a]) already covers [t], then [t] is the ONLY
    admissible timestamp: the ∀-over-oracles quantifier of a weak read
    collapses to a single value.

    The floor premise is deliberately stated at [Nat.max vpre (coh ws a)] —
    exactly [readable]'s own window — because the floor the vProp layer owns
    is the hart's index [w_vrNew ⊔ coh(a)], not [coh(a)] alone. *)
Lemma readable_latest_pin img log ws vpre a t t' :
  latest img log a t →
  (t ≤ Nat.max vpre (coh ws a))%nat →
  readable img log ws vpre a t' →
  t' = t.
Proof.
  intros [Ht Htop] Hfloor [Ht' Hn'].
  destruct (decide (t' = t)) as [->|Hne]; [done|exfalso].
  destruct (decide (t' < t)%nat) as [Hlt|Hge].
  - (* [t] itself is a write in [t']'s forbidden window *)
    apply Hn'. eapply (writes_in_log_byte img). exists t.
    split_and!; [lia|lia|done].
  - (* [t'] is a write strictly above [t], contradicting latest-ness *)
    apply Htop. eapply (writes_in_log_byte img). exists t'.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht').
Qed.

(** If [t] writes [a], the agent's coherence floor already covers [t], and no
    LATER timestamp in the whole log writes [a], then [t] is the ONLY readable
    timestamp for [a] — the reader is pinned to the top message.  The
    [vpre = 0] instance of [readable_latest_pin]. *)
Lemma readable_top_unique img log ws vpre a t t' :
  is_Some (log_byte img log t a) →
  (t ≤ coh ws a)%nat →
  ¬ writes_in log a t (length log) →
  readable img log ws vpre a t' →
  t' = t.
Proof.
  intros Ht Hcoh Htop Hr.
  eapply readable_latest_pin; [split; [exact Ht|exact Htop]| |exact Hr]. lia.
Qed.

(** The store case: right after a store, the storer can only read back its own
    message.  The store lands at the log's fresh top [S (length log)], and
    [store_post] pushes [coh(a)] up to it. *)
Lemma store_fresh_top_unique img log ws rl m a vpre t' :
  is_Some (msg_byte m a) →
  readable img (log ++ [m]) (store_post ws rl a (S (length log)))
           vpre a t' →
  t' = S (length log).
Proof.
  intros Hm Hr.
  eapply (readable_top_unique img (log ++ [m])); [| | |exact Hr].
  - assert (Hle : (length log ≤ length log)%nat) by lia.
    rewrite log_byte_S (lookup_app_r log [m] (length log) Hle) Nat.sub_diag /=.
    exact Hm.
  - apply store_post_coh.
  - rewrite length_app /=. intros (t & ? & ? & ?). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [ws_bounded]: every view a hart holds is a real timestamp

    THE MACHINE INVARIANT of M2b.  A [wstate] is a bundle of timestamps; the
    step functions only ever join them with timestamps drawn from the log, so
    every view a hart holds stays below the log's length.  Stated over a NAT
    bound rather than a log: the bound is then monotone ([ws_bounded_mono]),
    which is exactly what the OTHER harts need when the stepping hart appends.
    THE TIE IS ALWAYS USED AT [n = length log] — see
    [WeakInterp.wrun_ws_bounded] and [WeakGhost.weak_state_interp].

    THE FORWARD-BANK CONJUNCT IS NOT OPTIONAL.  [fwd_view] puts a BANKED view
    into a load's post-view ([load_post_at]'s [vpost]), so without a bound on
    the bank's second components [load_post_at] would not preserve
    boundedness — the banked view would flow straight into [w_vrOld]. *)

(** The reservation's own boundedness (RMW split §3): every timestamp it
    banks — the per-byte read timestamps and the banked post-view — is a
    real log position.  Vacuous when no reservation is held. *)
Definition wresv_bounded (o : option wresv) (n : nat) : Prop :=
  ∀ R, o = Some R →
    (∀ j t, rv_ts R !! j = Some t → (t ≤ n)%nat) ∧ (rv_view R ≤ n)%nat.

Lemma wresv_bounded_none n : wresv_bounded None n.
Proof. by intros ? ?. Qed.

Lemma wresv_bounded_mono o n n' :
  wresv_bounded o n → (n ≤ n')%nat → wresv_bounded o n'.
Proof.
  intros Ho Hle R HR. destruct (Ho R HR) as [Hts Hv].
  split; [|lia]. intros j t Ht. pose proof (Hts j t Ht). lia.
Qed.

Definition ws_bounded (ws : wstate) (n : nat) : Prop :=
  (w_vrOld ws ≤ n)%nat ∧ (w_vwOld ws ≤ n)%nat ∧
  (w_vrNew ws ≤ n)%nat ∧ (w_vwNew ws ≤ n)%nat ∧ (w_vRel ws ≤ n)%nat ∧
  (w_pub ws ≤ n)%nat ∧
  (∀ a, (coh ws a ≤ n)%nat) ∧
  (∀ a tv, w_fwd ws !! a = Some tv → (tv.1 ≤ n)%nat ∧ (tv.2 ≤ n)%nat) ∧
  (* THE THREE D2 COMPONENTS.  All three ARE bounded (unlike [ws_le], which
     only takes [w_vcap]): boundedness is about the VALUES being real
     timestamps, and a reset or an overwrite by a smaller view preserves
     that.  [w_regv] is bounded through the TOTAL accessor [regv], which is
     [0] off the map's domain. *)
  (∀ r, (regv ws r ≤ n)%nat) ∧ (w_vcap ws ≤ n)%nat ∧ (w_ldv ws ≤ n)%nat ∧
  (* THE TWO RMW-SPLIT COMPONENTS (RMW split §3).  Both are bounded for the
     same reason as the D2 three: they hold timestamps drawn from the log.
     [w_res] is the one that MUST be here — [fulfil_vpre] has to dominate
     [rv_view] at the conditional write. *)
  wresv_bounded (w_res ws) n ∧ (w_tbank ws ≤ n)%nat.

Lemma ws_bounded_vcap ws n : ws_bounded ws n → (w_vcap ws ≤ n)%nat.
Proof. by intros (_&_&_&_&_&_&_&_&_&?&_). Qed.

Lemma ws_bounded_ldv ws n : ws_bounded ws n → (w_ldv ws ≤ n)%nat.
Proof. by intros (_&_&_&_&_&_&_&_&_&_&?&_). Qed.

Lemma ws_bounded_res ws n : ws_bounded ws n → wresv_bounded (w_res ws) n.
Proof. by intros (_&_&_&_&_&_&_&_&_&_&_&?&_). Qed.

Lemma ws_bounded_tbank ws n : ws_bounded ws n → (w_tbank ws ≤ n)%nat.
Proof. by intros (_&_&_&_&_&_&_&_&_&_&_&_&?). Qed.

Lemma ws_bounded_regv ws n r : ws_bounded ws n → (regv ws r ≤ n)%nat.
Proof. by intros (_&_&_&_&_&_&_&_&H&_). Qed.

(** A source list's view is bounded by any bound on the state — the fact the
    machine's new arms need at every [srcs_view]. *)
Lemma srcs_view_bounded ws n l : ws_bounded ws n → (srcs_view ws l ≤ n)%nat.
Proof.
  intros Hb. induction l as [|x l IH]; [simpl; lia|].
  rewrite srcs_view_cons. destruct x as [r|]; simpl.
  - pose proof (ws_bounded_regv ws n r Hb). lia.
  - pose proof (ws_bounded_ldv ws n Hb). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** D3: THE DEPENDENCY-ONLY MOVE

    The three labels [LRegW]/[LCtrl]/[LInstr] move the view state, but ONLY
    through the three dependency components — every ordering component
    ([coh], the four frontiers, [w_vRel], the forward bank, [w_pub],
    [w_relp]) is untouched, and [w_vcap] only rises.  [ws_depmove] is that
    fact as a relation.  It is what the WP tier's batched silent-node rule
    hands its caller in place of an equation: a leaf that owns [hart_ws c ws]
    and runs a stretch of pure nodes gets back [hart_ws c ws'] for some
    [ws'] with [ws_depmove ws ws'], from which it can still read off every
    ordering fact it had (in particular [coh], [w_relp] and [ws_le]). *)
Definition ws_depmove (w1 w2 : wstate) : Prop :=
  w_coh w2 = w_coh w1 ∧
  w_vrOld w2 = w_vrOld w1 ∧ w_vwOld w2 = w_vwOld w1 ∧
  w_vrNew w2 = w_vrNew w1 ∧ w_vwNew w2 = w_vwNew w1 ∧
  w_vRel w2 = w_vRel w1 ∧ w_fwd w2 = w_fwd w1 ∧
  w_pub w2 = w_pub w1 ∧ w_relp w2 = w_relp w1 ∧
  (w_vcap w1 ≤ w_vcap w2)%nat.

Global Instance ws_depmove_refl : Reflexive ws_depmove.
Proof. intros w. rewrite /ws_depmove. split_and!; auto with lia. Qed.

Global Instance ws_depmove_trans : Transitive ws_depmove.
Proof.
  intros w1 w2 w3 (?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?).
  rewrite /ws_depmove. split_and!; try congruence. lia.
Qed.

Lemma ws_depmove_coh w1 w2 a : ws_depmove w1 w2 → coh w2 a = coh w1 a.
Proof. intros (H & _). by rewrite /coh H. Qed.

Lemma ws_depmove_relp w1 w2 : ws_depmove w1 w2 → w_relp w2 = w_relp w1.
Proof. by intros (?&?&?&?&?&?&?&?&?&?). Qed.

Lemma ws_depmove_le w1 w2 : ws_depmove w1 w2 → ws_le w1 w2.
Proof.
  intros (Hc&?&?&?&?&?&?&?&?&?). rewrite /ws_le. split_and!; try lia.
  intros a. rewrite /coh Hc. lia.
Qed.

Lemma regw_post_depmove ws rd v : ws_depmove ws (regw_post ws rd v).
Proof. rewrite /ws_depmove /regw_post /=. split_and!; auto with lia. Qed.

Lemma ctrl_post_depmove ws v : ws_depmove ws (ctrl_post ws v).
Proof. rewrite /ws_depmove /ctrl_post /=. split_and!; auto with lia. Qed.

Lemma instr_post_depmove ws : ws_depmove ws (instr_post ws).
Proof. rewrite /ws_depmove /instr_post /=. split_and!; auto with lia. Qed.

Lemma ws_bounded_init n : ws_bounded ws_init n.
Proof.
  rewrite /ws_bounded. split_and!; try (simpl; lia).
  - intros a. rewrite coh_init. lia.
  - intros a tv. rewrite /ws_init /= lookup_empty. done.
  - intros r. rewrite regv_init. lia.
  - apply wresv_bounded_none.
Qed.

Lemma ws_bounded_mono ws n n' :
  ws_bounded ws n → (n ≤ n')%nat → ws_bounded ws n'.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld
          & Hres & Htb)
         Hle.
  rewrite /ws_bounded. split_and!; try lia.
  - intros a. pose proof (Hcoh a). lia.
  - intros a tv Ha. destruct (Hfwd a tv Ha). split; lia.
  - intros r. move: (Hrg r). rewrite /regv /=. lia.
  - by eapply wresv_bounded_mono.
Qed.

(** The [coh] half of every preservation proof below: an insert stays bounded
    if the inserted value is. *)
Local Lemma coh_upd_bounded ws vrO vwO vrN vwN vR fwd pb rp rg vc ld rs tb
    a v n :
  (∀ a', (coh ws a' ≤ n)%nat) → (v ≤ n)%nat →
  ∀ a', (coh {| w_coh := <[a := v]> (w_coh ws); w_vrOld := vrO; w_vwOld := vwO;
                w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
                w_pub := pb; w_relp := rp;
                w_regv := rg; w_vcap := vc; w_ldv := ld;
                w_res := rs; w_tbank := tb |} a'
         ≤ n)%nat.
Proof.
  intros Hm Hv a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. exact Hv.
  - rewrite coh_upd_ne //. apply Hm.
Qed.

Lemma load_vpre_bounded ws aq n : ws_bounded ws n → (load_vpre ws aq ≤ n)%nat.
Proof.
  intros (_ & _ & Hrn & _ & Hrel & _ & _ & _ & _).
  rewrite /load_vpre. destruct aq; lia.
Qed.

Lemma load_vpre_d_bounded ws aq vaddr n :
  ws_bounded ws n → (vaddr ≤ n)%nat → (load_vpre_d ws aq vaddr ≤ n)%nat.
Proof.
  intros Hb Hv. pose proof (load_vpre_bounded ws aq n Hb).
  rewrite /load_vpre_d. lia.
Qed.

Lemma fwd_view_bounded ws aq a t n :
  ws_bounded ws n → (t ≤ n)%nat → (fwd_view ws aq a t ≤ n)%nat.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hfwd & _) Ht. rewrite /fwd_view.
  destruct aq; [exact Ht|].
  destruct (w_fwd ws !! a) as [[tf vf]|] eqn:Hf; [|exact Ht].
  case_bool_decide; [|exact Ht].
  destruct (Hfwd a (tf, vf) Hf) as [_ Hvf]. exact Hvf.
Qed.

Lemma load_post_at_bounded ws aq vpre a t n :
  ws_bounded ws n → (vpre ≤ n)%nat → (t ≤ n)%nat →
  ws_bounded (load_post_at ws aq vpre a t) n.
Proof.
  intros Hb Hvp Ht.
  pose proof (fwd_view_bounded ws aq a t n Hb Ht) as Hfv.
  destruct Hb as (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd
                  & Hrg & Hvc & Hld & Hres & Htb).
  rewrite /ws_bounded /load_post_at /=.
  split_and!; try (destruct aq; lia).
  - apply coh_upd_bounded; [exact Hcoh|]. pose proof (Hcoh a). lia.
  - exact Hfwd.
  - exact Hrg.
  - done.
Qed.

Lemma store_post_d_bounded ws rl vf a t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat → (vf ≤ n')%nat →
  ws_bounded (store_post_d ws rl vf a t) n'.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld & Hres & Htb)
         Ht Hle Hvf.
  rewrite /ws_bounded /store_post_d /=.
  split_and!; try (destruct rl, (w_relp ws); simpl; lia).
  - apply coh_upd_bounded.
    + intros a'. pose proof (Hcoh a'). lia.
    + pose proof (Hcoh a). lia.
  - intros a' tv. destruct (decide (a' = a)) as [->|Hne].
    + rewrite lookup_insert. intros [= <-]. simpl. split; lia.
    + rewrite lookup_insert_ne //. intros Ha'.
      destruct (Hfwd a' tv Ha'). split; lia.
  - intros r. move: (Hrg r). rewrite /regv /=. lia.
  - apply wresv_bounded_none.
Qed.

Lemma store_post_bounded ws rl a t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post ws rl a t) n'.
Proof.
  intros Hb Ht Hle. rewrite -store_post_d_0.
  eapply store_post_d_bounded; [exact Hb|done|done|lia].
Qed.

Lemma fence_post_bounded ws pr pw sr sw n :
  ws_bounded ws n → ws_bounded (fence_post ws pr pw sr sw) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld & Hres & Htb).
  rewrite /ws_bounded /fence_post /=.
  split_and!; try (destruct pr, pw, sr, sw; simpl; lia).
  - exact Hcoh.
  - exact Hfwd.
  - exact Hrg.
  - destruct pr, pw, sr, sw; simpl;
      first [ apply wresv_bounded_none | exact Hres ].
Qed.

(** The three dependency-only effects preserve both orders. *)
Lemma regw_post_le ws rd v : ws_le ws (regw_post ws rd v).
Proof. rewrite /ws_le /regw_post /=. split_and!; auto with lia. Qed.

Lemma instr_post_le ws : ws_le ws (instr_post ws).
Proof. rewrite /ws_le /instr_post /=. split_and!; auto with lia. Qed.

Lemma regw_post_bounded ws rd v n :
  ws_bounded ws n → (v ≤ n)%nat → ws_bounded (regw_post ws rd v) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld & Hres & Htb)
         Hv.
  rewrite /ws_bounded /regw_post /=. split_and!; try lia.
  - exact Hcoh.
  - exact Hfwd.
  - intros r. rewrite /regv /=. destruct (decide (r = rd)) as [->|Hne].
    + rewrite lookup_insert //.
    + rewrite lookup_insert_ne //. apply (Hrg r).
  - exact Hres.
Qed.

Lemma ctrl_post_bounded ws v n :
  ws_bounded ws n → (v ≤ n)%nat → ws_bounded (ctrl_post ws v) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld & Hres & Htb)
         Hv.
  rewrite /ws_bounded /ctrl_post /=. split_and!; try lia;
    [exact Hcoh|exact Hfwd|exact Hrg|exact Hres].
Qed.

Lemma instr_post_bounded ws n : ws_bounded ws n → ws_bounded (instr_post ws) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld & Hres & Htb).
  rewrite /ws_bounded /instr_post /=. split_and!; try lia;
    [exact Hcoh|exact Hfwd|exact Hrg|apply wresv_bounded_none].
Qed.

(** ... and the multi-byte folds the interpreter's read/write arms build. *)

Local Lemma load_post_fold_bounded aq vpre n ats :
  (vpre ≤ n)%nat →
  ∀ ws, ws_bounded ws n → Forall (λ p : Z * nat, (p.2 ≤ n)%nat) ats →
    ws_bounded (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) n.
Proof.
  intros Hvp. induction ats as [|at_ l IH]; intros ws Hb Hall; [exact Hb|].
  apply Forall_cons_1 in Hall as [Hat Hl].
  simpl. apply IH; [|exact Hl]. by apply load_post_at_bounded.
Qed.

(** NOTE the pre-view: [load_post_bytes] folds [load_post_at] with the
    pre-view computed ONCE from [ws], so the bound needed on it is exactly
    [load_vpre_bounded] and there is no [vpre] premise to state. *)
Lemma load_post_bytes_bounded ws aq ats n :
  ws_bounded ws n → Forall (λ p : Z * nat, (p.2 ≤ n)%nat) ats →
  ws_bounded (load_post_bytes ws aq ats) n.
Proof.
  intros Hb Hall. rewrite /load_post_bytes.
  apply load_post_fold_bounded; [by apply load_vpre_bounded|exact Hb|exact Hall].
Qed.

Local Lemma store_post_fold_bounded rl t n' as_ :
  (t ≤ n')%nat →
  ∀ ws, ws_bounded ws n' →
    ws_bounded (foldl (λ w a, store_post w rl a t) ws as_) n'.
Proof.
  intros Ht. induction as_ as [|a l IH]; intros ws Hb; [exact Hb|].
  simpl. apply IH. by apply (store_post_bounded ws rl a t n' n').
Qed.

Lemma store_post_bytes_bounded ws rl as_ t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post_bytes ws rl as_ t) n'.
Proof.
  intros Hb Ht Hle. rewrite /store_post_bytes.
  apply store_post_fold_bounded; [exact Ht|].
  eapply ws_bounded_mono; [exact Hb|exact Hle].
Qed.

(** The contiguous-run transport: byte [j] of the access sits at
    [base + j], and only the SECOND component of the zipped pair carries a
    timestamp. *)
Local Lemma Forall_zip_seq (base : Z) (n : nat) (ts : list nat) :
  Forall (λ t, (t ≤ n)%nat) ts →
  ∀ k, Forall (λ p : Z * nat, (p.2 ≤ n)%nat)
         (zip_with (λ j t, (base + Z.of_nat j, t)) (seq k (length ts)) ts).
Proof.
  induction ts as [|t l IH]; intros Hall k; [constructor|].
  apply Forall_cons_1 in Hall as [Ht Hl].
  (* [seq k (S m) = k :: seq (S k) m] holds by [reflexivity] *)
  simpl. constructor; [exact Ht|]. by apply IH.
Qed.

Lemma load_post_run_bounded ws aq base ts n :
  ws_bounded ws n → Forall (λ t, (t ≤ n)%nat) ts →
  ws_bounded (load_post_run ws aq base ts) n.
Proof.
  intros Hb Hall. rewrite /load_post_run.
  apply ctrl_post_bounded; [|by apply ws_bounded_tbank].
  apply load_post_bytes_bounded; [exact Hb|by apply Forall_zip_seq].
Qed.

Lemma store_post_run_bounded ws rl base cnt t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post_run ws rl base cnt t) n'.
Proof.
  intros Hb Ht Hle. rewrite /store_post_run.
  apply ctrl_post_bounded;
    [|etrans; [by apply ws_bounded_tbank|exact Hle]].
  by apply (store_post_bytes_bounded ws rl _ t n n').
Qed.

(** THE PAYOFF.  The hart's own index into the log — its read floor joined
    with a byte's coherence floor, i.e. exactly [readable]'s window — is a
    real timestamp.  This is what M3's lock transfer consumes; the view-level
    restatement lives above [WeakView], not here. *)
Lemma ws_bounded_scl ws n :
  ws_bounded ws n → ∀ a, (Nat.max (w_vrNew ws) (coh ws a) ≤ n)%nat.
Proof.
  intros (_ & _ & Hrn & _ & _ & _ & Hcoh & _) a. pose proof (Hcoh a). lia.
Qed.

(* ================================================================== *)
(** ** THE W4 LIFT BATCH — fold facts the consumers used to prove locally

    Every lemma below was proved verbatim in a consumer file
    ([WeakAxiomatic], [WeakAxiomatic2], [WeakAxiomatic3], [WeakLitmusProj],
    [WeakPromiseLitmus], [WeakPromiseBridge], [WeakRobustAcyc],
    [WeakRobustGraph]) with a header explaining that it belonged here and was
    only elsewhere because this file was frozen while sibling [.vo]s were in
    flight.  They are now here, and the local copies are gone.

    Three kinds of fact about the step functions live in this file:
    MONOTONE ([ws_le]), BOUNDED ([ws_bounded]), and — the third kind, added by
    this batch — DOMINATED (an upper bound on each component in terms of the
    step's inputs, §5 of [WeakAxiomatic3]). *)

(* ------------------------------------------------------------------ *)
(** *** Singleton collapses of the run-shaped post-states

    The byte address [base + Z.of_nat 0] normalizes to [base].  The store form
    is stated at [length [v]] rather than at [1] so that it matches the
    step relations' post-states syntactically.

    THE [ctrl_post] ON THE RIGHT is W-TV's consumption (see the note at
    [load_post_run_d]): a run-level access joins the entry state's
    translation bank into [w_vcap], and the per-byte functions
    [load_post]/[store_post] do not.  At [w_tbank ws = 0] — in particular at
    [ws_init] — [ctrl_post_0] collapses it away. *)

Lemma load_post_run_single ws aq base t :
  load_post_run ws aq base [t]
  = ctrl_post (load_post ws aq base t) (w_tbank ws).
Proof. rewrite /load_post_run /load_post_bytes /load_post /= Z.add_0_r //. Qed.

Lemma store_post_run_single ws rl base (v : bv 8) t :
  store_post_run ws rl base (length [v]) t
  = ctrl_post (store_post ws rl base t) (w_tbank ws).
Proof. rewrite /store_post_run /store_post_bytes /= Z.add_0_r //. Qed.

(* ------------------------------------------------------------------ *)
(** *** A message writes only inside its own byte range *)

Lemma msg_byte_range m a :
  is_Some (msg_byte m a) →
  ∃ j : nat, (j < length (wm_data m))%nat ∧ a = wm_pa m + Z.of_nat j.
Proof.
  rewrite /msg_byte. case_bool_decide as Hle; [|by intros []].
  intros Hs. exists (Z.to_nat (a - wm_pa m)). split.
  - by eapply lookup_lt_is_Some_1.
  - lia.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The missing [coh] / [w_vwOld] / forwarded-[w_vrOld] fold instances *)

Local Lemma load_post_fold_coh aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ coh (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) a)%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_coh ws aq vpre a t)|].
  apply ws_le_coh, (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t)).
Qed.

Lemma load_post_run_coh ws aq base ts (j : nat) t :
  ts !! j = Some t →
  (t ≤ coh (load_post_run ws aq base ts) (base + Z.of_nat j))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run ctrl_post_coh /load_post_bytes. apply load_post_fold_coh.
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Local Lemma store_post_fold_coh rl t as_ ws a :
  a ∈ as_ → (t ≤ coh (foldl (λ w a, store_post w rl a t) ws as_) a)%nat.
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (store_post_coh ws rl a t)|].
  apply ws_le_coh, (store_post_fold_le rl t l (store_post ws rl a t)).
Qed.

Lemma store_post_run_coh ws rl base n t (j : nat) :
  (j < n)%nat → (t ≤ coh (store_post_run ws rl base n t) (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite /store_post_run ctrl_post_coh /store_post_bytes.
  apply store_post_fold_coh, elem_of_list_In, in_map_iff.
  exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

Local Lemma store_post_fold_vwOld rl t as_ ws :
  as_ ≠ [] → (t ≤ w_vwOld (foldl (λ w a, store_post w rl a t) ws as_))%nat.
Proof.
  destruct as_ as [|a l]; [done|]. intros _. simpl.
  etrans; [apply (store_post_vwOld ws rl a t)|].
  apply ws_le_vwOld, (store_post_fold_le rl t l (store_post ws rl a t)).
Qed.

Lemma store_post_run_vwOld ws rl base n t :
  (0 < n)%nat → (t ≤ w_vwOld (store_post_run ws rl base n t))%nat.
Proof.
  intros Hn. rewrite /store_post_run ctrl_post_vwOld /store_post_bytes.
  apply store_post_fold_vwOld. by destruct n; [lia|].
Qed.

(** The generalized [load_post_run_vrOld]: what the read floor gains is the
    FORWARDED view, so the side condition needed is "this byte's read was not
    forwarded", not the stronger "this agent never stored to it". *)
Local Lemma load_post_fold_vrOld' aq vpre ats ws a t :
  (a, t) ∈ ats → fwd_view ws aq a t = t →
  (t ≤ w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin Hfv.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin].
  - simpl. etrans; [|apply ws_le_vrOld,
      (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t))].
    rewrite /load_post_at /= Hfv. lia.
  - apply IH; [exact Hin|]. by rewrite /fwd_view load_post_at_fwd.
Qed.

Lemma load_post_run_vrOld' ws aq base ts (j : nat) t :
  ts !! j = Some t → fwd_view ws aq (base + Z.of_nat j) t = t →
  (t ≤ w_vrOld (load_post_run ws aq base ts))%nat.
Proof.
  intros Ht Hfv. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run ctrl_post_vrOld /load_post_bytes.
  apply (load_post_fold_vrOld' _ _ _ _ (base + Z.of_nat j) t); [|exact Hfv].
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The acquire-load fold instances

    An acquire load pushes every byte's timestamp — and its own pre-view —
    into both [w_vrNew] and [w_vwNew]. *)

Local Lemma load_post_fold_vrNew_aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ w_vrNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_vrNew_aq ws vpre a t)|].
  apply ws_le_vrNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre a t)).
Qed.

Lemma load_post_run_vrNew_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vrNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run ctrl_post_vrNew /load_post_bytes.
  apply (load_post_fold_vrNew_aq _ _ _ (base + Z.of_nat j) t).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Local Lemma load_post_fold_vwNew_aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ w_vwNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_vwNew_aq ws vpre a t)|].
  apply ws_le_vwNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre a t)).
Qed.

Lemma load_post_run_vwNew_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vwNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run ctrl_post_vwNew /load_post_bytes.
  apply (load_post_fold_vwNew_aq _ _ _ (base + Z.of_nat j) t).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(** An ACQUIRE load's own PRE-VIEW lands under its post-[w_vrNew] — needed
    because [load_vpre] of an acquire joins [w_vRel], which is NOT below
    [w_vrNew] before the step. *)
Local Lemma load_post_fold_vrNew_aq_vpre vpre ats ws p :
  p ∈ ats →
  (vpre ≤ w_vrNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|q l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [|apply ws_le_vrNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre p.1 p.2))].
  rewrite /load_post_at /=. lia.
Qed.

Lemma load_post_run_vrNew_aq_vpre ws base ts (j : nat) t :
  ts !! j = Some t →
  (load_vpre ws true ≤ w_vrNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run ctrl_post_vrNew /load_post_bytes.
  apply (load_post_fold_vrNew_aq_vpre _ _ _ (base + Z.of_nat j, t)).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The forward-bank inversion for a store fold *)

Local Lemma store_post_fold_fwd rl t as_ ws a tf vf :
  w_fwd (foldl (λ w a, store_post w rl a t) ws as_) !! a = Some (tf, vf) →
  tf = t ∨ w_fwd ws !! a = Some (tf, vf).
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hlk; [by right|].
  destruct (IH _ Hlk) as [->|Hlk']; [by left|].
  rewrite /store_post /= in Hlk'.
  destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert in Hlk'. simplify_eq. by left.
  - rewrite lookup_insert_ne in Hlk'; [done|]. by right.
Qed.

Lemma store_post_run_fwd_inv ws rl base n t a tf vf :
  w_fwd (store_post_run ws rl base n t) !! a = Some (tf, vf) →
  tf = t ∨ w_fwd ws !! a = Some (tf, vf).
Proof.
  rewrite /store_post_run ctrl_post_fwd /store_post_bytes.
  apply store_post_fold_fwd.
Qed.

(* ================================================================== *)
(** ** DOMINATION: upper bounds for the step functions

    The THIRD kind of step-function fact (§5 of [WeakAxiomatic3]): after this
    step, each component is a join of the old component, the pre-view, and the
    timestamps the step touched.  Stated once for an arbitrary predicate
    closed under [Nat.max] and holding at 0, because the consumers instantiate
    it at several different predicates. *)

Definition maxcl (P : nat → Prop) : Prop :=
  P 0%nat ∧ ∀ n1 n2, P n1 → P n2 → P (Nat.max n1 n2).

Lemma maxcl_0 P : maxcl P → P 0%nat.
Proof. by intros [? _]. Qed.
Lemma maxcl_max P n1 n2 : maxcl P → P n1 → P n2 → P (Nat.max n1 n2).
Proof. intros [_ H]. exact (H n1 n2). Qed.

(** *** Pointwise shapes of the two per-byte updates *)

Lemma coh_load_post_at_eq ws aq vpre a t :
  coh (load_post_at ws aq vpre a t) a =
  Nat.max (coh ws a) (Nat.max (Nat.max vpre (fwd_view ws aq a t)) t).
Proof. rewrite /load_post_at coh_upd_eq //. Qed.

Lemma coh_load_post_at_ne ws aq vpre a t a' :
  a' ≠ a → coh (load_post_at ws aq vpre a t) a' = coh ws a'.
Proof. intros Hne. rewrite /load_post_at coh_upd_ne // /coh //. Qed.

Lemma coh_store_post_eq ws rl a t :
  coh (store_post ws rl a t) a = Nat.max (coh ws a) t.
Proof. rewrite /store_post coh_upd_eq //. Qed.

Lemma coh_store_post_ne ws rl a t a' :
  a' ≠ a → coh (store_post ws rl a t) a' = coh ws a'.
Proof. intros Hne. rewrite /store_post coh_upd_ne // /coh //. Qed.

(** *** The load fold: the components it does not touch *)

Lemma load_fold_vwOld aq vpre ats ws :
  w_vwOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_vwOld ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma load_fold_vRel aq vpre ats ws :
  w_vRel (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_vRel ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma load_fold_vrNew_plain vpre ats ws :
  w_vrNew (foldl (λ w at_, load_post_at w false vpre at_.1 at_.2) ws ats)
  = w_vrNew ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

(** *** The load fold: upper bounds, under "no byte of this load is
    forwarded". *)

Lemma load_fold_coh P aq vpre ats ws a :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (coh ws a) → P vpre → (∀ p, p ∈ ats → p.1 = a → P p.2) →
  P (coh (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) a).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - destruct (decide (a = p.1)) as [Heq|Hne]; last first.
    { rewrite (coh_load_post_at_ne _ _ _ _ _ _ Hne). exact Hc. }
    assert (Hpa : P p.2).
    { apply (Hts p); [apply elem_of_cons; by left|by rewrite -Heq]. }
    rewrite Heq coh_load_post_at_eq (Hfv p ltac:(apply elem_of_cons; by left)).
    apply maxcl_max; [done|rewrite -Heq; exact Hc|].
    apply maxcl_max; [done| |exact Hpa].
    apply maxcl_max; [done|exact Hv|exact Hpa].
  - exact Hv.
  - intros q Hq Hqa. apply (Hts q); [apply elem_of_cons; by right|exact Hqa].
Qed.

Lemma load_fold_vrOld P aq vpre ats ws :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (w_vrOld ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - rewrite /load_post_at /= (Hfv p ltac:(apply elem_of_cons; by left)).
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

Lemma load_fold_vrNew P aq vpre ats ws :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (w_vrNew ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrNew (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - rewrite /load_post_at /= (Hfv p ltac:(apply elem_of_cons; by left)).
    destruct aq; [|exact Hc].
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

(** *** The store fold *)

Lemma store_fold_vrOld rl t as_ ws :
  w_vrOld (foldl (λ w a, store_post w rl a t) ws as_) = w_vrOld ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vrNew rl t as_ ws :
  w_vrNew (foldl (λ w a, store_post w rl a t) ws as_) = w_vrNew ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vRel_norl t as_ ws :
  w_vRel (foldl (λ w a, store_post w false a t) ws as_) = w_vRel ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vwOld P rl t as_ ws :
  maxcl P → P (w_vwOld ws) → P t →
  P (w_vwOld (foldl (λ w a, store_post w rl a t) ws as_)).
Proof.
  intros Hcl. revert ws. induction as_ as [|a l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH; [|exact Ht]. rewrite /store_post /=. by apply maxcl_max.
Qed.

Lemma store_fold_coh P rl t as_ ws a :
  maxcl P → P (coh ws a) → (a ∈ as_ → P t) →
  P (coh (foldl (λ w a, store_post w rl a t) ws as_) a).
Proof.
  intros Hcl. revert ws. induction as_ as [|b l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH.
  - destruct (decide (a = b)) as [->|Hne]; last first.
    { rewrite (coh_store_post_ne _ _ _ _ _ Hne). exact Hc. }
    rewrite coh_store_post_eq.
    apply maxcl_max; [done|exact Hc|apply Ht, elem_of_cons; by left].
  - intros Hin. apply Ht, elem_of_cons; by right.
Qed.

(** *** The fence *)

Lemma fence_post_vrNew_pred P ws pr pw sr sw :
  maxcl P → P (w_vrNew ws) →
  (pr = true → sr = true → P (w_vrOld ws)) →
  (pw = true → sr = true → P (w_vwOld ws)) →
  P (w_vrNew (fence_post ws pr pw sr sw)).
Proof.
  intros Hcl Hn Hro Hwo. rewrite /fence_post /=.
  destruct sr; [|exact Hn].
  apply maxcl_max; [done|exact Hn|].
  apply maxcl_max; [done| |].
  - destruct pr; [by apply Hro|by apply maxcl_0].
  - destruct pw; [by apply Hwo|by apply maxcl_0].
Qed.

(* ================================================================== *)
(** ** THE DEPENDENCY-CARRYING RUN FACTS (D2)

    Everything the machines ([WeakPromise.wpstep],
    [WeakPromiseBridge.wp_pf_step]) and the replay need about the [_d]
    step functions.  The load side is nearly free: [vaddr] enters
    [load_post_bytes_d] only through the PRE-VIEW, and every per-byte fold
    lemma above already quantifies over an arbitrary [vpre]; only the
    run-level [ctrl_post] wrapper is new.  The store side needs the fold
    lemmas restated at [store_post_d], because the banked forward view sits
    INSIDE the fold. *)

(** *** The load run

    ([ctrl_post]'s field equations live next to its definition, above.) *)

Lemma load_post_bytes_d_le ws aq vaddr ats :
  ws_le ws (load_post_bytes_d ws aq vaddr ats).
Proof. apply load_post_fold_le. Qed.

Lemma load_post_run_d_le ws aq vaddr base ts :
  ws_le ws (load_post_run_d ws aq vaddr base ts).
Proof.
  rewrite /load_post_run_d. etrans; [apply load_post_bytes_d_le|apply ctrl_post_le].
Qed.

Lemma load_post_bytes_d_bounded ws aq vaddr ats n :
  ws_bounded ws n → (vaddr ≤ n)%nat →
  Forall (λ p : Z * nat, (p.2 ≤ n)%nat) ats →
  ws_bounded (load_post_bytes_d ws aq vaddr ats) n.
Proof.
  intros Hb Hva Hall. apply load_post_fold_bounded; [|exact Hb|exact Hall].
  by apply load_vpre_d_bounded.
Qed.

Lemma load_post_run_d_bounded ws aq vaddr base ts n :
  ws_bounded ws n → (vaddr ≤ n)%nat → Forall (λ t, (t ≤ n)%nat) ts →
  ws_bounded (load_post_run_d ws aq vaddr base ts) n.
Proof.
  intros Hb Hva Hall. rewrite /load_post_run_d.
  apply ctrl_post_bounded;
    [|apply Nat.max_lub; [exact Hva|by apply ws_bounded_tbank]].
  apply load_post_bytes_d_bounded; [exact Hb|exact Hva|].
  rewrite /load_run_ats Forall_lookup. intros j p Hp.
  rewrite lookup_zip_with in Hp.
  destruct (seq 0 (length ts) !! j) as [i|] eqn:Hi; simpl in Hp; [|done].
  destruct (ts !! j) as [t|] eqn:Ht; simpl in Hp; [|done]. simplify_eq/=.
  rewrite Forall_lookup in Hall. by eapply Hall.
Qed.

Lemma load_post_run_d_fwd ws aq vaddr base ts :
  w_fwd (load_post_run_d ws aq vaddr base ts) = w_fwd ws.
Proof.
  rewrite /load_post_run_d ctrl_post_fwd /load_post_bytes_d load_post_fold_fwd //.
Qed.

Lemma load_post_run_d_relp ws aq vaddr base ts :
  w_relp (load_post_run_d ws aq vaddr base ts) = w_relp ws.
Proof.
  rewrite /load_post_run_d ctrl_post_relp /load_post_bytes_d.
  generalize (load_run_ats base ts) => l. generalize ws at 2 3 => w.
  revert w. induction l as [|x l IH]; intros w; [done|by rewrite /= IH].
Qed.

Lemma load_post_run_d_coh ws aq vaddr base ts (j : nat) t :
  ts !! j = Some t →
  (t ≤ coh (load_post_run_d ws aq vaddr base ts) (base + Z.of_nat j))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run_d ctrl_post_coh /load_post_bytes_d.
  apply load_post_fold_coh, elem_of_list_lookup_2 with j.
  rewrite /load_run_ats lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Lemma load_post_run_d_vcap ws aq vaddr base ts :
  (vaddr ≤ w_vcap (load_post_run_d ws aq vaddr base ts))%nat.
Proof. rewrite /load_post_run_d ctrl_post_vcap. lia. Qed.

(** The RMW's exclusive-bank view is bounded like every other view. *)
Lemma ws_ldv0_bounded ws n : ws_bounded ws n → ws_bounded (ws_ldv0 ws) n.
Proof. apply instr_post_bounded. Qed.

Lemma ldv_of_bounded ws aq vaddr base ts n :
  ws_bounded ws n → (vaddr ≤ n)%nat → Forall (λ t, (t ≤ n)%nat) ts →
  (ldv_of ws aq vaddr base ts ≤ n)%nat.
Proof.
  intros Hb Hva Hall. rewrite /ldv_of.
  apply ws_bounded_ldv, load_post_run_d_bounded;
    [by apply ws_ldv0_bounded|exact Hva|exact Hall].
Qed.

(** *** The EXCLUSIVE load run (RMW split S2)

    Everything transfers from [load_post_run_d] through the record update:
    [ws_res_set] touches only [w_res], which is in neither [ws_le] nor
    [ws_depmove] and is handled by one extra [ws_bounded] conjunct. *)

Lemma ws_res_set_le ws1 ws2 r : ws_le ws1 ws2 → ws_le ws1 (ws_res_set ws2 r).
Proof. by rewrite /ws_le /ws_res_set /=. Qed.

Lemma ws_res_set_bounded ws r n :
  ws_bounded ws n → wresv_bounded r n → ws_bounded (ws_res_set ws r) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd & Hrg & Hvc & Hld
          & Hres & Htb) Hr.
  rewrite /ws_bounded /ws_res_set /=. by split_and!.
Qed.

Lemma res_view_bounded ws n : ws_bounded ws n → (res_view ws ≤ n)%nat.
Proof.
  intros Hb. rewrite /res_view.
  destruct (w_res ws) as [R|] eqn:HR; [|lia].
  by destruct (ws_bounded_res _ _ Hb R HR) as [_ ?].
Qed.

Lemma exload_post_run_d_le ws aq vaddr base ts :
  ws_le ws (exload_post_run_d ws aq vaddr base ts).
Proof. apply ws_res_set_le, load_post_run_d_le. Qed.

Lemma exload_post_run_d_bounded ws aq vaddr base ts n :
  ws_bounded ws n → (vaddr ≤ n)%nat →
  Forall (λ t, (t ≤ n)%nat) ts →
  ws_bounded (exload_post_run_d ws aq vaddr base ts) n.
Proof.
  intros Hb Hva Hall. apply ws_res_set_bounded.
  - by apply load_post_run_d_bounded.
  - intros R [= <-]. simpl. split.
    + intros j t Ht. rewrite Forall_lookup in Hall. by eapply Hall.
    + by apply ldv_of_bounded.
Qed.

Lemma exload_post_run_d_fwd ws aq vaddr base ts :
  w_fwd (exload_post_run_d ws aq vaddr base ts) = w_fwd ws.
Proof. rewrite /exload_post_run_d ws_res_set_fwd load_post_run_d_fwd //. Qed.

Lemma exload_post_run_d_relp ws aq vaddr base ts :
  w_relp (exload_post_run_d ws aq vaddr base ts) = w_relp ws.
Proof. rewrite /exload_post_run_d ws_res_set_relp load_post_run_d_relp //. Qed.

Lemma exload_post_run_d_coh ws aq vaddr base ts (j : nat) t :
  ts !! j = Some t →
  (t ≤ coh (exload_post_run_d ws aq vaddr base ts) (base + Z.of_nat j))%nat.
Proof.
  intros Ht. rewrite /exload_post_run_d ws_res_set_coh.
  by apply load_post_run_d_coh.
Qed.

Lemma exload_post_run_d_vcap ws aq vaddr base ts :
  (vaddr ≤ w_vcap (exload_post_run_d ws aq vaddr base ts))%nat.
Proof.
  rewrite /exload_post_run_d ws_res_set_vcap. apply load_post_run_d_vcap.
Qed.

(** *** The store run *)

Lemma store_post_d_le ws rl vf a t : ws_le ws (store_post_d ws rl vf a t).
Proof.
  rewrite /ws_le /store_post_d /=.
  split_and!; try (destruct rl, (w_relp ws); simpl; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. lia.
  - rewrite coh_upd_ne //.
Qed.

Lemma store_post_fold_d_le rl vf t as_ ws :
  ws_le ws (foldl (λ w a, store_post_d w rl vf a t) ws as_).
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [reflexivity|].
  etrans; [apply store_post_d_le|apply IH].
Qed.

Lemma store_post_bytes_d_le ws rl vf as_ t :
  ws_le ws (store_post_bytes_d ws rl vf as_ t).
Proof. apply store_post_fold_d_le. Qed.

Lemma store_post_run_d_le ws rl vaddr vdata base n t :
  ws_le ws (store_post_run_d ws rl vaddr vdata base n t).
Proof.
  rewrite /store_post_run_d.
  etrans; [apply store_post_bytes_d_le|apply ctrl_post_le].
Qed.

Local Lemma store_post_fold_d_bounded rl vf t as_ n' :
  (vf ≤ n')%nat → (t ≤ n')%nat →
  ∀ ws, ws_bounded ws n' →
    ws_bounded (foldl (λ w a, store_post_d w rl vf a t) ws as_) n'.
Proof.
  intros Hvf Ht. induction as_ as [|a l IH]; intros ws Hb; [exact Hb|].
  simpl. apply IH. eapply store_post_d_bounded; [exact Hb|exact Ht|lia|exact Hvf].
Qed.

Lemma store_post_bytes_d_bounded ws rl vf as_ t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat → (vf ≤ n')%nat →
  ws_bounded (store_post_bytes_d ws rl vf as_ t) n'.
Proof.
  intros Hb Ht Hle Hvf. rewrite /store_post_bytes_d.
  apply store_post_fold_d_bounded; [exact Hvf|exact Ht|].
  eapply ws_bounded_mono; [exact Hb|exact Hle].
Qed.

Lemma store_post_run_d_bounded ws rl vaddr vdata base cnt t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  (vaddr ≤ n')%nat → (vdata ≤ n')%nat →
  ws_bounded (store_post_run_d ws rl vaddr vdata base cnt t) n'.
Proof.
  intros Hb Ht Hle Hva Hvd. rewrite /store_post_run_d.
  apply ctrl_post_bounded;
    [|apply Nat.max_lub;
      [exact Hva|etrans; [by apply ws_bounded_tbank|exact Hle]]].
  apply (store_post_bytes_d_bounded _ _ _ _ _ n n'); [exact Hb|exact Ht|exact Hle|lia].
Qed.

Local Lemma store_post_fold_d_coh rl vf t as_ ws a :
  a ∈ as_ → (t ≤ coh (foldl (λ w a, store_post_d w rl vf a t) ws as_) a)%nat.
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [|apply ws_le_coh, store_post_fold_d_le].
  rewrite /store_post_d coh_upd_eq. lia.
Qed.

Lemma store_post_run_d_coh ws rl vaddr vdata base n t (j : nat) :
  (j < n)%nat →
  (t ≤ coh (store_post_run_d ws rl vaddr vdata base n t) (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite /store_post_run_d ctrl_post_coh /store_post_bytes_d.
  apply store_post_fold_d_coh, elem_of_list_In, in_map_iff.
  exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

Local Lemma store_post_fold_d_vwOld rl vf t as_ ws :
  as_ ≠ [] → (t ≤ w_vwOld (foldl (λ w a, store_post_d w rl vf a t) ws as_))%nat.
Proof.
  destruct as_ as [|a l]; [done|]. intros _. simpl.
  etrans; [|apply ws_le_vwOld, store_post_fold_d_le].
  rewrite /store_post_d /=. lia.
Qed.

Lemma store_post_run_d_vwOld ws rl vaddr vdata base n t :
  (0 < n)%nat →
  (t ≤ w_vwOld (store_post_run_d ws rl vaddr vdata base n t))%nat.
Proof.
  intros Hn. rewrite /store_post_run_d ctrl_post_vwOld /store_post_bytes_d.
  apply store_post_fold_d_vwOld. rewrite /store_run_as. by destruct n; [lia|].
Qed.

Local Lemma store_post_fold_d_relp rl vf t as_ ws :
  as_ ≠ [] → w_relp (foldl (λ w a, store_post_d w rl vf a t) ws as_) = false.
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws Hne; [done|].
  simpl. destruct l as [|b l']; [done|]. by apply IH.
Qed.

Lemma store_post_run_d_relp ws rl vaddr vdata base n t :
  (0 < n)%nat → w_relp (store_post_run_d ws rl vaddr vdata base n t) = false.
Proof.
  intros Hn. rewrite /store_post_run_d ctrl_post_relp /store_post_bytes_d.
  apply store_post_fold_d_relp. rewrite /store_run_as. by destruct n; [lia|].
Qed.

Local Lemma store_post_fold_d_fwd rl vf t as_ ws a tf vfd :
  w_fwd (foldl (λ w a, store_post_d w rl vf a t) ws as_) !! a = Some (tf, vfd) →
  (tf = t ∧ vfd = vf) ∨ w_fwd ws !! a = Some (tf, vfd).
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hlk; [by right|].
  destruct (IH _ Hlk) as [Heq|Hlk']; [by left|].
  rewrite /store_post_d /= in Hlk'.
  destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert in Hlk'. simplify_eq. by left.
  - rewrite lookup_insert_ne in Hlk'; [done|]. by right.
Qed.

Lemma store_post_run_d_fwd_inv ws rl vaddr vdata base n t a tf vfd :
  w_fwd (store_post_run_d ws rl vaddr vdata base n t) !! a = Some (tf, vfd) →
  (tf = t ∧ vfd = Nat.max vaddr vdata) ∨ w_fwd ws !! a = Some (tf, vfd).
Proof.
  rewrite /store_post_run_d ctrl_post_fwd /store_post_bytes_d.
  apply store_post_fold_d_fwd.
Qed.

Lemma store_post_run_d_vcap ws rl vaddr vdata base n t :
  (vaddr ≤ w_vcap (store_post_run_d ws rl vaddr vdata base n t))%nat.
Proof. rewrite /store_post_run_d ctrl_post_vcap. lia. Qed.

(** *** THE DEPENDENCY-FREE RUN IS BELOW THE DEPENDENCY-CARRYING ONE

    A bigger address view only raises the load's pre-view (and the control
    view), so every component of the post-state grows.  This is the
    behaviour-REMOVING direction the deps design predicts, and it is what
    lets a consumer that proved a LOWER BOUND against the old
    [load_post_run] keep it against [load_post_run_d]. *)

Lemma load_post_at_mono ws1 ws2 aq vpre1 vpre2 a t :
  ws_le ws1 ws2 → w_fwd ws1 = w_fwd ws2 → (vpre1 ≤ vpre2)%nat →
  ws_le (load_post_at ws1 aq vpre1 a t) (load_post_at ws2 aq vpre2 a t).
Proof.
  intros Hle Hfw Hvp.
  have Hfv : fwd_view ws1 aq a t = fwd_view ws2 aq a t
    by rewrite /fwd_view Hfw.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HR & Hpub & Hvc).
  rewrite /ws_le /load_post_at /=. split_and!; try (destruct aq; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite !coh_upd_eq. pose proof (Hcoh a). lia.
  - rewrite !coh_upd_ne // -!/(coh ws1 a') -!/(coh ws2 a'). apply Hcoh.
Qed.

Local Lemma load_post_fold_mono aq vpre1 vpre2 ats :
  (vpre1 ≤ vpre2)%nat →
  ∀ w1 w2, ws_le w1 w2 → w_fwd w1 = w_fwd w2 →
    ws_le (foldl (λ w at_, load_post_at w aq vpre1 at_.1 at_.2) w1 ats)
          (foldl (λ w at_, load_post_at w aq vpre2 at_.1 at_.2) w2 ats).
Proof.
  intros Hvp. induction ats as [|x l IH]; intros w1 w2 Hle Hfw; [exact Hle|].
  simpl. apply IH.
  - by apply load_post_at_mono.
  - by rewrite !load_post_at_fwd.
Qed.

(** The BYTE-fold form.  Stated separately because [simpl] peels the
    run-level [ctrl_post] projection off a component accessor, leaving a
    goal about [load_post_bytes_d] that the run-level lemma cannot see. *)
Lemma load_post_bytes_d_mono ws aq vaddr ats :
  ws_le (load_post_bytes ws aq ats) (load_post_bytes_d ws aq vaddr ats).
Proof.
  rewrite /load_post_bytes_d /load_post_bytes.
  apply load_post_fold_mono; [rewrite /load_vpre_d; lia|reflexivity|done].
Qed.

Lemma load_post_run_d_mono ws aq vaddr base ts :
  ws_le (load_post_run ws aq base ts) (load_post_run_d ws aq vaddr base ts).
Proof.
  rewrite /load_post_run /load_post_run_d.
  apply ctrl_post_mono; [apply load_post_bytes_d_mono|lia].
Qed.

(* ================================================================== *)
(** ** A RAISED CONTROL VIEW, AND NOTHING ELSE ([ws_ctrl_up])

    W-TV's consumption is the only thing the RUN-level wrappers do that the
    per-byte functions do not, and it moves ONLY [w_vcap].  A machine that
    steps with [load_post]/[store_post] — the toy hart-program machine
    [WeakLitmus], whose accesses are all single-byte and which has no
    [LInstr] to reset the bank with — therefore tracks one that steps with
    the run functions ([WeakAxiomatic.mstep]) up to exactly this relation,
    which is what [WeakLitmusProj.lcfg_match] carries in place of the
    [wstate] equality it carried before W-TV.  The slack is invisible to
    every side condition on either side: neither machine READS [w_vcap]
    (the axiomatic tier has no [fulfil_ok] at all). *)
Definition ws_ctrl_up (w1 w2 : wstate) : Prop := ∃ v, w2 = ctrl_post w1 v.

Global Instance ws_ctrl_up_refl : Reflexive ws_ctrl_up.
Proof. intros w. exists 0%nat. by rewrite ctrl_post_0. Qed.

Lemma ws_ctrl_up_le w1 w2 : ws_ctrl_up w1 w2 → ws_le w1 w2.
Proof. intros [v ->]. apply ctrl_post_le. Qed.

(** Two control raises are one. *)
Lemma ctrl_post_ctrl ws v1 v2 :
  ctrl_post (ctrl_post ws v1) v2 = ctrl_post ws (Nat.max v1 v2).
Proof.
  rewrite {1 2}/ctrl_post /=. by rewrite Nat.max_assoc (Nat.max_comm v2 v1).
Qed.

Global Instance ws_ctrl_up_trans : Transitive ws_ctrl_up.
Proof.
  intros w1 w2 w3 [v1 ->] [v2 ->]. exists (Nat.max v1 v2).
  by rewrite ctrl_post_ctrl.
Qed.

(** The three per-byte step functions COMMUTE with a control raise: none of
    them reads [w_vcap], and each copies it through. *)
Lemma load_post_at_ctrl ws aq v vpre a t :
  load_post_at (ctrl_post ws v) aq vpre a t
  = ctrl_post (load_post_at ws aq vpre a t) v.
Proof. done. Qed.

Lemma load_post_ctrl ws aq v a t :
  load_post (ctrl_post ws v) aq a t = ctrl_post (load_post ws aq a t) v.
Proof. done. Qed.

Lemma store_post_ctrl ws rl v a t :
  store_post (ctrl_post ws v) rl a t = ctrl_post (store_post ws rl a t) v.
Proof. done. Qed.

Lemma fence_post_ctrl ws v pr pw sr sw :
  fence_post (ctrl_post ws v) pr pw sr sw
  = ctrl_post (fence_post ws pr pw sr sw) v.
Proof. done. Qed.

(** The byte FOLD commutes too, hence so does the whole dependency-carrying
    load run: a control raise on the entry state comes out unchanged on the
    post-state (the bank it consumes is not the raised component). *)
Local Lemma load_post_fold_ctrl aq vpre ats v :
  ∀ ws,
    foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) (ctrl_post ws v) ats
    = ctrl_post (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) v.
Proof.
  induction ats as [|x l IH]; intros ws; [done|].
  by rewrite /= load_post_at_ctrl IH.
Qed.

Lemma load_post_bytes_d_ctrl ws aq vaddr ats v :
  load_post_bytes_d (ctrl_post ws v) aq vaddr ats
  = ctrl_post (load_post_bytes_d ws aq vaddr ats) v.
Proof. rewrite /load_post_bytes_d. apply load_post_fold_ctrl. Qed.

Lemma load_post_run_d_ctrl ws aq vaddr base ts v :
  load_post_run_d (ctrl_post ws v) aq vaddr base ts
  = ctrl_post (load_post_run_d ws aq vaddr base ts) v.
Proof.
  rewrite /load_post_run_d load_post_bytes_d_ctrl ctrl_post_tbank.
  rewrite !ctrl_post_ctrl. by rewrite Nat.max_comm.
Qed.

(** … hence the SINGLE-BYTE run-level arms preserve the relation. *)
Lemma ws_ctrl_up_load ws1 ws2 aq base t :
  ws_ctrl_up ws1 ws2 →
  ws_ctrl_up (load_post ws1 aq base t) (load_post_run ws2 aq base [t]).
Proof.
  intros [v ->]. rewrite load_post_run_single load_post_ctrl ctrl_post_tbank.
  rewrite ctrl_post_ctrl. by eexists.
Qed.

Lemma ws_ctrl_up_store ws1 ws2 rl base t :
  ws_ctrl_up ws1 ws2 →
  ws_ctrl_up (store_post ws1 rl base t) (store_post_run ws2 rl base 1 t).
Proof.
  intros [v ->].
  rewrite /store_post_run /store_post_bytes /= Z.add_0_r store_post_ctrl.
  rewrite ctrl_post_ctrl. by eexists.
Qed.

Lemma ws_ctrl_up_fence ws1 ws2 pr pw sr sw :
  ws_ctrl_up ws1 ws2 →
  ws_ctrl_up (fence_post ws1 pr pw sr sw) (fence_post ws2 pr pw sr sw).
Proof. intros [v ->]. rewrite fence_post_ctrl. by eexists. Qed.
