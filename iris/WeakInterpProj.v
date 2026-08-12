(** * WeakInterpProj.v — projecting [WeakInterp.wrun] onto [WeakAxiomatic.exec_wf]

    M6 / W4 "Projection lemmas" ([claude-notes/projects/weak-memory-m6.md]).
    [WeakPromiseBridge.v] projects the FULL promising machine onto the
    canonical axiomatic LTS; this file does the same for the OTHER consumer of
    [WeakMem] — the Sail interpreter [WeakInterp.wrun].

        one agent's [wrun] step  ⟶  an extension of a [WeakAxiomatic] execution

    The projection is PER AGENT.  A [wmstate] is one hart's view of the machine
    (its registers, the era-initial image, the global log, its own [wstate],
    its device fabric); a [WeakAxiomatic.mstate] carries the log plus EVERY
    agent's [wstate].  So the state relation [ws_match i s σ] constrains only
    agent [i]'s slot and FRAMES the others, and the extension lemma reports
    that the framed slots did not move.

    ------------------------------------------------------------------------
    WHAT THE PROJECTION KEEPS AND WHAT IT DROPS.  Five deliberate losses, each
    sound for THIS direction (we produce an [exec_wf], i.e. every emitted step
    must be legal; we do not claim the projection is onto).

    (1) REGISTERS, DEVICES AND TRACE OUTCOMES ARE INVISIBLE.  [wset_reg] /
        [wset_dev] and every announce/exception/cycle outcome move neither
        [wm_img], [wm_log] nor [wm_ws], so [ws_match] is preserved
        DEFINITIONALLY and those arms emit no event.  MMIO reads and writes go
        through [dev_read]/[dev_write] and are likewise silent: device views
        are M5, and the axiomatic alphabet has no device label.

    (2) COHERENT READS ARE SILENT.  A read whose [akinfo] has [ak_coh = true]
        (instruction fetch, page-table walk) leaves [wm_ws] AND [wm_log]
        untouched ([WeakInterp.wread_post_coh_id]), so it projects to NO event
        and [ws_match] is preserved on the nose.  Sound because such a step
        changes no projected state; the rf edges it would contribute are not
        needed by the consumer (design Decision 4: kernel text has a single
        message, so every admissible fetch returns the same byte).  Note this
        arm is DEAD for rv64d anyway — [WeakInterp] §3 records that the model
        never emits [AK_ifetch]/[AK_ttw].

    (3) THE [ak_latest] PINNING IS DROPPED.  An exclusive (or [AK_arch]) read
        satisfies, on top of readability, "no write to this byte above [t]".
        [WeakAxiomatic.rd_ok] asks only for readability, so a pinned read
        projects to a plain [LLoad] — the same "pinning dropped, sound for this
        direction" move [WeakPromiseBridge] makes for [read_ok]'s [lat] flag
        (cf. [WeakMem.latest_readable]).

    (4) AN AMO IS SPLIT, NOT FUSED.  The Sail model emits an AMO as TWO
        outcomes — an exclusive [MemRead] and then a conditional [MemWrite] —
        with arbitrary monadic code in between, and [wrun] threads them as two
        independent state updates.  They therefore project to an [LLoad]
        followed by an [LStore], NEVER to an [LRmw].  Each emitted step is
        legal, so the produced execution is [exec_wf]; what is lost is the
        atomicity LINK (and with it [mstep]'s [rmw_latest] side condition,
        which the projected pair does not have to satisfy).  *** IF W5 EVER
        NEEDS THE RMW FUSED, THIS FILE IS WHERE IT CHANGES: the fix is a
        coarser step relation on the Sail side that runs read-half and
        write-half as one unit, since [wrun] itself cannot see the pairing. ***

    (5) AN HONEST ADDED PREMISE: [nz_writes].  [mstep]'s store arm demands a
        NONEMPTY message ([vs ≠ []]), while [WeakInterp.wwrite_post] happily
        appends a zero-byte message for a width-0 [MemWrite] — the log would
        grow with no axiomatic step to mirror it, breaking [ws_match]'s
        [ms_log σ = wm_log s].  Widths are 1/2/4/8 in every RISC-V access, so
        the premise is vacuous in practice; it is stated as the monad-level
        predicate [nz_writes] (every non-device [MemWrite] node has width
        [n ≠ 0]) and is the caller's obligation downstream.

    ADDRESSING.  [WeakInterp.acc_addr pa j = pa_z pa + j] and
    [WeakAxiomatic.acc_addr base j = base + j] agree at [base = pa_z pa] by
    conversion, so no seam lemma is needed; the two [acc_addr]s are distinct
    constants and every ambiguous occurrence below is qualified.

    DEPENDENCIES: [WeakInterp]'s (hence the Sail model) plus [WeakAxiomatic].
    Nothing Iris. *)
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakAxiomatic WeakInterp.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The byte list of an access

    Both sides spell a multi-byte access's payload as the little-endian byte
    list of its value; [WeakInterp.wwrite_msg] already uses exactly this list,
    so [wwrite_msg_wbytes] below is [eq_refl]. *)

Definition wbytes (n : N) {w : N} (v : bv w) : list (bv 8) :=
  map (λ j : nat, nth_byte v j) (seq 0 (N.to_nat n)).

Lemma wbytes_length (n : N) {w : N} (v : bv w) :
  length (wbytes n v) = N.to_nat n.
Proof. rewrite /wbytes length_map length_seq //. Qed.

Lemma wbytes_lookup (n : N) {w : N} (v : bv w) (j : nat) :
  (j < N.to_nat n)%nat → wbytes n v !! j = Some (nth_byte v j).
Proof. intros Hj. rewrite /wbytes list_lookup_fmap lookup_seq_lt //. Qed.

Lemma wbytes_nonnil (n : N) {w : N} (v : bv w) : n ≠ 0%N → wbytes n v ≠ [].
Proof.
  intros Hn Hc. apply (f_equal length) in Hc.
  rewrite wbytes_length /= in Hc. lia.
Qed.

Lemma wwrite_msg_wbytes tid k pa n {w : N} (v : bv w) :
  wwrite_msg tid k pa n v = WMsg (pa_z pa) (wbytes n v) tid k.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 2. The state relation and execution extension *)

(** Agent [i]'s slot is pinned; every other agent's [wstate] is framed (a
    [wmstate] simply does not mention them). *)
Definition ws_match (i : agent) (s : wmstate) (σ : mstate) : Prop :=
  ms_img σ = wimg s ∧ ms_log σ = wm_log s ∧ ms_ws σ i = wm_ws s.

(** "[E'] continues [E]": both components grow at the end.  This is what
    [WeakAxiomatic.exec_snoc] produces, and it is what makes the era-initial
    image [ex_img] stable ([exec_extends_img]). *)
Definition exec_extends (E E' : exec) : Prop :=
  ex_st E `prefix_of` ex_st E' ∧ ex_tr E `prefix_of` ex_tr E'.

Global Instance exec_extends_refl : Reflexive exec_extends.
Proof. intros E. split; reflexivity. Qed.

Global Instance exec_extends_trans : Transitive exec_extends.
Proof.
  intros E1 E2 E3 [H1 H2] [H3 H4]. split.
  - etrans; [exact H1|exact H3].
  - etrans; [exact H2|exact H4].
Qed.

Lemma exec_extends_img E E' :
  exec_wf E → exec_extends E E' → ex_img E' = ex_img E.
Proof.
  intros Hwf [Hst _].
  destruct (exec_st_len E 0%nat Hwf ltac:(lia)) as [σ0 Hσ0].
  rewrite /ex_img /eimg (stt_lookup _ _ _ Hσ0).
  rewrite (stt_lookup _ _ _ (prefix_lookup_Some _ _ _ _ Hσ0 Hst)) //.
Qed.

(** Appending ONE machine step, with the new final state named.  (This is
    [WeakPromiseBridge.bridge_step]'s core, factored so that the [fence.tso]
    arm can use it twice.) *)
Lemma exec_extend E i lb σ' :
  exec_wf E → mstep (stt E (length (ex_tr E))) i lb σ' →
  ∃ E', exec_wf E' ∧ exec_extends E E' ∧ stt E' (length (ex_tr E')) = σ'.
Proof.
  intros HE Hms. exists (Exec (ex_st E ++ [σ']) (ex_tr E ++ [EStep i lb])).
  pose proof HE as (Hlen & _ & _). split_and!.
  - apply (exec_snoc E (EStep i lb) σ'); [done|by simpl].
  - split; simpl; by apply prefix_app_r.
  - rewrite /stt /= length_app /=. rewrite lookup_app_r; [lia|].
    replace (length (ex_tr E) + 1 - length (ex_st E))%nat with 0%nat by lia.
    by simpl.
Qed.

(** The shape every arm below produces.  [E ⊑ E'], agent [i] ends in the
    [wmstate] the interpreter reached, every other agent is untouched. *)
Definition proj_ext (i : agent) (s' : wmstate) (E E' : exec) : Prop :=
  exec_wf E' ∧ exec_extends E E' ∧
  ws_match i s' (stt E' (length (ex_tr E'))) ∧
  (∀ j, j ≠ i → ms_ws (stt E' (length (ex_tr E'))) j
              = ms_ws (stt E (length (ex_tr E))) j).

Lemma proj_ext_refl i s E :
  exec_wf E → ws_match i s (stt E (length (ex_tr E))) → proj_ext i s E E.
Proof. intros ??. split_and!; [done|reflexivity|done|done]. Qed.

Lemma proj_ext_trans i s1 s2 E E1 E2 :
  proj_ext i s1 E E1 → proj_ext i s2 E1 E2 → proj_ext i s2 E E2.
Proof.
  intros (_ & Hx1 & _ & Hf1) (H2 & Hx2 & Hm2 & Hf2). split_and!.
  - done.
  - etrans; [exact Hx1|exact Hx2].
  - done.
  - intros j Hne. rewrite (Hf2 j Hne) (Hf1 j Hne) //.
Qed.

(* ====================================================================== *)
(** ** 3. The three event-emitting arms *)

(** FENCE.  [barrier_post] is one [fence_post], two of them ([fence.tso]) or
    the identity ([fence.i]); this is the one-step case. *)
Lemma exec_fence E i s pr pw sr sw :
  exec_wf E → ws_match i s (stt E (length (ex_tr E))) →
  ∃ E', proj_ext i (wset_ws s (fence_post (wm_ws s) pr pw sr sw)) E E'.
Proof.
  intros HE Hm. pose proof Hm as (Himg & Hlog & Hws).
  destruct (exec_extend E i (LFence pr pw sr sw) _ HE
              (MStepFence _ _ pr pw sr sw)) as (E' & HE' & Hext & Hst).
  exists E'. split_and!; [done|done| |]; rewrite Hst /=.
  - rewrite /ws_match /=. split_and!; [done|done|].
    rewrite upd_ws_eq Hws //.
  - intros j Hne. by rewrite upd_ws_ne.
Qed.

(** The whole barrier lattice: nine single fences, [fence.tso] = two chained
    fences, [fence.i] = no event at all (it is the identity on [wstate]s). *)
Lemma exec_barrier E i s b :
  exec_wf E → ws_match i s (stt E (length (ex_tr E))) →
  ∃ E', proj_ext i (wset_ws s (barrier_post (wm_ws s) b)) E E'.
Proof.
  intros HE Hm. destruct b; cbn [barrier_post].
  - exact (exec_fence E i s true  true  true  true  HE Hm).
  - exact (exec_fence E i s true  false true  true  HE Hm).
  - exact (exec_fence E i s true  false true  false HE Hm).
  - exact (exec_fence E i s true  true  false true  HE Hm).
  - exact (exec_fence E i s false true  false true  HE Hm).
  - exact (exec_fence E i s false true  true  true  HE Hm).
  - exact (exec_fence E i s true  true  true  false HE Hm).
  - exact (exec_fence E i s true  false false true  HE Hm).
  - exact (exec_fence E i s false true  true  false HE Hm).
  - (* fence.tso = fence r,r ; fence rw,w *)
    destruct (exec_fence E i s true false true false HE Hm) as (E1 & Hp1).
    pose proof Hp1 as (HE1 & _ & Hm1 & _).
    destruct (exec_fence E1 i (wset_ws s (fence_post (wm_ws s) true false true false))
                true true false true HE1 Hm1) as (E2 & Hp2).
    exists E2. exact (proj_ext_trans _ _ _ _ _ _ Hp1 Hp2).
  - (* fence.i *)
    exists E. apply proj_ext_refl; [done|exact Hm].
Qed.

(** LOAD.  A coherent read emits nothing (header, (2)); a weak read emits one
    [LLoad] whose [rd_ok] is [wread_ok] minus the [ak_latest] pinning
    (header, (3)). *)
Lemma exec_read E i s ak pa n ts w :
  exec_wf E → ws_match i s (stt E (length (ex_tr E))) →
  wread_ok s ak pa n ts w →
  ∃ E', proj_ext i (wread_post s ak pa ts) E E'.
Proof.
  intros HE Hm Hok. destruct (ak_coh ak) eqn:Hcoh.
  { exists E. rewrite (wread_post_coh_id s ak pa ts Hcoh).
    by apply proj_ext_refl. }
  pose proof Hm as (Himg & Hlog & Hws).
  pose proof Hok as (Hlen & Hbytes).
  have Hrd : rd_ok (ms_img (stt E (length (ex_tr E))))
                   (ms_log (stt E (length (ex_tr E))))
                   (ms_ws (stt E (length (ex_tr E))) i)
                   (ak_sync ak) (pa_z pa) ts (wbytes n w).
  { rewrite Himg Hlog Hws. split; [by rewrite wbytes_length|].
    intros j t v Ht Hv.
    pose proof (lookup_lt_Some _ _ _ Ht) as Hj. rewrite Hlen in Hj.
    rewrite (wbytes_lookup n w j Hj) in Hv.
    pose proof (Hbytes j ltac:(lia)) as Hb.
    rewrite /wbyte_ok Hcoh (list_lookup_total_correct _ _ _ Ht) in Hb.
    destruct Hb as (Hlb & Hrdb & _). simplify_eq/=. by split. }
  destruct (exec_extend E i (LLoad (ak_sync ak) (pa_z pa) ts (wbytes n w)) _ HE
              (MStepLoad _ _ (ak_sync ak) (pa_z pa) ts (wbytes n w) Hrd))
    as (E' & HE' & Hext & Hst).
  exists E'. split_and!; [done|done| |]; rewrite Hst /=.
  - rewrite /ws_match /wread_post Hcoh /=. split_and!; [done|done|].
    rewrite upd_ws_eq Hws //.
  - intros j Hne. by rewrite upd_ws_ne.
Qed.

(** STORE.  [wwrite_post] appends [wwrite_msg] at the log's fresh top and
    applies [store_post_run] at [S (length log)] — literally [MStepStore]'s
    post-state.  The [n ≠ 0] premise is the honest one of header (5). *)
Lemma exec_write E i s ak pa n (v : bv (8 * n)) :
  exec_wf E → ws_match i s (stt E (length (ex_tr E))) → n ≠ 0%N →
  ∃ E', proj_ext i (wwrite_post (Some i) s ak pa n v) E E'.
Proof.
  intros HE Hm Hn. pose proof Hm as (Himg & Hlog & Hws).
  destruct (exec_extend E i
              (LStore (ak_sync ak) (pa_z pa) (wbytes n v)
                 (wm_class_of ak (wm_ws s))) _ HE
              (MStepStore _ _ (ak_sync ak) (pa_z pa) (wbytes n v)
                 (wm_class_of ak (wm_ws s)) (wbytes_nonnil n v Hn)))
    as (E' & HE' & Hext & Hst).
  exists E'. split_and!; [done|done| |]; rewrite Hst /=.
  - rewrite /ws_match /wwrite_post /=. split_and!.
    + done.
    + rewrite Hlog wwrite_msg_wbytes //.
    + rewrite upd_ws_eq Hws Hlog wbytes_length //.
  - intros j Hne. by rewrite upd_ws_ne.
Qed.

(* ====================================================================== *)
(** ** 4. The width side condition on the monad

    Every non-device [MemWrite] node of [m] has a nonzero width.  Stated over
    the WHOLE monad (all continuations, not only the ones the run takes),
    which is the shape a caller can discharge by inspecting the decoded
    instruction.  See header (5) for why it is needed at all. *)
Fixpoint nz_writes {X} (m : M X) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       | Interface.MemWrite n req =>
           fun k => (dev_addr (Interface.WriteReq.pa req) = true ∨ n ≠ 0%N)
                    ∧ ∀ r, nz_writes (k r)
       | _ => fun k => ∀ r, nz_writes (k r)
       end) k
  end.

(* ====================================================================== *)
(** ** 5. THE CORE LEMMA

    One [wrun] of agent [i] extends any [exec_wf] execution whose final state
    matches [i]'s pre-state, to one whose final state matches [i]'s post-state
    — leaving every other agent's [wstate] where it was.

    The induction is [WeakInterp]'s own ([wrun_ws_le] &c.): a dependent
    [induction m] mirroring [wrun]'s [Fixpoint]. *)
Lemma wrun_exec (i : agent) {X} (m : M X) :
  ∀ s x s' E,
    nz_writes m →
    wrun (Some i) m s x s' →
    exec_wf E → ws_match i s (stt E (length (ex_tr E))) →
    ∃ E', proj_ext i s' E E'.
Proof.
  induction m as [y|T oc k IH]; intros s x s' E Hnz Hrun HE Hm.
  - destruct Hrun as [_ ->]. exists E. by apply proj_ext_refl.
  - destruct oc; simpl in Hrun, Hnz;
      try (exact (IH _ _ _ _ _ (Hnz _) Hrun HE Hm));
      try (exfalso; exact Hrun);
      try (destruct Hrun as (c & Hrun); exact (IH _ _ _ _ _ (Hnz _) Hrun HE Hm)).
    + (* MemRead *)
      lazymatch type of Hrun with
      | context[dev_addr ?p] => destruct (dev_addr p) eqn:Hd
      end.
      * (* MMIO read: silent, [wset_dev] moves nothing matched *)
        destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ _ (Hnz _) Hrun HE Hm).
      * destruct Hrun as (w & ts & Hok & Hrun).
        destruct (exec_read E i s _ _ _ ts w HE Hm Hok) as (E1 & Hp1).
        pose proof Hp1 as (HE1 & _ & Hm1 & _).
        destruct (IH _ _ _ _ _ (Hnz _) Hrun HE1 Hm1) as (E2 & Hp2).
        exists E2. exact (proj_ext_trans _ _ _ _ _ _ Hp1 Hp2).
    + (* MemWrite *)
      destruct Hnz as (Hn & Hnz).
      lazymatch type of Hrun with
      | context[dev_addr ?p] => destruct (dev_addr p) eqn:Hd
      end.
      * (* MMIO write: silent *)
        destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ _ (Hnz _) Hrun HE Hm).
      * have Hn0 : n ≠ 0%N by destruct Hn; [congruence|done].
        lazymatch type of Hrun with
        | context[wwrite_post _ _ ?ak ?pa _ ?v] =>
            destruct (exec_write E i s ak pa n v HE Hm Hn0) as (E1 & Hp1)
        end.
        pose proof Hp1 as (HE1 & _ & Hm1 & _).
        destruct (IH _ _ _ _ _ (Hnz _) Hrun HE1 Hm1) as (E2 & Hp2).
        exists E2. exact (proj_ext_trans _ _ _ _ _ _ Hp1 Hp2).
    + (* Barrier: one, two, or zero fences *)
      destruct (exec_barrier E i s b HE Hm) as (E1 & Hp1).
      pose proof Hp1 as (HE1 & _ & Hm1 & _).
      destruct (IH _ _ _ _ _ (Hnz _) Hrun HE1 Hm1) as (E2 & Hp2).
      exists E2. exact (proj_ext_trans _ _ _ _ _ _ Hp1 Hp2).
Qed.

(* ====================================================================== *)
(** ** 6. Whole runs

    A chain of instruction executions by ONE agent.  (Multi-agent
    interleaving — several [wmstate]s sharing one log — is W5's composition
    job, not this file's: nothing here fixes how two agents' logs are kept in
    step.) *)

Definition wstep (i : agent) (s s' : wmstate) : Prop :=
  ∃ (X : Type) (m : M X) (x : X), nz_writes m ∧ wrun (Some i) m s x s'.

Lemma wrun_chain_exec (i : agent) s0 s :
  rtc (wstep i) s0 s →
  ∀ E, exec_wf E → ws_match i s0 (stt E (length (ex_tr E))) →
  ∃ E', proj_ext i s E E'.
Proof.
  induction 1 as [s0|s0 s1 s2 (X & m & x & Hnz & Hrun) _ IH]; intros E HE Hm.
  - exists E. by apply proj_ext_refl.
  - destruct (wrun_exec i m s0 x s1 E Hnz Hrun HE Hm) as (E1 & Hp1).
    pose proof Hp1 as (HE1 & _ & Hm1 & _).
    destruct (IH E1 HE1 Hm1) as (E2 & Hp2).
    exists E2. exact (proj_ext_trans _ _ _ _ _ _ Hp1 Hp2).
Qed.

(** THE PROJECTION THEOREM.  From a fresh [wmstate] (empty log, [ws_init]),
    any chain of [wrun] instruction executions by agent [i] induces a
    well-formed [WeakAxiomatic] execution with the same era-initial image, the
    same final log, and [i]'s final [wstate]; every other agent is still at
    [ws_init] (nobody else stepped). *)
Theorem wrun_exec_wf (i : agent) s0 s :
  wm_log s0 = [] → wm_ws s0 = ws_init →
  rtc (wstep i) s0 s →
  ∃ E, exec_wf E ∧
       ex_img E = wimg s0 ∧
       ex_log E = wm_log s ∧
       ews E (length (ex_tr E)) i = wm_ws s ∧
       (∀ j, j ≠ i → ews E (length (ex_tr E)) j = ws_init).
Proof.
  intros Hlog0 Hws0 Hrun.
  set (σ0 := MSt (wimg s0) [] (λ _ : agent, ws_init)).
  have HE0 : exec_wf (Exec [σ0] []) by apply exec_nil.
  have Hm0 : ws_match i s0 (stt (Exec [σ0] []) (length (ex_tr (Exec [σ0] [])))).
  { rewrite /ws_match /stt /=. split_and!; [done|by rewrite Hlog0|].
    by rewrite Hws0. }
  destruct (wrun_chain_exec i s0 s Hrun (Exec [σ0] []) HE0 Hm0)
    as (E & HE & Hext & (Himg & Hlog & Hws) & Hfr).
  exists E. split_and!.
  - done.
  - rewrite (exec_extends_img _ _ HE0 Hext) //.
  - rewrite /ex_log /elog Hlog //.
  - rewrite /ews Hws //.
  - intros j Hne. rewrite /ews (Hfr j Hne) //.
Qed.
