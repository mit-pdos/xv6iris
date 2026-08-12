(** * WeakSailLTS.v — the EVENT-LEVEL Sail program LTS (M6 / W5)

    [WeakPromise.v]'s machine is parametric in an abstract per-agent program
    LTS [pstep : P → wlabel → P → Prop]; the M6 robustness theorem (Layer 1)
    is stated over that parameter.  THIS FILE IS THE INSTANTIATION the W5
    composition needs: [psail] — the residual instruction monad plus the
    hart's register file and its MMIO oracle stream — with [sail_step]
    mirroring [WeakInterp.wrun]'s arms ONE LABEL PER MEMORY EVENT.

    Three things are delivered:

    (1) the LTS ([psail], [sail_step]) and its two Layer-1 side conditions —
        LAT-FREEDOM ([sail_lat_free]) and TIMESTAMP-OBLIVIOUSNESS
        ([sail_ts_oblivious], [sail_ts_oblivious_rmw]);
    (2) the FUSED RMW arm, which is the fix point [WeakInterpProj.v]'s header
        (4) explicitly defers to W5: the Sail model emits an AMO as an
        exclusive [MemRead] and a conditional [MemWrite] with arbitrary
        register/trace code in between, and this LTS brackets that whole
        span into ONE [WeakPromise.LRmw] label;
    (3) the BRACKETING theorem [wrun_sail_bracket]: one [wrun] of an
        instruction monad is an [rtc] of [WeakPromiseBridge.wp_pf_run] steps
        of the ONE stepping agent, with the same log, the same [wstate] and
        the same registers at the end.  [sail_instr_bracket] wraps it with
        the instruction-boundary steps for [RiscvLang.riscv_step], which is
        what [WeakLang.wprim_step]'s hart arm runs.

    ------------------------------------------------------------------------
    DESIGN DELTAS (each deliberate; read before extending this file).

    (a) [sail_step] IS A [Definition] BY [match], NOT AN [Inductive].  The
        outcome type of [Interface.MemRead n req] is
        [bv (8 * n) * option bool + abort], i.e. it DEPENDS on the outcome
        being matched; an inductive whose constructors pattern-match on
        [Interface.Next oc k] would have to spell each continuation type by
        hand.  [wrun] itself is written as a [Fixpoint] with the
        [match oc in Interface.outcome _ T return (T → M X) → Prop] idiom for
        exactly this reason, and this file MIRRORS IT — every arm of
        [sail_mstep] sits opposite the [wrun] arm it brackets.  Being a
        [Definition], inversion is [destruct]+[simpl] rather than
        [inversion], which is also what keeps the proofs below small.

    (b) THE MMIO ORACLE.  [wpcfg] has no device component (design decision
        recorded in the W5 notes block: the retained MMIO-ordering assumption
        covers the stream ↔ real-device seam), so device reads are served
        from a per-agent stream [sp_dev : dstream] carried INSIDE the program
        state and consumed silently; device writes are silent and consume
        nothing.  One entry is the little-endian byte list of the word the
        device returned, so the bracket's stream is existentially produced by
        the run — one [wbytes n w] entry per device read, appended in the
        order the run performs them, and CONSUMED EXACTLY (the bracket runs
        from [str ++ tail] to [tail]).

    (c) THE PENDING SECOND FENCE.  [WeakInterp.barrier_post] makes
        [fence.tso] TWO chained [fence_post]s, but a [wlabel] carries one
        fence.  [sail_step] emits the FIRST fence (r,r) AND TAKES THE
        CONTINUATION [k tt] in the same step, parking the second fence
        (rw,w) in [sp_fence]; the next step emits it and clears the field,
        leaving [sp_m] alone.  While [sp_fence] is set NO other arm can
        fire — the outer match on [sp_fence] gates everything — so the two
        fences cannot be separated by another event of this agent.
        [fence.i] is [LSilent] ([barrier_post] is the identity on it).

    (d) COHERENT READS ARE A STUCK ARM, NOT A SILENT ONE.  A read with
        [ak_coh = true] (ifetch / page-table walk) would want [lat = true],
        which lat-freedom forbids; [WeakInterp] §3's finding (1) says rv64d
        NEVER emits [AK_ifetch]/[AK_ttw], so the arm is dead.  [sail_step]
        therefore REQUIRES [ak_coh = false] on every RAM read, and the
        bracket carries that as the [sail_shaped] premise (the [no_coh_reads]
        of the task statement, folded into the one shape predicate).

    (e) EXCLUSIVE ACCESSES ONLY EVER APPEAR FUSED.  The plain-store arm
        requires [ak_latest = false], so a conditional (store-exclusive)
        write is NOT steppable on its own: it can only be consumed as the
        write half of the fused arm.  [sail_shaped] demands the matching
        shape — every exclusive [MemRead] node's continuation reaches, through
        register/trace/choice code ONLY, a conditional [MemWrite] to the same
        address and of the same width.  This, plus [nz_writes]-style nonzero
        widths, is the whole content of [sail_shaped]; it is the caller's
        obligation exactly as [WeakInterpProj.nz_writes] is.

    (f) THE BRACKET IS PER-AGENT AND FRAMED.  [wrun_sail_bracket] is stated
        over an arbitrary agent list [ags] with agent [i]'s slot pinned and
        every other slot framed: the conclusion is an [rtc] between
        configurations differing only by [<[i := …]>].  A single-agent
        configuration is the [ags := [ag]], [i := 0] instance.

    (g) WHAT IS NOT PROVED HERE.  The bracket is the ⇒ direction only (a
        [wrun] execution induces a [sail_step] sequence).  The ⇐ direction
        (every completed [sail_step] sequence is a [wrun]) is NOT stated: the
        composition needs only ⇒, and ⇐ additionally needs a determinism
        argument for the fused arm's silent prefix.  Also NOT here: the
        [WeakLang.wprim_step] ⇔ statement over [wgstate] (multi-hart global
        state), which is the composition file's job — [sail_instr_bracket]
        is stated on the [wmstate] that [WeakLang.whart_view] produces
        ([sail_instr_bracket_single] is its one-agent instance).

    DEPENDENCIES: [WeakInterp] (hence the Sail model), [WeakInterpProj]
    ([wbytes]), [WeakPromise]/[WeakPromiseFact]/[WeakPromiseBridge], and —
    for the final instantiation only — [RiscvLang] ([riscv_step]).

    NOTE ON NAMES.  [WeakPromise] and [WeakAxiomatic] (pulled in by
    [WeakInterpProj]/[WeakPromiseBridge]) both export [LLoad]/[LStore]/
    [LFence]/[LRmw]; every occurrence below is QUALIFIED
    [WeakPromise.LLoad] &c. *)
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakInterp WeakInterpProj.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The program state

    The residual monad ([None] = at an instruction boundary), the register
    file (what [wrun] threads through [wm_regs]), the remaining MMIO oracle
    entries, and the parked second fence of a [fence.tso]. *)

(** One oracle entry: the little-endian bytes one device read returns. *)
Definition dstream := list (list (bv 8)).

Record psail := PSail {
  sp_m     : option (M unit);
  sp_regs  : regstate;
  sp_dev   : dstream;
  sp_fence : option (bool * bool * bool * bool);
}.
Add Printing Constructor psail.

(** The silent one-step relation on (residual monad, registers) used by the
    fused RMW arm: the outcomes that may sit BETWEEN an AMO's read half and
    its write half.  No memory, no barrier — those would break the fusion
    (and the model never emits them there). *)
Definition silent1 (c c' : M unit * regstate) : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.RegRead r _      => λ k, c' = (k (register_lookup r c.2), c.2)
       | Interface.RegWrite r _ v   => λ k, c' = (k tt, register_set r v c.2)
       | Interface.InstrAnnounce _  => λ k, c' = (k tt, c.2)
       | Interface.BranchAnnounce _ _ => λ k, c' = (k tt, c.2)
       | Interface.CacheOp _        => λ k, c' = (k tt, c.2)
       | Interface.TlbOp _          => λ k, c' = (k tt, c.2)
       | Interface.TakeException _  => λ k, c' = (k tt, c.2)
       | Interface.ReturnException _=> λ k, c' = (k tt, c.2)
       | Interface.TranslationStart _ => λ k, c' = (k tt, c.2)
       | Interface.TranslationEnd _ => λ k, c' = (k tt, c.2)
       | Interface.CycleCount       => λ k, c' = (k tt, c.2)
       | Interface.Message _        => λ k, c' = (k tt, c.2)
       | Interface.GetCycleCount    => λ k, c' = (k 0%Z, c.2)
       | Interface.Choose _         => λ k, ∃ ch, c' = (k ch, c.2)
       | _ => λ _, False
       end) k
  end.

Definition silent_run : relation (M unit * regstate) := rtc silent1.

(** The write half of a fused RMW: [m] is a conditional [MemWrite] node to
    RAM, writing [data] at [base] with release annotation [rl], continuing
    as [m'].  (The [ak_latest = true] conjunct is what makes this arm
    disjoint from the plain-store arm — delta (e).) *)
Definition wr_node (m : M unit) (rl : bool) (base : Z) (data : list (bv 8))
    (m' : M unit) : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemWrite n req => λ k,
           dev_addr (Interface.WriteReq.pa req) = false ∧
           n ≠ 0%N ∧
           ak_latest (classify (Interface.WriteReq.access_kind req)) = true ∧
           rl = ak_sync (classify (Interface.WriteReq.access_kind req)) ∧
           base = pa_z (Interface.WriteReq.pa req) ∧
           data = wbytes n (Interface.WriteReq.value req) ∧
           m' = k (inl None)
       | _ => λ _, False
       end) k
  end.

(** The barrier table: which label a barrier emits, and what it parks.
    Compare [WeakInterp.barrier_post] line for line. *)
Definition barrier_lbl (b : barrier_kind)
    : wlabel * option (bool * bool * bool * bool) :=
  match b with
  | Barrier_RISCV_rw_rw => (WeakPromise.LFence true  true  true  true , None)
  | Barrier_RISCV_r_rw  => (WeakPromise.LFence true  false true  true , None)
  | Barrier_RISCV_r_r   => (WeakPromise.LFence true  false true  false, None)
  | Barrier_RISCV_rw_w  => (WeakPromise.LFence true  true  false true , None)
  | Barrier_RISCV_w_w   => (WeakPromise.LFence false true  false true , None)
  | Barrier_RISCV_w_rw  => (WeakPromise.LFence false true  true  true , None)
  | Barrier_RISCV_rw_r  => (WeakPromise.LFence true  true  true  false, None)
  | Barrier_RISCV_r_w   => (WeakPromise.LFence true  false false true , None)
  | Barrier_RISCV_w_r   => (WeakPromise.LFence false true  true  false, None)
  | Barrier_RISCV_tso   => (WeakPromise.LFence true  false true  false,
                            Some (true, true, false, true))
  | Barrier_RISCV_i     => (WeakPromise.LSilent, None)
  end.

(* ====================================================================== *)
(** ** 2. The step relation

    [sail_mstep m rs d l p'] is the step of a hart whose residual monad is
    [m], registers [rs], oracle [d] and no parked fence.  Every arm sits
    opposite the [wrun] arm of the same outcome. *)

Definition sail_mstep (m : M unit) (rs : regstate) (d : dstream)
    (l : wlabel) (p' : psail) : Prop :=
  match m with
  | Interface.Ret _ =>
      (* end of the instruction: back to the boundary *)
      l = WeakPromise.LSilent ∧ p' = PSail None rs d None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.RegRead r _ => λ k,
           l = WeakPromise.LSilent ∧
           p' = PSail (Some (k (register_lookup r rs))) rs d None
       | Interface.RegWrite r _ v => λ k,
           l = WeakPromise.LSilent ∧
           p' = PSail (Some (k tt)) (register_set r v rs) d None
       | Interface.MemRead n req => λ k,
           if dev_addr (Interface.ReadReq.pa req)
           then
             (* MMIO: silent, one oracle entry consumed *)
             l = WeakPromise.LSilent ∧
             ∃ (e : list (bv 8)) (d' : dstream) (w : bv (8 * n)),
               d = e :: d' ∧ length e = N.to_nat n ∧
               (∀ j : nat, (j < N.to_nat n)%nat → e !! j = Some (nth_byte w j)) ∧
               p' = PSail (Some (k (inl (w, None)))) rs d' None
           else
             ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
             match l with
             | WeakPromise.LLoad aq false base tvs =>
                 (* a PLAIN load: the label fixes only the VALUES that flow
                    to the continuation; admissibility is the machine's job *)
                 ak_latest (classify (Interface.ReadReq.access_kind req)) = false ∧
                 aq = ak_sync (classify (Interface.ReadReq.access_kind req)) ∧
                 base = pa_z (Interface.ReadReq.pa req) ∧
                 length tvs = N.to_nat n ∧
                 ∃ w : bv (8 * n),
                   (∀ j : nat, (j < N.to_nat n)%nat →
                      tvs.*2 !! j = Some (nth_byte w j)) ∧
                   p' = PSail (Some (k (inl (w, None)))) rs d None
             | WeakPromise.LRmw aq rl base tvs data =>
                 (* THE FUSED ARM: exclusive read, silent prefix, conditional
                    write — one label *)
                 ak_latest (classify (Interface.ReadReq.access_kind req)) = true ∧
                 aq = ak_sync (classify (Interface.ReadReq.access_kind req)) ∧
                 base = pa_z (Interface.ReadReq.pa req) ∧
                 length tvs = N.to_nat n ∧ length data = N.to_nat n ∧
                 ∃ (w : bv (8 * n)) (m1 m2 : M unit) (rs1 : regstate),
                   (∀ j : nat, (j < N.to_nat n)%nat →
                      tvs.*2 !! j = Some (nth_byte w j)) ∧
                   silent_run (k (inl (w, None)), rs) (m1, rs1) ∧
                   wr_node m1 rl base data m2 ∧
                   p' = PSail (Some m2) rs1 d None
             | _ => False
             end
       | Interface.MemWrite n req => λ k,
           if dev_addr (Interface.WriteReq.pa req)
           then l = WeakPromise.LSilent ∧
                p' = PSail (Some (k (inl None))) rs d None
           else
             l = WeakPromise.LStore
                   (ak_sync (classify (Interface.WriteReq.access_kind req)))
                   (pa_z (Interface.WriteReq.pa req))
                   (wbytes n (Interface.WriteReq.value req)) ∧
             n ≠ 0%N ∧
             ak_latest (classify (Interface.WriteReq.access_kind req)) = false ∧
             p' = PSail (Some (k (inl None))) rs d None
       | Interface.Barrier b => λ k,
           l = (barrier_lbl b).1 ∧
           p' = PSail (Some (k tt)) rs d (barrier_lbl b).2
       | Interface.InstrAnnounce _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.BranchAnnounce _ _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.CacheOp _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.TlbOp _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.TakeException _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.ReturnException _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.TranslationStart _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.TranslationEnd _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.CycleCount => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.Message _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None
       | Interface.GetCycleCount => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k 0%Z)) rs d None
       | Interface.Choose _ => λ k,
           l = WeakPromise.LSilent ∧ ∃ c, p' = PSail (Some (k c)) rs d None
       | _ => λ _, False
       end) k
  end.

(** The LTS.  [next] is the instruction generator taken at a boundary —
    [RiscvLang.riscv_step] downstream (§6), kept a parameter so that the bulk
    of this file does not depend on the decoder. *)
Definition sail_step (next : bool → M unit)
    (p : psail) (l : wlabel) (p' : psail) : Prop :=
  match sp_fence p with
  | Some (pr, pw, sr, sw) =>
      (* the parked second fence of a [fence.tso]; nothing else may fire *)
      l = WeakPromise.LFence pr pw sr sw ∧
      p' = PSail (sp_m p) (sp_regs p) (sp_dev p) None
  | None =>
      match sp_m p with
      | None =>
          l = WeakPromise.LSilent ∧
          ∃ tick : bool,
            p' = PSail (Some (next tick)) (sp_regs p) (sp_dev p) None
      | Some m => sail_mstep m (sp_regs p) (sp_dev p) l p'
      end
  end.

(* ====================================================================== *)
(** ** 3. The Layer-1 side conditions

    Both are DEFINITIONAL — they are properties of how the arms are spelled,
    which is why the spelling above is load-bearing (worklist W2b finding
    (v)). *)

(** LAT-FREEDOM.  The only arm producing an [LLoad] pattern-matches [lat] at
    [false]; the fused arm's read half carries no [lat] at all.  So no
    latest-kind load is ever emitted — the hypothesis [WeakPromiseFact]'s
    front-loading theorem takes. *)
Theorem sail_lat_free next : lat_free_prog (sail_step next).
Proof.
  intros p aq base tvs p' H. rewrite /sail_step in H.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by destruct H as [? _]|].
  destruct (sp_m p) as [m|]; [|by destruct H as [? _]].
  destruct m as [y|T oc k]; [by destruct H as [? _]|].
  destruct oc; simpl in H;
    try (by destruct H as [? _]); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _); [by destruct H as [? _]|].
    by destruct H as [_ H].
  - (* MemWrite *)
    destruct (dev_addr _); by destruct H as [? _].
  - (* Barrier *)
    destruct b; by destruct H as [? _].
Qed.

(** TIMESTAMP-OBLIVIOUSNESS.  The load arm constrains [tvs] only through
    [length tvs] and [tvs.*2]; the continuation it hands the program is
    computed from the VALUES alone.  Retiming a load is therefore free —
    which is exactly what Layer 1 needs when it re-times a read against a
    reordered log. *)
Theorem sail_ts_oblivious next p aq lat base tvs tvs' p' :
  tvs.*2 = tvs'.*2 →
  sail_step next p (WeakPromise.LLoad aq lat base tvs) p' →
  sail_step next p (WeakPromise.LLoad aq lat base tvs') p'.
Proof.
  intros Heq H. rewrite /sail_step in H |- *.
  have Hlen : length tvs = length tvs'.
  { by rewrite -(length_fmap snd tvs) -(length_fmap snd tvs') Heq. }
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by destruct H as [? _]|].
  destruct (sp_m p) as [m|]; [|by destruct H as [? _]].
  destruct m as [y|T oc k]; [by destruct H as [? _]|].
  destruct oc; simpl in H |- *;
    try (by destruct H as [? _]); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _); [by destruct H as [? _]|].
    destruct H as [Hcoh H]. destruct lat; [done|].
    destruct H as (Hlat & Haq & Hbase & Hlt & w & Hw & Hp).
    split; [done|]. split_and!; [done|done|done|by rewrite -Hlen|].
    exists w. split; [|done]. intros j Hj. rewrite -Heq. by apply Hw.
  - (* MemWrite *)
    destruct (dev_addr _); by destruct H as [? _].
  - (* Barrier *)
    destruct b; by destruct H as [? _].
Qed.

(** The [LRmw] analogue: the read half's timestamps are retimed, the values
    read and the data written are fixed. *)
Theorem sail_ts_oblivious_rmw next p aq rl base tvs tvs' data p' :
  tvs.*2 = tvs'.*2 →
  sail_step next p (WeakPromise.LRmw aq rl base tvs data) p' →
  sail_step next p (WeakPromise.LRmw aq rl base tvs' data) p'.
Proof.
  intros Heq H. rewrite /sail_step in H |- *.
  have Hlen : length tvs = length tvs'.
  { by rewrite -(length_fmap snd tvs) -(length_fmap snd tvs') Heq. }
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by destruct H as [? _]|].
  destruct (sp_m p) as [m|]; [|by destruct H as [? _]].
  destruct m as [y|T oc k]; [by destruct H as [? _]|].
  destruct oc; simpl in H |- *;
    try (by destruct H as [? _]); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _); [by destruct H as [? _]|].
    destruct H as [Hcoh H].
    destruct H as (Hlat & Haq & Hbase & Hlt & Hld & w & m1 & m2 & rs1 & Hw & Hsil & Hwr & Hp).
    split; [done|]. split_and!; [done|done|done|by rewrite -Hlen|done|].
    exists w, m1, m2, rs1. split_and!; [|done|done|done].
    intros j Hj. rewrite -Heq. by apply Hw.
  - (* MemWrite *)
    destruct (dev_addr _); by destruct H as [? _].
  - (* Barrier *)
    destruct b; by destruct H as [? _].
Qed.

(* ====================================================================== *)
(** ** 4. The shape premise on the instruction monad

    [WeakInterpProj]'s [nz_writes] with two more conjuncts, all three of the
    same character (a property of the DECODED INSTRUCTION, discharged by the
    caller, vacuous for rv64d):

    - no coherent reads (delta (d): rv64d never emits [AK_ifetch]/[AK_ttw]);
    - no zero-width RAM write (else the log grows with a message no label can
      mirror — [WeakInterpProj] header (5));
    - EVERY exclusive [MemRead] is AMO-PAIRED: its continuation reaches, by
      register/trace/choice code only, a conditional [MemWrite] to the SAME
      address and width, and no conditional write occurs anywhere else
      (delta (e)).

    [amo_tail pa n m] is the second half of that pairing. *)
Fixpoint sail_shaped (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemRead n req => λ k,
           if dev_addr (Interface.ReadReq.pa req)
           then ∀ r, sail_shaped (k r)
           else
             ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
             (if ak_latest (classify (Interface.ReadReq.access_kind req))
              then ∀ w : bv (8 * n),
                     amo_tail (Interface.ReadReq.pa req) n (k (inl (w, None)))
              else ∀ r, sail_shaped (k r))
       | Interface.MemWrite n req => λ k,
           (if dev_addr (Interface.WriteReq.pa req) then True
            else n ≠ 0%N ∧
                 ak_latest (classify (Interface.WriteReq.access_kind req)) = false) ∧
           (∀ r, sail_shaped (k r))
       | _ => λ k, ∀ r, sail_shaped (k r)
       end) k
  end
with amo_tail (pa : Arch.pa) (n : N) (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemWrite n' req' => λ k,
           dev_addr (Interface.WriteReq.pa req') = false ∧
           Interface.WriteReq.pa req' = pa ∧ n' = n ∧ n' ≠ 0%N ∧
           ak_latest (classify (Interface.WriteReq.access_kind req')) = true ∧
           (∀ r, sail_shaped (k r))
       | Interface.MemRead _ _ => λ _, False
       | Interface.Barrier _ => λ _, False
       | _ => λ k, ∀ r, amo_tail pa n (k r)
       end) k
  end.

(* ====================================================================== *)
(** ** 5. Bracketing [wrun] against [WeakPromiseBridge.wp_pf_step]

    The pf machine is [WeakPromise]'s promise-free fragment — the fragment
    Layer 1's robustness statement runs on.  One [wrun] of an instruction
    monad by agent [i] becomes an [rtc] of pf steps of agent [i] ALONE, with
    every other agent framed. *)

(** The label's [(t, v)] pairs, from the interpreter's timestamp list and the
    word it read. *)
Definition mk_tvs (n : N) (ts : list nat) (w : bv (8 * n)) : list (nat * bv 8) :=
  zip ts (wbytes n w).

Lemma mk_tvs_length n ts (w : bv (8 * n)) :
  length ts = N.to_nat n → length (mk_tvs n ts w) = N.to_nat n.
Proof. intros H. rewrite /mk_tvs length_zip wbytes_length H. lia. Qed.

Lemma mk_tvs_fst n ts (w : bv (8 * n)) :
  length ts = N.to_nat n → (mk_tvs n ts w).*1 = ts.
Proof. intros H. apply fst_zip. rewrite wbytes_length H. lia. Qed.

Lemma mk_tvs_snd n ts (w : bv (8 * n)) :
  length ts = N.to_nat n → (mk_tvs n ts w).*2 = wbytes n w.
Proof. intros H. apply snd_zip. rewrite wbytes_length H. lia. Qed.

Lemma mk_tvs_lookup n ts (w : bv (8 * n)) j t v :
  mk_tvs n ts w !! j = Some (t, v) →
  (j < N.to_nat n)%nat ∧ t = ts !!! j ∧ v = nth_byte w j.
Proof.
  rewrite /mk_tvs /zip. intros [x [y (Heq & Hx & Hy)]]%lookup_zip_with_Some.
  simplify_eq/=.
  pose proof (lookup_lt_Some _ _ _ Hy) as Hlt. rewrite wbytes_length in Hlt.
  split_and!; [done|by rewrite (list_lookup_total_correct _ _ _ Hx)|].
  rewrite (wbytes_lookup n w j Hlt) in Hy. by simplify_eq.
Qed.

(** [wread_ok] ⟹ [read_ok] with the [lat] pinning dropped — the same sound
    weakening [WeakInterpProj] header (3) makes, here justified because the
    label the LTS emits is a PLAIN load. *)
Lemma wread_read_ok s ak pa n ts (w : bv (8 * n)) :
  ak_coh ak = false →
  wread_ok s ak pa n ts w →
  read_ok (wimg s) (wm_log s) (wm_ws s) (ak_sync ak) false (pa_z pa)
          (mk_tvs n ts w).
Proof.
  intros Hcoh (Hlen & Hb) j t v Hj.
  apply mk_tvs_lookup in Hj as (Hlt & -> & ->).
  pose proof (Hb j ltac:(lia)) as Hok.
  rewrite /wbyte_ok Hcoh in Hok. destruct Hok as (Hlb & Hrd & _).
  split_and!; [exact Hlb|exact Hrd|done].
Qed.

(** The [ak_latest] pinning is not dropped for the FUSED rmw: it is exactly
    what discharges [WeakPromise.excl_ok] at the fused top.  Nothing above
    [t] writes the byte, in particular nothing written by another agent. *)
Lemma wread_excl_ok (i : agent) s ak pa n ts (w : bv (8 * n)) :
  ak_coh ak = false → ak_latest ak = true →
  wread_ok s ak pa n ts w →
  excl_ok (wm_log s) i (pa_z pa) (mk_tvs n ts w) (S (length (wm_log s))).
Proof.
  intros Hcoh Hlat (Hlen & Hb) j t v Hj Hw.
  apply mk_tvs_lookup in Hj as (Hlt & -> & ->).
  pose proof (Hb j ltac:(lia)) as Hok.
  rewrite /wbyte_ok Hcoh in Hok. destruct Hok as (_ & _ & Hpin).
  apply (Hpin Hlat). replace (length (wm_log s)) with (S (length (wm_log s)) - 1)%nat by lia.
  by apply writes_in_by_writes_in in Hw.
Qed.

Section bracket.
  Context (next : bool → M unit) (i : agent).

  Implicit Types ags : list (wpagent psail).

  Lemma lookup_insert_i ags ag a :
    ags !! i = Some ag → (<[i := a]> ags) !! i = Some a.
  Proof. intros H. apply list_lookup_insert. exact (lookup_lt_Some _ _ _ H). Qed.

  (* ---- the five one-step wrappers, each collapsing the double insert ---- *)

  Lemma pf_silent ags ag p1 img log img' log' fin :
    ags !! i = Some ag →
    sail_step next (pa_st ag) WeakPromise.LSilent p1 →
    rtc (wp_pf_run (sail_step next))
        (WPCfg img log (<[i := WPAgent p1 (pa_ws ag) (pa_prom ag)]> ags))
        (WPCfg img' log'
           (<[i := fin]> (<[i := WPAgent p1 (pa_ws ag) (pa_prom ag)]> ags))) →
    rtc (wp_pf_run (sail_step next)) (WPCfg img log ags)
        (WPCfg img' log' (<[i := fin]> ags)).
  Proof.
    intros Hlk Hst Hrest. rewrite list_insert_insert in Hrest.
    eapply rtc_l; [|exact Hrest]. exists i, WeakPromise.LSilent.
    by eapply PFSilent.
  Qed.

  Lemma pf_fence ags ag pr pw sr sw p1 img log img' log' fin :
    ags !! i = Some ag →
    sail_step next (pa_st ag) (WeakPromise.LFence pr pw sr sw) p1 →
    rtc (wp_pf_run (sail_step next))
        (WPCfg img log
           (<[i := WPAgent p1 (fence_post (pa_ws ag) pr pw sr sw) (pa_prom ag)]> ags))
        (WPCfg img' log'
           (<[i := fin]>
              (<[i := WPAgent p1 (fence_post (pa_ws ag) pr pw sr sw) (pa_prom ag)]> ags))) →
    rtc (wp_pf_run (sail_step next)) (WPCfg img log ags)
        (WPCfg img' log' (<[i := fin]> ags)).
  Proof.
    intros Hlk Hst Hrest. rewrite list_insert_insert in Hrest.
    eapply rtc_l; [|exact Hrest]. exists i, (WeakPromise.LFence pr pw sr sw).
    by eapply PFFence.
  Qed.

  Lemma pf_load ags ag aq lat base tvs p1 img log img' log' fin :
    ags !! i = Some ag →
    sail_step next (pa_st ag) (WeakPromise.LLoad aq lat base tvs) p1 →
    read_ok img log (pa_ws ag) aq lat base tvs →
    rtc (wp_pf_run (sail_step next))
        (WPCfg img log
           (<[i := WPAgent p1 (load_post_run (pa_ws ag) aq base tvs.*1)
                      (pa_prom ag)]> ags))
        (WPCfg img' log'
           (<[i := fin]>
              (<[i := WPAgent p1 (load_post_run (pa_ws ag) aq base tvs.*1)
                         (pa_prom ag)]> ags))) →
    rtc (wp_pf_run (sail_step next)) (WPCfg img log ags)
        (WPCfg img' log' (<[i := fin]> ags)).
  Proof.
    intros Hlk Hst Hok Hrest. rewrite list_insert_insert in Hrest.
    eapply rtc_l; [|exact Hrest].
    exists i, (WeakPromise.LLoad aq lat base tvs). by eapply PFLoad.
  Qed.

  Lemma pf_store ags ag rl base data k p1 img log img' log' fin :
    ags !! i = Some ag →
    sail_step next (pa_st ag) (WeakPromise.LStore rl base data) p1 →
    data ≠ [] →
    rtc (wp_pf_run (sail_step next))
        (WPCfg img (log ++ [WMsg base data (Some i) k])
           (<[i := WPAgent p1
                     (store_post_run (pa_ws ag) rl base (length data)
                        (S (length log))) (pa_prom ag)]> ags))
        (WPCfg img' log'
           (<[i := fin]>
              (<[i := WPAgent p1
                        (store_post_run (pa_ws ag) rl base (length data)
                           (S (length log))) (pa_prom ag)]> ags))) →
    rtc (wp_pf_run (sail_step next)) (WPCfg img log ags)
        (WPCfg img' log' (<[i := fin]> ags)).
  Proof.
    intros Hlk Hst Hne Hrest. rewrite list_insert_insert in Hrest.
    eapply rtc_l; [|exact Hrest].
    exists i, (WeakPromise.LStore rl base data). by eapply PFStore.
  Qed.

  Lemma pf_rmw ags ag aq rl base tvs data k p1 img log img' log' fin :
    ags !! i = Some ag →
    sail_step next (pa_st ag) (WeakPromise.LRmw aq rl base tvs data) p1 →
    data ≠ [] →
    length tvs = length data →
    read_ok img log (pa_ws ag) aq false base tvs →
    excl_ok log i base tvs (S (length log)) →
    rtc (wp_pf_run (sail_step next))
        (WPCfg img (log ++ [WMsg base data (Some i) k])
           (<[i := WPAgent p1
                     (store_post_run (load_post_run (pa_ws ag) aq base tvs.*1)
                        rl base (length data) (S (length log)))
                     (pa_prom ag)]> ags))
        (WPCfg img' log'
           (<[i := fin]>
              (<[i := WPAgent p1
                        (store_post_run (load_post_run (pa_ws ag) aq base tvs.*1)
                           rl base (length data) (S (length log)))
                        (pa_prom ag)]> ags))) →
    rtc (wp_pf_run (sail_step next)) (WPCfg img log ags)
        (WPCfg img' log' (<[i := fin]> ags)).
  Proof.
    intros Hlk Hst Hne Hlen Hok Hex Hrest. rewrite list_insert_insert in Hrest.
    eapply rtc_l; [|exact Hrest].
    exists i, (WeakPromise.LRmw aq rl base tvs data). by eapply PFRmw.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The two mutually-inductive bracket statements

      [sail_bracket m]: running [m] to completion is a pf run ending at the
      residual [Interface.Ret x], with the interpreter's final log, [wstate]
      and registers.  The oracle stream the run consumes is EXISTENTIAL and
      is consumed exactly ([str ++ tail] in, [tail] out).

      [amo_bracket pa n m]: [m] is the tail of an AMO (an [amo_tail]); it
      reaches the conditional write by silent steps, and the REST of the
      instruction (after that write) is a pf run from the post-write
      configuration.  The fused [LRmw] step itself is taken by the caller —
      the read node — which is why this statement starts at the post-write
      log. *)

  Definition sail_bracket (m : M unit) : Prop :=
    ∀ (s : wmstate) (x : unit) (s' : wmstate),
      sail_shaped m →
      wrun (Some i) m s x s' →
      ∃ str : dstream,
        ∀ (tail : dstream) (prom : gset nat) ags,
          ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (str ++ tail) None)
                             (wm_ws s) prom) →
          rtc (wp_pf_run (sail_step next))
            (WPCfg (wimg s) (wm_log s) ags)
            (WPCfg (wimg s) (wm_log s')
               (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s') tail None)
                         (wm_ws s') prom]> ags)).

  Definition amo_bracket (pa : Arch.pa) (n : N) (m : M unit) : Prop :=
    ∀ (s : wmstate) (x : unit) (s' : wmstate),
      amo_tail pa n m →
      wrun (Some i) m s x s' →
      ∃ (m1 m2 : M unit) (rs1 : regstate) (rl : bool) (data : list (bv 8))
        (k : wm_class) (str : dstream),
        silent_run (m, wm_regs s) (m1, rs1) ∧
        wr_node m1 rl (pa_z pa) data m2 ∧
        length data = N.to_nat n ∧ data ≠ [] ∧
        (∀ (tail : dstream) (prom : gset nat) ags,
           ags !! i = Some (WPAgent (PSail (Some m2) rs1 (str ++ tail) None)
                              (store_post_run (wm_ws s) rl (pa_z pa) (length data)
                                 (S (length (wm_log s)))) prom) →
           rtc (wp_pf_run (sail_step next))
             (WPCfg (wimg s) (wm_log s ++ [WMsg (pa_z pa) data (Some i) k]) ags)
             (WPCfg (wimg s) (wm_log s')
                (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s') tail None)
                          (wm_ws s') prom]> ags))).

  Local Ltac sbr_silent :=
    match goal with
    | Hsh : ∀ _, sail_shaped _, Hrun : wrun _ _ _ _ _, IH : ∀ _, _ ∧ _ |- _ =>
        let str := fresh "str" in let Hch := fresh "Hch" in
        destruct (proj1 (IH _) _ _ _ (Hsh _) Hrun) as (str & Hch);
        exists str; intros tail prom ags Hlk;
        eapply pf_silent;
          [exact Hlk | by (rewrite /sail_step /=; split; reflexivity) |];
        apply Hch; by apply (lookup_insert_i _ _ _ Hlk)
    end.

  Local Ltac amo_silent :=
    match goal with
    | Hsh : ∀ _, amo_tail _ _ _, Hrun : wrun _ _ _ _ _, IH : ∀ _, _ ∧ _ |- _ =>
        let m1 := fresh "m1" in let m2 := fresh "m2" in
        let rs1 := fresh "rs1" in let rl := fresh "rl" in
        let data := fresh "data" in let str := fresh "str" in
        let kc := fresh "kc" in
        destruct (proj2 (IH _) _ _ _ _ _ (Hsh _) Hrun)
          as (m1 & m2 & rs1 & rl & data & kc & str & Hsil & Hwr & Hlen & Hne & Hch);
        exists m1, m2, rs1, rl, data, kc, str;
        split_and!; [|exact Hwr|exact Hlen|exact Hne|exact Hch];
        eapply rtc_l; [|exact Hsil]; by rewrite /silent1 /=
    end.

  (** THE CORE LEMMA (mutual induction over the monad, [WeakInterpProj]'s
      skeleton).  Both statements at once: the fused arm of the first needs
      the second at the read's continuation, and the write node of the second
      needs the first at the write's continuation. *)
  Lemma sail_bracket_all (m : M unit) :
    sail_bracket m ∧ ∀ pa n, amo_bracket pa n m.
  Proof.
    induction m as [y|T oc k IH].
    { split.
      - intros s x s' _ [-> ->]. exists []. intros tail prom ags Hlk.
        rewrite (list_insert_id _ _ _ Hlk). apply rtc_refl.
      - intros pa n s x s' Hamo. destruct Hamo. }
    split.
    - (* ---------------- sail_bracket ---------------- *)
      intros s x s' Hsh Hrun.
      destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                     |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hsh, Hrun;
        try (by sbr_silent); try (by exfalso; exact Hrun).
      { (* MemRead *)
        destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
        - (* MMIO: consume one oracle entry, silently *)
          destruct (dev_read (wm_dev s) (Interface.ReadReq.pa req) nn)
            as [[w d']|] eqn:Hdr; [|by exfalso; exact Hrun].
          destruct (proj1 (IH (inl (w, None))) _ _ _ (Hsh _) Hrun) as (str & Hch).
          exists (wbytes nn w :: str). intros tail prom ags Hlk.
          eapply pf_silent; [exact Hlk| |].
          + rewrite /sail_step /= Hd. split; [reflexivity|].
            exists (wbytes nn w), (str ++ tail), w. split_and!.
            * reflexivity.
            * apply wbytes_length.
            * intros j Hj. by apply wbytes_lookup.
            * reflexivity.
          + apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
        - destruct Hsh as (Hcoh & Hsh).
          destruct Hrun as (w & ts & Hok & Hrun).
          rewrite /wread_post Hcoh /= in Hrun.
          destruct (ak_latest (classify (Interface.ReadReq.access_kind req)))
            eqn:Hlat.
          + (* THE FUSED RMW *)
            destruct (proj2 (IH (inl (w, None))) (Interface.ReadReq.pa req) nn
                        _ _ _ (Hsh w) Hrun)
              as (m1 & m2 & rs1 & rl & data & kc & str & Hsil & Hwr & Hlend & Hne & Hch).
            exists str. intros tail prom ags Hlk.
            pose proof Hok as (Hlents & _).
            eapply pf_rmw.
            * exact Hlk.
            * rewrite /sail_step /= Hd. split; [exact Hcoh|].
              split_and!;
                [exact Hlat|reflexivity|reflexivity
                |exact (mk_tvs_length nn ts w Hlents)|exact Hlend|].
              exists w, m1, m2, rs1.
              split_and!; [|exact Hsil|exact Hwr|reflexivity].
              intros j Hj. rewrite (mk_tvs_snd nn ts w Hlents).
              by apply wbytes_lookup.
            * exact Hne.
            * rewrite (mk_tvs_length nn ts w Hlents) Hlend //.
            * exact (wread_read_ok s _ _ nn ts w Hcoh Hok).
            * exact (wread_excl_ok i s _ _ nn ts w Hcoh Hlat Hok).
            * rewrite (mk_tvs_fst nn ts w Hlents).
              apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
          + (* a plain load *)
            destruct (proj1 (IH (inl (w, None))) _ _ _ (Hsh _) Hrun)
              as (str & Hch).
            exists str. intros tail prom ags Hlk.
            pose proof Hok as (Hlents & _).
            eapply pf_load with (lat := false).
            * exact Hlk.
            * rewrite /sail_step /= Hd. split; [exact Hcoh|].
              split_and!;
                [exact Hlat|reflexivity|reflexivity
                |exact (mk_tvs_length nn ts w Hlents)|].
              exists w. split; [|reflexivity].
              intros j Hj. rewrite (mk_tvs_snd nn ts w Hlents).
              by apply wbytes_lookup.
            * exact (wread_read_ok s _ _ nn ts w Hcoh Hok).
            * rewrite (mk_tvs_fst nn ts w Hlents).
              apply Hch. by apply (lookup_insert_i _ _ _ Hlk). }
      { (* MemWrite *)
        destruct Hsh as (Hn & Hsh).
        destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
        - destruct (dev_write (wm_dev s) (Interface.WriteReq.pa req) nn
                      (Interface.WriteReq.value req)) as [d'|] eqn:Hdw;
            [|by exfalso; exact Hrun].
          destruct (proj1 (IH (inl None)) _ _ _ (Hsh _) Hrun) as (str & Hch).
          exists str. intros tail prom ags Hlk.
          eapply pf_silent; [exact Hlk| |].
          + rewrite /sail_step /= Hd. split; reflexivity.
          + apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
        - destruct Hn as (Hn0 & Hnlat).
          destruct (proj1 (IH (inl None)) _ _ _ (Hsh _) Hrun) as (str & Hch).
          exists str. intros tail prom ags Hlk.
          eapply pf_store.
          + exact Hlk.
          + rewrite /sail_step /= Hd. split_and!; [reflexivity|exact Hn0|exact Hnlat|reflexivity].
          + by apply wbytes_nonnil.
          + rewrite wbytes_length. apply Hch.
            by apply (lookup_insert_i _ _ _ Hlk). }
      { (* Barrier *)
        destruct (proj1 (IH tt) _ _ _ (Hsh _) Hrun) as (str & Hch).
        exists str. intros tail prom ags Hlk. destruct bk.
        1-9: eapply pf_fence;
               [exact Hlk | by (rewrite /sail_step /=; split; reflexivity) |];
             apply Hch; by apply (lookup_insert_i _ _ _ Hlk).
        - (* fence.tso: two chained fences, the second parked *)
          eapply pf_fence;
            [exact Hlk | by (rewrite /sail_step /=; split; reflexivity) |].
          eapply pf_fence.
          + by apply (lookup_insert_i _ _ _ Hlk).
          + rewrite /sail_step /=. split; reflexivity.
          + rewrite list_insert_insert. apply Hch.
            by apply (lookup_insert_i _ _ _ Hlk).
        - (* fence.i: no event *)
          eapply pf_silent;
            [exact Hlk | by (rewrite /sail_step /=; split; reflexivity) |].
          apply Hch. by apply (lookup_insert_i _ _ _ Hlk). }
      { (* Choose *)
        destruct Hrun as (c & Hrun).
        destruct (proj1 (IH c) _ _ _ (Hsh _) Hrun) as (str & Hch).
        exists str. intros tail prom ags Hlk.
        eapply pf_silent; [exact Hlk| |].
        - rewrite /sail_step /=. split; [reflexivity|]. by exists c.
        - apply Hch. by apply (lookup_insert_i _ _ _ Hlk). }
    - (* ---------------- amo_bracket ---------------- *)
      intros pa n s x s' Hsh Hrun.
      destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                     |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hsh, Hrun;
        try (by amo_silent); try (by exfalso; exact Hrun);
        try (by destruct Hsh).
      { (* the conditional write: the fused arm's second half *)
        destruct Hsh as (Hd & Hpa & Hn & Hn0 & Hlat & Hsh).
        rewrite Hd in Hrun. subst pa n.
        destruct (proj1 (IH (inl None)) _ _ _ (Hsh _) Hrun) as (str & Hch).
        exists (Interface.Next (Interface.MemWrite nn req) k), (k (inl None)),
               (wm_regs s), (ak_sync (classify (Interface.WriteReq.access_kind req))),
               (wbytes nn (Interface.WriteReq.value req)),
               (wm_class_of (classify (Interface.WriteReq.access_kind req))
                  (wm_ws s)), str.
        split_and!.
        - apply rtc_refl.
        - rewrite /wr_node. split_and!; [exact Hd|exact Hn0|exact Hlat|
                                         reflexivity|reflexivity|reflexivity|reflexivity].
        - apply wbytes_length.
        - by apply wbytes_nonnil.
        - rewrite wbytes_length. exact Hch. }
      { (* Choose *)
        destruct Hrun as (c & Hrun).
        destruct (proj2 (IH c) _ _ _ _ _ (Hsh _) Hrun)
          as (m1 & m2 & rs1 & rl & data & kc & str & Hsil & Hwr & Hlen & Hne & Hch).
        exists m1, m2, rs1, rl, data, kc, str.
        split_and!; [|exact Hwr|exact Hlen|exact Hne|exact Hch].
        eapply rtc_l; [|exact Hsil]. rewrite /silent1 /=. by exists c. }
  Qed.

  (** THE BRACKET.  One instruction monad, run by [wrun], IS a pf run of the
      one stepping agent. *)
  Theorem wrun_sail_bracket (m : M unit) s x s' :
    sail_shaped m →
    wrun (Some i) m s x s' →
    ∃ str : dstream,
      ∀ (tail : dstream) (prom : gset nat) ags,
        ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (str ++ tail) None)
                           (wm_ws s) prom) →
        rtc (wp_pf_run (sail_step next))
          (WPCfg (wimg s) (wm_log s) ags)
          (WPCfg (wimg s) (wm_log s')
             (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s') tail None)
                       (wm_ws s') prom]> ags)).
  Proof. apply (proj1 (sail_bracket_all m)). Qed.

End bracket.

(* ====================================================================== *)
(** ** 6. The real hart program

    [WeakLang.wprim_step]'s hart arm runs exactly one
    [wrun (Some (fin_to_nat cpu)) (riscv_step tick) (whart_view g cpu) u s'],
    so instantiating [next := RiscvLang.riscv_step] closes the loop: at an
    instruction boundary the LTS picks a [tick] and loads the loop body, and
    at the residual [Interface.Ret] it returns to the boundary.  Both are
    [LSilent] steps, so the label sequence is unchanged — the bracket below
    is [wrun_sail_bracket] with a silent step glued on each end.

    (This is the [wmstate]-level statement.  Lifting it to [wgstate] — one
    [WeakLang] prim_step of hart [cpu] against the multi-hart configuration —
    belongs to the composition file: it is where [whart_view]/[whart_write]
    and the other harts' framing are handled.) *)
Require Import RiscvLang.

Section instr.
  Context (i : agent).

  Lemma pf_silent_last ags p0 p1 ws prom img log :
    (i < length ags)%nat →
    sail_step riscv_step p0 WeakPromise.LSilent p1 →
    rtc (wp_pf_run (sail_step riscv_step))
        (WPCfg img log (<[i := WPAgent p0 ws prom]> ags))
        (WPCfg img log (<[i := WPAgent p1 ws prom]> ags)).
  Proof.
    intros Hlt Hst. eapply rtc_l; [|apply rtc_refl].
    exists i, WeakPromise.LSilent.
    have Hlk : (<[i := WPAgent p0 ws prom]> ags) !! i = Some (WPAgent p0 ws prom)
      by apply list_lookup_insert.
    have Hstep := PFSilent (sail_step riscv_step) i
        (WPCfg img log (<[i := WPAgent p0 ws prom]> ags))
        (WPAgent p0 ws prom) p1 Hlk Hst.
    simpl in Hstep. rewrite list_insert_insert in Hstep. exact Hstep.
  Qed.

  (** ONE INSTRUCTION, boundary to boundary. *)
  Theorem sail_instr_bracket (tick : bool) s x s' :
    sail_shaped (riscv_step tick) →
    wrun (Some i) (riscv_step tick) s x s' →
    ∃ str : dstream,
      ∀ (tail : dstream) (prom : gset nat) (ags : list (wpagent psail)),
        ags !! i = Some (WPAgent (PSail None (wm_regs s) (str ++ tail) None)
                           (wm_ws s) prom) →
        rtc (wp_pf_run (sail_step riscv_step))
          (WPCfg (wimg s) (wm_log s) ags)
          (WPCfg (wimg s) (wm_log s')
             (<[i := WPAgent (PSail None (wm_regs s') tail None)
                       (wm_ws s') prom]> ags)).
  Proof.
    intros Hsh Hrun.
    destruct (wrun_sail_bracket riscv_step i (riscv_step tick) s x s' Hsh Hrun)
      as (str & Hch).
    exists str. intros tail prom ags Hlk.
    have Hlt : (i < length ags)%nat by exact (lookup_lt_Some _ _ _ Hlk).
    eapply pf_silent.
    - exact Hlk.
    - rewrite /sail_step /=. split; [reflexivity|]. by exists tick.
    - eapply rtc_transitive.
      + apply Hch. apply list_lookup_insert. exact Hlt.
      + apply pf_silent_last; [by rewrite length_insert|].
        rewrite /sail_step /=. split; reflexivity.
  Qed.

End instr.

(** The ONE-AGENT instance: the configuration shape
    [WPCfg img log [WPAgent p ws ∅]] the W5 composition starts from
    ([<[0 := a]> [b]] reduces to [[a]], so this is [sail_instr_bracket] read
    at [i := 0] with a singleton agent list). *)
Corollary sail_instr_bracket_single (tick : bool) s x s' :
  sail_shaped (riscv_step tick) →
  wrun (Some 0%nat) (riscv_step tick) s x s' →
  ∃ str : dstream,
    ∀ (tail : dstream) (prom : gset nat),
      rtc (wp_pf_run (sail_step riscv_step))
        (WPCfg (wimg s) (wm_log s)
           [WPAgent (PSail None (wm_regs s) (str ++ tail) None) (wm_ws s) prom])
        (WPCfg (wimg s) (wm_log s')
           [WPAgent (PSail None (wm_regs s') tail None) (wm_ws s') prom]).
Proof.
  intros Hsh Hrun.
  destruct (sail_instr_bracket 0%nat tick s x s' Hsh Hrun) as (str & Hch).
  exists str. intros tail prom.
  apply (Hch tail prom
           [WPAgent (PSail None (wm_regs s) (str ++ tail) None) (wm_ws s) prom]).
  reflexivity.
Qed.
