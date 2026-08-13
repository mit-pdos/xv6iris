(** * WeakSailLTS.v — the EVENT-LEVEL Sail program LTS (M6 / W5)

    [WeakPromise.v]'s machine is parametric in an abstract per-agent program
    LTS [pstep : P → wlabel → P → Prop]; the M6 robustness theorem (Layer 1)
    is stated over that parameter.  THIS FILE IS THE INSTANTIATION the W5
    composition needs: [psail] — the residual instruction monad plus the
    hart's register file and its MMIO oracle stream — with [sail_step]
    mirroring [WeakInterp.wrun]'s arms ONE LABEL PER MEMORY EVENT.

    Three things are delivered:

    (1) the LTS ([psail], [sail_step] — with the PER-HART DEVICE FABRIC
        [sp_dev] and the INTERRUPT oracle [sp_irq]) and its two Layer-1 side conditions —
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

    (b) THE PER-HART DEVICE FABRIC ([sp_dev : dev_state]).  [wpcfg] has no
        device component (design decision recorded in the W5 notes block: the
        retained MMIO-ordering assumption covers the private-fabric ↔
        real-device seam), so device accesses are served from a per-agent
        COPY OF THE DEVICE AUTOMATON carried INSIDE the program state, and are
        silent.

        THIS REPLACES AN EARLIER ORACLE STREAM ([sp_dev : dstream]), and the
        replacement is a soundness fix, not a convenience.  A positional
        stream needs a consistency premise ("this stream is what the device
        would have answered") that, to be usable at all, had to hold ALONG
        EVERY PATH of the instruction monad — and [WeakInterp]'s RAM reads
        quantify over every read value, including the FETCHED WORD and every
        page-walk PTE.  One stream would then have to serve, from one device
        state, every device access every junk fetch decodes to along every
        junk-but-valid translation path: two fetched words decoding to [lw]
        and [lb] at the same VA demand the same stream head have length 4 and
        1.  The ∀-path premise is therefore UNSATISFIABLE at essentially every
        record (2026-08-13 finding); the only oracle that can answer an
        arbitrary request sequence is the device automaton itself, so that is
        what the hart now carries.

        The accessors are TOTALIZED ([dev_read_t]/[dev_write_t] below):
        an access [dev_read]/[dev_write] does not decode (bad width or
        unmapped offset inside a device window) returns junk and leaves the
        fabric alone, rather than being stuck.  Modelling undefined device
        behaviour as "anything" rather than "nothing" is what makes the
        device arms of this LTS total — [sail_step] never gets stuck at a
        device access, and no per-path premise is needed to know that.  The
        residual seam is now just an EQUALITY: the hart's private fabric
        agrees with the machine's at each hart segment
        ([WeakComposeLang]'s [wl_lift]).

    (b') THE INTERRUPT ORACLE ([sp_irq], [irq_deliver]; L0(b) of
        [claude-notes/completed/weak-memory-lift.md], landed 2026-08-12).
        [RiscvLang.plic_step] writes ANOTHER agent's register file
        ([PlicStepWire] sets hart [c]'s [sig_seip] from [dev_seip]), which a
        per-agent LTS whose only shared channel is the log cannot express at
        all — the gap the lift plan names.  The fix is a SECOND per-agent
        oracle stream, [sp_irq : istream], and one silent arm [irq_deliver]
        that consumes an entry and installs it in [sig_seip].  So a
        [plic_step] of the real machine maps to ONE [LSilent] pf step of the
        hart it targets, and nothing else in this file changes.

        WHY THE ARM WRITES THE REGISTER rather than the alternative shape
        the plan floated (oracle-FED READS of the interrupt-pending CSRs,
        with [sp_regs] not consulted there).  Two reasons, and the second is
        decisive.  (1) The value type of a [RegRead] is [type_of_register r],
        so an oracle-fed read arm needs a dependent match over the [register]
        family just to give the stream a type — invasive, and it would have
        to be mirrored in [silent1] (the fused-RMW window) as well.  (2) An
        oracle-fed read lets [sp_regs] DRIFT from the interpreter's
        [wm_regs], and [sail_instr_bracket] pins them equal at every
        instruction boundary ([PSail None (wm_regs s) …]); the whole lift
        rests on that equation.  Delivering into the register file keeps it,
        and it is the more faithful reading anyway — [plic_step] IS a
        register write.

        SCOPE, honestly: (i) the designated register is [sig_seip], the
        S-mode external pin [RiscvLang.plic_step] actually drives (the
        M-mode [sig_meip] would be a second entry of the same shape, and is
        not wired by [plic_step]); (ii) the arm is GATED by [sp_fence], so
        no delivery separates the two halves of a [fence.tso] (delta (c));
        (iii) [silent1] is unchanged, so no delivery happens inside a fused
        AMO window — that window is register/choice code and an interrupt
        arriving there is unobservable to the AMO.  A delivery is otherwise
        admissible at ANY point, which over-approximates the real PLIC (it
        only ever writes the current pin level); that is the safe direction
        for the conclusion, and it strengthens the declared premise exactly
        as the MMIO oracle already does — seam (4).

    (c) THE PENDING SECOND FENCE.  [WeakInterp.barrier_post] makes
        [fence.tso] TWO chained [fence_post]s, but a [wlabel] carries one
        fence.  [sail_step] emits the FIRST fence (r,r) AND TAKES THE
        CONTINUATION [k tt] in the same step, parking the second fence
        (rw,w) in [sp_fence]; the next step emits it and clears the field,
        leaving [sp_m] alone.  While [sp_fence] is set NO other arm can
        fire — the outer match on [sp_fence] gates everything — so the two
        fences cannot be separated by another event of this agent.
        [fence.i] is [LSilent] ([barrier_post] is the identity on it).
        (The interrupt arm of (b') is gated by the same outer match, so it
        cannot fire between them either.)

    (d) COHERENT READS ARE A STUCK ARM, NOT A SILENT ONE.  A read with
        [ak_coh = true] (ifetch / page-table walk) would want [lat = true],
        which lat-freedom forbids; [WeakInterp] §3's finding (1) says rv64d
        NEVER emits [AK_ifetch]/[AK_ttw], so the arm is dead.  [sail_step]
        therefore REQUIRES [ak_coh = false] on every RAM read, and the
        bracket carries that as the [sail_shaped] premise (the [no_coh_reads]
        of the task statement, folded into the one shape predicate).

    (e) AN EXCLUSIVE WINDOW EITHER FUSES OR IS ABANDONED — AND BOTH ARE ONE
        STEP.  The plain-store arm requires [ak_latest = false], so a
        conditional (store-exclusive) write is NOT steppable on its own: it
        can only be consumed as the write half of the FUSED arm.  But real
        hardware executes a bare [lr] with no [sc], a FAILING [sc], an
        [amocas] whose comparison misses, and a page-walk whose exclusive PTE
        read errors out — every one of which ABANDONS the window (stage C1
        finding (O2); [WeakShape] §7c lists the three model sites).  Fusing
        was the only arm, so all of those were STUCK: a machine coverage gap,
        not merely a predicate bug.

        The fix is the BARE EXCLUSIVE-READ ARM, the second disjunct of the
        [LLoad] case of [sail_mstep]'s RAM [MemRead]: an [ak_latest] read may
        also step as a PLAIN load ([lat := false] — an abandoned reservation
        read has ordinary load semantics, and lat-freedom (§3) is preserved),
        and — exactly as the fused arm brackets read/silent-window/write into
        one [LRmw] — it brackets read/silent-window/[Interface.Ret] into one
        [LLoad], landing the agent at the END of the instruction.  That is
        not a convenience: it is what [amo_tail] already says, since an
        abandoned window admits no further memory access and no barrier
        before the instruction ends.  It also keeps the residual invariants
        of the completion kit unchanged — after a bare step the residual is
        [Interface.Ret], which is trivially [sail_shaped] and [sail_live], so
        no window-mode residual ever exists.

        [sail_shaped] demands the matching shape — every exclusive [MemRead]
        node's continuation is an [amo_tail]: through register/trace/choice
        code ONLY (no read, no barrier) it either reaches a conditional
        [MemWrite] to the same address and of the same width, or reaches the
        end of the instruction.  This, plus [nz_writes]-style nonzero widths,
        is the whole content of [sail_shaped]; it is the caller's obligation
        exactly as [WeakInterpProj.nz_writes] is.

        The ⇐ direction cannot reconstruct a [wrun] from a block that used
        the bare arm (a [wrun]'s exclusive read is not a plain load), so it
        carries the run-local side condition [WeakSailLTS2.fused_blk],
        target-indexed exactly like [dev_ok_blk].

    (e'') …AND THE MIRROR IMAGE: A CONDITIONAL WRITE WITH NO EXCLUSIVE READ.
        Delta (e) covers an exclusive read whose window is abandoned.  The
        SYMMETRIC gap is a conditional ([AV_exclusive], [ak_latest = true])
        write with no exclusive read anywhere in the instruction — which is
        exactly what a STANDALONE [sc] is: [rv64d.execute_STORECON] issues
        [write_ram Write_RISCV_conditional …], and the lr/sc reservation
        lives in the model's PURE axioms ([load_reservation]/
        [match_reservation]/[valid_reservation]), not in a memory event, with
        the matching [lr] a DIFFERENT [riscv_step] (stage C3 finding (O4)).
        Through stage C3 both [sail_shaped]'s and [sail_mstep]'s window-CLOSED
        [MemWrite] arms demanded [ak_latest = false], so [∀ b, sail_shaped
        (riscv_step b)] was FALSE at every [sc] and the LTS was STUCK there —
        the same machine coverage gap as (e), on the write side.

        THE FIX IS ONE CONJUNCT IN EACH: the window-closed [MemWrite] arms of
        [sail_mstep] and [sail_shaped] accept ANY RAM write (the [n ≠ 0]
        conjunct stays; only [ak_latest = false] goes).  A standalone
        conditional write therefore steps as an ordinary
        [WeakPromise.LStore] — which is the honest reading, since a
        SUCCEEDING [sc] really does store, and the machine only GAINS
        behaviors (the safe direction, as in (e)).  Unlike (e) the arm is
        ONE STEP, not a bracket: there is no open window to abandon, so the
        residual after the write is the ordinary [k (inl None)] and every
        residual invariant ([WeakSailComplete.sail_shaped_res_step],
        [tail_complete]) goes through with the widened shape predicate.
        [amo_tail]'s write arm is UNCHANGED — inside an open window a
        [MemWrite] must still BE the closing conditional write to the same
        address and width.

        WHAT IT COSTS is again a ⇐-side side condition, and it is folded into
        the SAME predicate as (e)'s: [WeakSailLTS2.pf_solo_f] now also says
        the step is not taken from a standalone conditional-write node
        ([at_con_write]), so [fused_blk] reads "every exclusive access of the
        block is part of a fused RMW".  The reason a side condition is still
        needed even though [WeakInterp.wrun]'s write arm accepts a
        conditional write unchanged (it never inspects [ak_latest]) is the
        MESSAGE CLASS: [wrun] computes [WCexcl] there
        ([WeakInterp.wm_class_of]) while a pf [LStore] step carries
        [WeakSailLTS2.lbl_class], i.e. [WCrel]/[WCplain] — the logs would
        differ in that one inert field.  Per-image discharge, as for (e): the
        xv6 kernel uses [amoswap], not [sc].

    (e') THE ANSWERS THE SHAPE PREDICATES QUANTIFY OVER ARE THE ANSWERS THIS
        LTS SUPPLIES.  [sail_mstep]'s memory arms hand the continuation
        [inl (w, None)] (read) and [inl None] (write) and nothing else, so
        [sail_shaped]/[amo_tail] (and [WeakSailComplete.sail_live]) quantify
        over exactly those — NOT over the full answer type, whose abort
        branch [inr ab] the model answers with [exit tt] and which made
        [∀ b, sail_live (riscv_step b)] refutable (stage C1 finding (O1)).

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
    file (what [wrun] threads through [wm_regs]), the hart's private copy of
    the device fabric, and the parked second fence of a [fence.tso]. *)

(** THE TOTALIZED DEVICE ACCESSORS (delta (b)).  [DevModel.dev_read] /
    [dev_write] are PARTIAL — they decline a bad width or an undecoded offset
    inside a device window.  This LTS's device arms must be total (that is
    the whole point of carrying the automaton rather than a stream), so a
    declined access reads junk and leaves the fabric unchanged.  Both are
    defined HERE, not in [DevModel], so that [WeakInterp]'s [wrun] keeps the
    partial (stuck-on-undecoded) reading it has always had: the two coincide
    exactly on the accesses [wrun] can take, which is what the ⇐ bracket's
    [dev_ok] side condition records ([WeakSailLTS2] §2). *)
Definition dev_read_t (d : dev_state) (pa : Arch.pa) (n : N)
  : bv (8 * n) * dev_state :=
  match dev_read d pa n with
  | Some (w, d') => (w, d')
  | None => (bv_0 (8 * n), d)
  end.

Definition dev_write_t (d : dev_state) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) : dev_state :=
  default d (dev_write d pa n v).

Lemma dev_read_t_Some d pa n w d' :
  dev_read d pa n = Some (w, d') → dev_read_t d pa n = (w, d').
Proof. rewrite /dev_read_t. by intros ->. Qed.

Lemma dev_write_t_Some d pa n v d' :
  dev_write d pa n v = Some d' → dev_write_t d pa n v = d'.
Proof. rewrite /dev_write_t. by intros ->. Qed.

(** The whole-register-file update on a [wmstate].  ([WeakInterp.wset_reg] is
    the single-register one.)  The silent window an exclusive read opens moves
    NOTHING ELSE, so this is the only state change an ABANDONED window makes —
    which is what the bare arm's bracket records (delta (e)) and what the ⇐
    direction replays ([WeakSailLTS2] §4). *)
Definition wregs_set (s : wmstate) (rs : regstate) : wmstate :=
  WMState rs (wm_img s) (wm_log s) (wm_ws s) (wm_dev s).

Lemma wregs_set_id s : wregs_set s (wm_regs s) = s.
Proof. by destruct s. Qed.

(** THE INTERRUPT ORACLE (delta (b') below).  One entry is one delivery of an
    external interrupt pin to this hart — the value [RiscvLang.plic_step]'s
    [PlicStepWire] writes into the hart's [sig_seip].  Typed by the register
    itself so that no [mword] spelling is duplicated here. *)
Definition istream := list (type_of_register sig_seip).

Record psail := PSail {
  sp_m     : option (M unit);
  sp_regs  : regstate;
  sp_dev   : dev_state;
  sp_fence : option (bool * bool * bool * bool);
  sp_irq   : istream;
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
    [m], registers [rs], device fabric [d] and no parked fence.  Every arm
    sits opposite the [wrun] arm of the same outcome. *)

Definition sail_mstep (m : M unit) (rs : regstate) (d : dev_state)
    (iq : istream) (l : wlabel) (p' : psail) : Prop :=
  match m with
  | Interface.Ret _ =>
      (* end of the instruction: back to the boundary *)
      l = WeakPromise.LSilent ∧ p' = PSail None rs d None iq
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.RegRead r _ => λ k,
           l = WeakPromise.LSilent ∧
           p' = PSail (Some (k (register_lookup r rs))) rs d None iq
       | Interface.RegWrite r _ v => λ k,
           l = WeakPromise.LSilent ∧
           p' = PSail (Some (k tt)) (register_set r v rs) d None iq
       | Interface.MemRead n req => λ k,
           if dev_addr (Interface.ReadReq.pa req)
           then
             (* MMIO: silent and DETERMINISTIC — the hart's own fabric
                answers, totalized (delta (b)) *)
             l = WeakPromise.LSilent ∧
             p' = PSail
                    (Some (k (inl ((dev_read_t d (Interface.ReadReq.pa req) n).1,
                                   None))))
                    rs (dev_read_t d (Interface.ReadReq.pa req) n).2 None iq
           else
             ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
             match l with
             | WeakPromise.LLoad aq false base tvs =>
                 (* a PLAIN load: the label fixes only the VALUES that flow
                    to the continuation; admissibility is the machine's job *)
                 (ak_latest (classify (Interface.ReadReq.access_kind req)) = false ∧
                  aq = ak_sync (classify (Interface.ReadReq.access_kind req)) ∧
                  base = pa_z (Interface.ReadReq.pa req) ∧
                  length tvs = N.to_nat n ∧
                  ∃ w : bv (8 * n),
                    (∀ j : nat, (j < N.to_nat n)%nat →
                       tvs.*2 !! j = Some (nth_byte w j)) ∧
                    p' = PSail (Some (k (inl (w, None)))) rs d None iq)
                 ∨
                 (* THE BARE EXCLUSIVE READ (delta (e)): the window is
                    ABANDONED — the read half has ordinary load semantics
                    and the rest of the instruction is the silent window,
                    bracketed to the instruction's [Interface.Ret] exactly as
                    the fused arm brackets to its conditional write *)
                 (ak_latest (classify (Interface.ReadReq.access_kind req)) = true ∧
                  aq = ak_sync (classify (Interface.ReadReq.access_kind req)) ∧
                  base = pa_z (Interface.ReadReq.pa req) ∧
                  length tvs = N.to_nat n ∧
                  ∃ w : bv (8 * n),
                    (∀ j : nat, (j < N.to_nat n)%nat →
                       tvs.*2 !! j = Some (nth_byte w j)) ∧
                    ∃ (y : unit) (rs1 : regstate),
                      silent_run (k (inl (w, None)), rs) (Interface.Ret y, rs1) ∧
                      p' = PSail (Some (Interface.Ret y)) rs1 d None iq)
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
                   p' = PSail (Some m2) rs1 d None iq
             | _ => False
             end
       | Interface.MemWrite n req => λ k,
           if dev_addr (Interface.WriteReq.pa req)
           then l = WeakPromise.LSilent ∧
                p' = PSail (Some (k (inl None))) rs
                       (dev_write_t d (Interface.WriteReq.pa req) n
                          (Interface.WriteReq.value req)) None iq
           else
             (* ANY RAM write, conditional or not (delta (e'')): a standalone
                [sc] has no window to close, and its store is a real store *)
             l = WeakPromise.LStore
                   (ak_sync (classify (Interface.WriteReq.access_kind req)))
                   (pa_z (Interface.WriteReq.pa req))
                   (wbytes n (Interface.WriteReq.value req)) ∧
             n ≠ 0%N ∧
             p' = PSail (Some (k (inl None))) rs d None iq
       | Interface.Barrier b => λ k,
           l = (barrier_lbl b).1 ∧
           p' = PSail (Some (k tt)) rs d (barrier_lbl b).2 iq
       | Interface.InstrAnnounce _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.BranchAnnounce _ _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.CacheOp _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.TlbOp _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.TakeException _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.ReturnException _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.TranslationStart _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.TranslationEnd _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.CycleCount => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.Message _ => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k tt)) rs d None iq
       | Interface.GetCycleCount => λ k,
           l = WeakPromise.LSilent ∧ p' = PSail (Some (k 0%Z)) rs d None iq
       | Interface.Choose _ => λ k,
           l = WeakPromise.LSilent ∧ ∃ c, p' = PSail (Some (k c)) rs d None iq
       | _ => λ _, False
       end) k
  end.

(** THE INTERRUPT-DELIVERY ARM (delta (b')).  The environment — concretely
    [RiscvLang.plic_step]'s [PlicStepWire], which writes ANOTHER agent's
    register file — raises or lowers this hart's external-interrupt pin.  It
    is SILENT (no memory event, no log, no [wstate] move) and consumes one
    entry of the interrupt oracle [sp_irq].

    Whether this arm has fired is invisible to every other arm: reads of the
    pin go through the ordinary [RegRead] path, which is what keeps
    [sp_regs] equal to the interpreter's [wm_regs] at every instruction
    boundary — see delta (b') for why THAT, and not an oracle-fed CSR read,
    is the right shape here. *)
Definition irq_deliver (p : psail) (l : wlabel) (p' : psail) : Prop :=
  l = WeakPromise.LSilent ∧
  ∃ (v : type_of_register sig_seip) (iq : istream),
    sp_irq p = v :: iq ∧
    p' = PSail (sp_m p) (register_set sig_seip v (sp_regs p)) (sp_dev p)
               (sp_fence p) iq.

(** The LTS.  [next] is the instruction generator taken at a boundary —
    [RiscvLang.riscv_step] downstream (§6), kept a parameter so that the bulk
    of this file does not depend on the decoder. *)
Definition sail_step (next : bool → M unit)
    (p : psail) (l : wlabel) (p' : psail) : Prop :=
  match sp_fence p with
  | Some (pr, pw, sr, sw) =>
      (* the parked second fence of a [fence.tso]; nothing else may fire *)
      l = WeakPromise.LFence pr pw sr sw ∧
      p' = PSail (sp_m p) (sp_regs p) (sp_dev p) None (sp_irq p)
  | None =>
      irq_deliver p l p'
      ∨ match sp_m p with
        | None =>
            l = WeakPromise.LSilent ∧
            ∃ tick : bool,
              p' = PSail (Some (next tick)) (sp_regs p) (sp_dev p) None
                     (sp_irq p)
        | Some m => sail_mstep m (sp_regs p) (sp_dev p) (sp_irq p) l p'
        end
  end.

(* ====================================================================== *)
(** ** 3. The Layer-1 side conditions

    Both are DEFINITIONAL — they are properties of how the arms are spelled,
    which is why the spelling above is load-bearing (worklist W2b finding
    (v)). *)

(** LAT-FREEDOM.  Both arms producing an [LLoad] — the plain load and the
    BARE exclusive read (delta (e)) — pattern-match [lat] at [false]; the
    fused arm's read half carries no [lat] at all.  So no latest-kind load is
    ever emitted — the hypothesis [WeakPromiseFact]'s front-loading theorem
    takes. *)
Theorem sail_lat_free next : lat_free_prog (sail_step next).
Proof.
  intros p aq base tvs p' H. rewrite /sail_step in H.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by destruct H as [? _]|].
  destruct H as [Hirq|H]; [by destruct Hirq as [? _]|].
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
  destruct H as [Hirq|H]; [by destruct Hirq as [? _]|]. right.
  destruct (sp_m p) as [m|]; [|by destruct H as [? _]].
  destruct m as [y|T oc k]; [by destruct H as [? _]|].
  destruct oc; simpl in H |- *;
    try (by destruct H as [? _]); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _); [by destruct H as [? _]|].
    destruct H as [Hcoh H]. destruct lat; [done|].
    split; [done|].
    destruct H as [(Hlat & Haq & Hbase & Hlt & w & Hw & Hp)
                  |(Hlat & Haq & Hbase & Hlt & w & Hw & y & rs1 & Hsil & Hp)].
    + left. split_and!; [done|done|done|by rewrite -Hlen|].
      exists w. split; [|done]. intros j Hj. rewrite -Heq. by apply Hw.
    + right. split_and!; [done|done|done|by rewrite -Hlen|].
      exists w. split; [intros j Hj; rewrite -Heq; by apply Hw|].
      by exists y, rs1.
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
  destruct H as [Hirq|H]; [by destruct Hirq as [? _]|]. right.
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
      mirror — [WeakInterpProj] header (5)).  Nothing else is asked of a RAM
      write: a CONDITIONAL one with no exclusive read in the instruction (a
      standalone [sc]) is admitted and steps as a plain store (delta (e''));
    - EVERY exclusive [MemRead] OPENS A WINDOW: its continuation crosses, by
      register/trace/choice code only, either to a conditional [MemWrite] to
      the SAME address and width (the window CLOSES — the fused arm) or to
      the end of the instruction (the window is ABANDONED — the bare arm),
      and NO OTHER memory access or barrier occurs inside the window
      (delta (e)).  Outside a window a conditional write is ordinary
      (delta (e'')).

    [amo_tail pa n m] is that window.  Its [Interface.Ret] arm is [True]: a
    window MAY be abandoned (stage C1 finding (O2) — [execute_LOADRES],
    [execute_AMO]'s fault/mismatch arms and [update_and_write_pte]'s error
    arms all do), and the LTS's bare arm is what steps such a tail.  What the
    window still forbids is what would make the abandoned tail unsteppable or
    the fused bracket unsound: no [MemRead], no [Barrier], and any [MemWrite]
    at all must BE the closing conditional write.

    Every ∀ over an answer is over the answers [sail_mstep] SUPPLIES —
    [inl (w, None)] and [inl None] (delta (e')). *)
Fixpoint sail_shaped (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemRead n req => λ k,
           if dev_addr (Interface.ReadReq.pa req)
           then ∀ w : bv (8 * n), sail_shaped (k (inl (w, None)))
           else
             ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
             (if ak_latest (classify (Interface.ReadReq.access_kind req))
              then ∀ w : bv (8 * n),
                     amo_tail (Interface.ReadReq.pa req) n (k (inl (w, None)))
              else ∀ w : bv (8 * n), sail_shaped (k (inl (w, None))))
       | Interface.MemWrite n req => λ k,
           (* ANY RAM write with a nonzero width — including a STANDALONE
              conditional one (delta (e'')) *)
           (if dev_addr (Interface.WriteReq.pa req) then True
            else n ≠ 0%N) ∧
           sail_shaped (k (inl None))
       | _ => λ k, ∀ r, sail_shaped (k r)
       end) k
  end
with amo_tail (pa : Arch.pa) (n : N) (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemWrite n' req' => λ k,
           dev_addr (Interface.WriteReq.pa req') = false ∧
           Interface.WriteReq.pa req' = pa ∧ n' = n ∧ n' ≠ 0%N ∧
           ak_latest (classify (Interface.WriteReq.access_kind req')) = true ∧
           sail_shaped (k (inl None))
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
      residual [Interface.Ret x], with the interpreter's final log, [wstate],
      registers AND DEVICE FABRIC.  The agent starts with the interpreter's
      device state ([wm_dev s]) and ends with the interpreter's ([wm_dev s']);
      there is no existential stream any more (delta (b)) — the two sides
      compute the same answers because [wrun] took every device access it
      reached, so [dev_read]/[dev_write] said [Some] there and the totalized
      accessors agree.

      [amo_bracket pa n m]: [m] is an open exclusive window (an [amo_tail]),
      and the run inside it goes ONE OF TWO WAYS (delta (e)).  EITHER it
      reaches the conditional write by silent steps, and the REST of the
      instruction (after that write) is a pf run from the post-write
      configuration — the fused [LRmw] step itself is taken by the caller,
      the read node, which is why that disjunct starts at the post-write log.
      OR the window is ABANDONED: the run reaches [Interface.Ret] by silent
      steps alone, so it touched nothing but the register file, and the
      caller takes the BARE arm — which brackets the whole window, so this
      disjunct carries no run at all. *)

  Definition sail_bracket (m : M unit) : Prop :=
    ∀ (s : wmstate) (x : unit) (s' : wmstate),
      sail_shaped m →
      wrun (Some i) m s x s' →
      ∀ (iq : istream) (prom : gset nat) ags,
        ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (wm_dev s) None iq)
                           (wm_ws s) prom) →
        rtc (wp_pf_run (sail_step next))
          (WPCfg (wimg s) (wm_log s) ags)
          (WPCfg (wimg s) (wm_log s')
             (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s')
                                (wm_dev s') None iq)
                       (wm_ws s') prom]> ags)).

  Definition amo_bracket (pa : Arch.pa) (n : N) (m : M unit) : Prop :=
    ∀ (s : wmstate) (x : unit) (s' : wmstate),
      amo_tail pa n m →
      wrun (Some i) m s x s' →
      (∃ (m1 m2 : M unit) (rs1 : regstate) (rl : bool) (data : list (bv 8))
         (k : wm_class),
         silent_run (m, wm_regs s) (m1, rs1) ∧
         wr_node m1 rl (pa_z pa) data m2 ∧
         length data = N.to_nat n ∧ data ≠ [] ∧
         (∀ (iq : istream) (prom : gset nat) ags,
            ags !! i = Some (WPAgent (PSail (Some m2) rs1 (wm_dev s) None iq)
                               (store_post_run (wm_ws s) rl (pa_z pa) (length data)
                                  (S (length (wm_log s)))) prom) →
            rtc (wp_pf_run (sail_step next))
              (WPCfg (wimg s) (wm_log s ++ [WMsg (pa_z pa) data (Some i) k]) ags)
              (WPCfg (wimg s) (wm_log s')
                 (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s')
                                    (wm_dev s') None iq)
                           (wm_ws s') prom]> ags))))
      ∨ (∃ rs1 : regstate,
           silent_run (m, wm_regs s) (Interface.Ret x, rs1) ∧
           s' = wregs_set s rs1).

  Local Ltac sbr_silent :=
    match goal with
    | Hsh : ∀ _, sail_shaped _, Hrun : wrun _ _ _ _ _, IH : ∀ _, _ ∧ _ |- _ =>
        let Hch := fresh "Hch" in
        pose proof (proj1 (IH _) _ _ _ (Hsh _) Hrun) as Hch;
        intros iq prom ags Hlk;
        eapply pf_silent;
          [exact Hlk | by (rewrite /sail_step /=; right; split; reflexivity) |];
        apply Hch; by apply (lookup_insert_i _ _ _ Hlk)
    end.

  Local Ltac amo_silent :=
    match goal with
    | Hsh : ∀ _, amo_tail _ _ _, Hrun : wrun _ _ _ _ _, IH : ∀ _, _ ∧ _ |- _ =>
        let m1 := fresh "m1" in let m2 := fresh "m2" in
        let rs1 := fresh "rs1" in let rl := fresh "rl" in
        let data := fresh "data" in
        let kc := fresh "kc" in
        let rsa := fresh "rsa" in
        destruct (proj2 (IH _) _ _ _ _ _ (Hsh _) Hrun)
          as [(m1 & m2 & rs1 & rl & data & kc & Hsil & Hwr & Hlen & Hne & Hch)
             |(rsa & Hsil & Heqs)];
        [ left; exists m1, m2, rs1, rl, data, kc;
          split_and!; [|exact Hwr|exact Hlen|exact Hne|exact Hch];
          eapply rtc_l; [|exact Hsil]; by rewrite /silent1 /=
        | right; exists rsa; split;
            [eapply rtc_l; [|exact Hsil]; by rewrite /silent1 /=
            |exact Heqs] ]
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
      - intros s x s' _ [-> ->]. intros iq prom ags Hlk.
        rewrite (list_insert_id _ _ _ Hlk). apply rtc_refl.
      - (* the window may be ABANDONED at the instruction's end: no run at
           all, and the state moved only in its registers (not at all, here) *)
        intros pa n s x s' _ [-> ->]. right.
        exists (wm_regs s). split; [apply rtc_refl|by rewrite wregs_set_id]. }
    split.
    - (* ---------------- sail_bracket ---------------- *)
      intros s x s' Hsh Hrun.
      destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                     |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hsh, Hrun;
        try (by sbr_silent); try (by exfalso; exact Hrun).
      { (* MemRead *)
        destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
        - (* MMIO: the hart's own fabric answers, silently *)
          destruct (dev_read (wm_dev s) (Interface.ReadReq.pa req) nn)
            as [[w d']|] eqn:Hdr; [|by exfalso; exact Hrun].
          pose proof (proj1 (IH (inl (w, None))) _ _ _ (Hsh _) Hrun) as Hch.
          intros iq prom ags Hlk.
          eapply pf_silent; [exact Hlk| |].
          + rewrite /sail_step /= Hd (dev_read_t_Some _ _ _ _ _ Hdr) /=.
            right. split; reflexivity.
          + apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
        - destruct Hsh as (Hcoh & Hsh).
          destruct Hrun as (w & ts & Hok & Hrun).
          rewrite /wread_post Hcoh /= in Hrun.
          destruct (ak_latest (classify (Interface.ReadReq.access_kind req)))
            eqn:Hlat.
          + (* AN EXCLUSIVE READ: fused if the window closes, BARE if the
               run abandons it (delta (e)) *)
            destruct (proj2 (IH (inl (w, None))) (Interface.ReadReq.pa req) nn
                        _ _ _ (Hsh w) Hrun)
              as [(m1 & m2 & rs1 & rl & data & kc & Hsil & Hwr & Hlend & Hne & Hch)
                 |(rs1 & Hsil & Heqs)].
            * (* THE FUSED RMW *)
              intros iq prom ags Hlk.
              pose proof Hok as (Hlents & _).
              eapply pf_rmw.
              -- exact Hlk.
              -- rewrite /sail_step /= Hd. right. split; [exact Hcoh|].
                 split_and!;
                   [exact Hlat|reflexivity|reflexivity
                   |exact (mk_tvs_length nn ts w Hlents)|exact Hlend|].
                 exists w, m1, m2, rs1.
                 split_and!; [|exact Hsil|exact Hwr|reflexivity].
                 intros j Hj. rewrite (mk_tvs_snd nn ts w Hlents).
                 by apply wbytes_lookup.
              -- exact Hne.
              -- rewrite (mk_tvs_length nn ts w Hlents) Hlend //.
              -- exact (wread_read_ok s _ _ nn ts w Hcoh Hok).
              -- exact (wread_excl_ok i s _ _ nn ts w Hcoh Hlat Hok).
              -- rewrite (mk_tvs_fst nn ts w Hlents).
                 apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
            * (* THE BARE ARM: one [LLoad] brackets the whole abandoned
                 window, landing at the instruction's [Interface.Ret] *)
              intros iq prom ags Hlk.
              pose proof Hok as (Hlents & _).
              eapply pf_load with (lat := false).
              -- exact Hlk.
              -- rewrite /sail_step /= Hd. right. split; [exact Hcoh|]. right.
                 split_and!;
                   [exact Hlat|reflexivity|reflexivity
                   |exact (mk_tvs_length nn ts w Hlents)|].
                 exists w. split.
                 { intros j Hj. rewrite (mk_tvs_snd nn ts w Hlents).
                   by apply wbytes_lookup. }
                 exists x, rs1. split; [exact Hsil|reflexivity].
              -- exact (wread_read_ok s _ _ nn ts w Hcoh Hok).
              -- rewrite (mk_tvs_fst nn ts w Hlents) Heqs list_insert_insert.
                 apply rtc_refl.
          + (* a plain load *)
            pose proof (proj1 (IH (inl (w, None))) _ _ _ (Hsh _) Hrun) as Hch.
            intros iq prom ags Hlk.
            pose proof Hok as (Hlents & _).
            eapply pf_load with (lat := false).
            * exact Hlk.
            * rewrite /sail_step /= Hd. right. split; [exact Hcoh|]. left.
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
          pose proof (proj1 (IH (inl None)) _ _ _ Hsh Hrun) as Hch.
          intros iq prom ags Hlk.
          eapply pf_silent; [exact Hlk| |].
          + rewrite /sail_step /= Hd (dev_write_t_Some _ _ _ _ _ Hdw).
            right. split; reflexivity.
          + apply Hch. by apply (lookup_insert_i _ _ _ Hlk).
        - pose proof (proj1 (IH (inl None)) _ _ _ Hsh Hrun) as Hch.
          intros iq prom ags Hlk.
          eapply pf_store.
          + exact Hlk.
          + rewrite /sail_step /= Hd. right.
            split_and!; [reflexivity|exact Hn|reflexivity].
          + by apply wbytes_nonnil.
          + rewrite wbytes_length. apply Hch.
            by apply (lookup_insert_i _ _ _ Hlk). }
      { (* Barrier *)
        pose proof (proj1 (IH tt) _ _ _ (Hsh _) Hrun) as Hch.
        intros iq prom ags Hlk. destruct bk.
        1-9: eapply pf_fence;
               [exact Hlk | by (rewrite /sail_step /=; right; split; reflexivity) |];
             apply Hch; by apply (lookup_insert_i _ _ _ Hlk).
        - (* fence.tso: two chained fences, the second parked *)
          eapply pf_fence;
            [exact Hlk | by (rewrite /sail_step /=; right; split; reflexivity) |].
          eapply pf_fence.
          + by apply (lookup_insert_i _ _ _ Hlk).
          + (* the PARKED fence: [sp_fence] is set, so no irq arm here *)
            rewrite /sail_step /=. split; reflexivity.
          + rewrite list_insert_insert. apply Hch.
            by apply (lookup_insert_i _ _ _ Hlk).
        - (* fence.i: no event *)
          eapply pf_silent;
            [exact Hlk | by (rewrite /sail_step /=; right; split; reflexivity) |].
          apply Hch. by apply (lookup_insert_i _ _ _ Hlk). }
      { (* Choose *)
        destruct Hrun as (c & Hrun).
        pose proof (proj1 (IH c) _ _ _ (Hsh _) Hrun) as Hch.
        intros iq prom ags Hlk.
        eapply pf_silent; [exact Hlk| |].
        - rewrite /sail_step /=. right. split; [reflexivity|]. by exists c.
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
        pose proof (proj1 (IH (inl None)) _ _ _ Hsh Hrun) as Hch. left.
        exists (Interface.Next (Interface.MemWrite nn req) k), (k (inl None)),
               (wm_regs s), (ak_sync (classify (Interface.WriteReq.access_kind req))),
               (wbytes nn (Interface.WriteReq.value req)),
               (wm_class_of (classify (Interface.WriteReq.access_kind req))
                  (wm_ws s)).
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
          as [(m1 & m2 & rs1 & rl & data & kc & Hsil & Hwr & Hlen & Hne & Hch)
             |(rsa & Hsil & Heqs)].
        - left. exists m1, m2, rs1, rl, data, kc.
          split_and!; [|exact Hwr|exact Hlen|exact Hne|exact Hch].
          eapply rtc_l; [|exact Hsil]. rewrite /silent1 /=. by exists c.
        - right. exists rsa. split; [|exact Heqs].
          eapply rtc_l; [|exact Hsil]. rewrite /silent1 /=. by exists c. }
  Qed.

  (** THE BRACKET.  One instruction monad, run by [wrun], IS a pf run of the
      one stepping agent. *)
  Theorem wrun_sail_bracket (m : M unit) s x s' :
    sail_shaped m →
    wrun (Some i) m s x s' →
    ∀ (iq : istream) (prom : gset nat) ags,
      ags !! i = Some (WPAgent (PSail (Some m) (wm_regs s) (wm_dev s) None iq)
                         (wm_ws s) prom) →
      rtc (wp_pf_run (sail_step next))
        (WPCfg (wimg s) (wm_log s) ags)
        (WPCfg (wimg s) (wm_log s')
           (<[i := WPAgent (PSail (Some (Interface.Ret x)) (wm_regs s')
                              (wm_dev s') None iq)
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
    ∀ (iq : istream) (prom : gset nat) (ags : list (wpagent psail)),
      ags !! i = Some (WPAgent (PSail None (wm_regs s) (wm_dev s) None iq)
                         (wm_ws s) prom) →
      rtc (wp_pf_run (sail_step riscv_step))
        (WPCfg (wimg s) (wm_log s) ags)
        (WPCfg (wimg s) (wm_log s')
           (<[i := WPAgent (PSail None (wm_regs s') (wm_dev s') None iq)
                     (wm_ws s') prom]> ags)).
  Proof.
    intros Hsh Hrun.
    pose proof (wrun_sail_bracket riscv_step i (riscv_step tick) s x s' Hsh Hrun)
      as Hch.
    intros iq prom ags Hlk.
    have Hlt : (i < length ags)%nat by exact (lookup_lt_Some _ _ _ Hlk).
    eapply pf_silent.
    - exact Hlk.
    - rewrite /sail_step /=. right. split; [reflexivity|]. by exists tick.
    - eapply rtc_transitive.
      + apply Hch. apply list_lookup_insert. exact Hlt.
      + apply pf_silent_last; [by rewrite length_insert|].
        rewrite /sail_step /=. right. split; reflexivity.
  Qed.

End instr.

(** The ONE-AGENT instance: the configuration shape
    [WPCfg img log [WPAgent p ws ∅]] the W5 composition starts from
    ([<[0 := a]> [b]] reduces to [[a]], so this is [sail_instr_bracket] read
    at [i := 0] with a singleton agent list). *)
Corollary sail_instr_bracket_single (tick : bool) s x s' :
  sail_shaped (riscv_step tick) →
  wrun (Some 0%nat) (riscv_step tick) s x s' →
  ∀ (iq : istream) (prom : gset nat),
    rtc (wp_pf_run (sail_step riscv_step))
      (WPCfg (wimg s) (wm_log s)
         [WPAgent (PSail None (wm_regs s) (wm_dev s) None iq) (wm_ws s) prom])
      (WPCfg (wimg s) (wm_log s')
         [WPAgent (PSail None (wm_regs s') (wm_dev s') None iq) (wm_ws s') prom]).
Proof.
  intros Hsh Hrun.
  pose proof (sail_instr_bracket 0%nat tick s x s' Hsh Hrun) as Hch.
  intros iq prom.
  apply (Hch iq prom
           [WPAgent (PSail None (wm_regs s) (wm_dev s) None iq) (wm_ws s) prom]).
  reflexivity.
Qed.
