(** * WeakEvLang.v — the EVENT-GRANULAR weak-memory language (spike S1)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    2026-08-14 "expression-resident monad" section); worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S1).

    [WeakLang.wprim_step]'s hart arm runs a WHOLE INSTRUCTION
    ([WeakInterp.wrun (riscv_step tick)]) in one language step.  THIS
    language's hart arm runs ONE EVENT of the Sail interaction monad — the
    same case analysis [WeakSailLTS.sail_mstep] performs, but WITHOUT the two
    oracles ([psail]'s [sp_dev] stream/fabric and [sp_irq]), because the
    device fabric is σ's and the residual monad is the EXPRESSION's.

    ------------------------------------------------------------------------
    THE PLACEMENT RULE (design doc, revised).  Control state goes in the
    EXPRESSION exactly where control flow is MODEL-DEFINED, and in σ where it
    is MEMORY-DEFINED.  INTER-instruction control flow is memory-defined (the
    next instruction comes from a fetch through a page table into mutable
    memory), so the boundary stays a boring token [ELoop].  INTRA-instruction
    control flow is model-defined (the continuation IS the Sail monad value
    [riscv_step tick] hands out), so it rides in [ECycle], is consumed
    monotonically, and WP-of-an-instruction becomes proof by SYNTACTIC
    DESCENT on that argument.  Devices have neither a fetch nor a preemption
    problem, so [EDisk] carries its whole operation state.

      σ           = [WeakLang.wgstate] VERBATIM (no new fields, no new
                    ghosts, [WeakGhost.weak_state_interp] unchanged);
      [ELoop g c] = hart [c] at an instruction boundary;
      [ECycle g c m fn] = hart [c] executing one instruction, [m] the
                    residual monad and [fn] the parked second fence;
      [EDisk g pend dws] = the disk agent, its message burst and its own
                    view — the pf [PDisk] agent field for field;
      [EUart g] / [EPlic g] / [EPower] = as in [WeakLang].

    ------------------------------------------------------------------------
    DESIGN DELTAS AND RECORDED DECISIONS (read before extending).

    (D1) THE DEVICE ACCESSORS ARE THE **PARTIAL** ONES.
         [DevModel.dev_read]/[dev_write] decline a bad width or an undecoded
         offset inside a device window, and this language is STUCK there —
         it does NOT use [WeakSailLTS]'s totalized [dev_read_t]/[dev_write_t].
         Justified by the design's "stuck-is-fine": nothing in this tower ever
         has to know that an instruction COMPLETES (there is no [sail_live],
         no [sail_shaped], no reconstruction), so a stuck node costs nothing.

    (D2) THE STORE ARM **COMPUTES** THE MESSAGE CLASS
         ([WeakInterp.wm_class_of ak ws] at the storing hart's own [wstate]),
         so there is no free class binder and [cls_canonical]/the retag die by
         construction (design doc, decision 2 of three).  The FUSED RMW arm
         stamps [WCexcl] outright.

    (D3) THE RMW STAYS FUSED — exclusive read, silent window, conditional
         write, ONE event ([esilent_run]/[ewr_node]).  A bare exclusive read
         and a standalone conditional write each take the ordinary
         load/store arm.

    (D4) INTERRUPT DELIVERY IS **ONLY** THE PLIC THREAD'S ARM
         ([RiscvLang.plic_step]'s wire write, spelled here as [eplic_step]).
         There is NO hart-side delivery event: delivery is an asynchronous
         cross-thread register write and fires whatever expression the hart
         is sitting at.  (The pre-revision draft had it twice; the redundancy
         is gone.)

    (D5) THE PARKED FENCE GATES EVERYTHING: while [fn] is [Some _] the ONLY
         move [ECycle g c m fn] has is to fire it.  So the two halves of a
         [fence.tso] cannot be separated by any other event of that hart, and
         the whole park/fire discipline is local to one instruction's cycle —
         which is why [ECycle _ _ (Ret _) fn] pops to [ELoop] only at
         [fn = None]. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The expressions

    [RiscvLang.mexpr] with the hart's boundary token SPLIT ([ELoop] /
    [ECycle]) and the disk's token carrying its operation state.  The
    generation index and the corpse discipline are unchanged, so the whole
    power/crash machinery transfers: [ECycle] simply gets the corpse arm
    [ELoop] already had. *)

Inductive eexpr :=
  | ELoop  (gen : nat) (cpu : CPU)
  | ECycle (gen : nat) (cpu : CPU) (m : M unit)
           (fn : option (bool * bool * bool * bool))
  | EUart  (gen : nat)
  | EDisk  (gen : nat) (pend : list wmsg) (dws : wstate)
  | EPlic  (gen : nat)
  | EPower.

Definition eval := Empty_set.
Definition eobs := Empty_set.
Definition eof_val (v : eval) : eexpr := match v with end.
Definition eto_val (_ : eexpr) : option eval := None.

(** The thread pool a fresh era forks: one hart thread per CPU, the two
    device threads and the PLIC.  The disk's expression carries the EMPTY
    burst and a FRESH view — the two clauses the pre-revision [eboot_facts]
    had to put on σ. *)
Definition epower_fork (gen : nat) : list eexpr :=
  (ELoop gen <$> enum CPU) ++ [EUart gen; EDisk gen [] ws_init; EPlic gen].

(* ====================================================================== *)
(** ** 2. σ-updates

    σ is [WeakLang.wgstate] verbatim, so an arm's effect is one of five
    named shapes.  Keeping them named (rather than writing [WGState …] at
    each arm) is what lets S4's lifting rules state ONE interpretation-closing
    lemma per shape. *)

Definition ewg_reg (σ : wgstate) (c : CPU) (rs : regstate) : wgstate :=
  WGState (<[c := rs]> (wgregs σ)) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
          (wggen σ) (wgpow σ).

Definition ewg_dev (σ : wgstate) (d : dev_state) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) d (wggen σ) (wgpow σ).

Definition ewg_ws (σ : wgstate) (c : CPU) (ws : wstate) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (<[c := ws]> (wgws σ)) (wgdev σ)
          (wggen σ) (wgpow σ).

Definition ewg_store (σ : wgstate) (c : CPU) (ws : wstate) (lg : list wmsg)
    : wgstate :=
  WGState (wgregs σ) (wgimg σ) lg (<[c := ws]> (wgws σ)) (wgdev σ)
          (wggen σ) (wgpow σ).

Definition ewg_rmw (σ : wgstate) (c : CPU) (rs : regstate) (ws : wstate)
    (lg : list wmsg) : wgstate :=
  WGState (<[c := rs]> (wgregs σ)) (wgimg σ) lg (<[c := ws]> (wgws σ))
          (wgdev σ) (wggen σ) (wgpow σ).

Definition ewg_log (σ : wgstate) (lg : list wmsg) : wgstate :=
  WGState (wgregs σ) (wgimg σ) lg (wgws σ) (wgdev σ) (wggen σ) (wgpow σ).

(* ====================================================================== *)
(** ** 3. The fused-RMW ingredients

    [WeakSailLTS.silent1] / [silent_run] / [wr_node], RESTATED here rather
    than imported: [WeakSailLTS] exports [psail] with its [sp_dev]/[sp_irq]
    oracle fields, and this language must not depend on that file at all. *)

Definition esilent1 (c c' : M unit * regstate) : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       | Interface.RegRead r _       => fun k => c' = (k (register_lookup r c.2), c.2)
       | Interface.RegWrite r _ v    => fun k => c' = (k tt, register_set r v c.2)
       | Interface.InstrAnnounce _   => fun k => c' = (k tt, c.2)
       | Interface.BranchAnnounce _ _=> fun k => c' = (k tt, c.2)
       | Interface.CacheOp _         => fun k => c' = (k tt, c.2)
       | Interface.TlbOp _           => fun k => c' = (k tt, c.2)
       | Interface.TakeException _   => fun k => c' = (k tt, c.2)
       | Interface.ReturnException _ => fun k => c' = (k tt, c.2)
       | Interface.TranslationStart _=> fun k => c' = (k tt, c.2)
       | Interface.TranslationEnd _  => fun k => c' = (k tt, c.2)
       | Interface.CycleCount        => fun k => c' = (k tt, c.2)
       | Interface.Message _         => fun k => c' = (k tt, c.2)
       | Interface.GetCycleCount     => fun k => c' = (k 0%Z, c.2)
       | Interface.Choose _          => fun k => exists ch, c' = (k ch, c.2)
       | _ => fun _ => False
       end) k
  end.

Definition esilent_run : relation (M unit * regstate) := rtc esilent1.

Definition ewr_node (m : M unit) (rl : bool) (base : Z) (data : list (bv 8))
    (m' : M unit) : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       | Interface.MemWrite n req => fun k =>
           dev_addr (Interface.WriteReq.pa req) = false /\
           n <> 0%N /\
           ak_latest (classify (Interface.WriteReq.access_kind req)) = true /\
           rl = ak_sync (classify (Interface.WriteReq.access_kind req)) /\
           base = pa_z (Interface.WriteReq.pa req) /\
           data = wbytes n (Interface.WriteReq.value req) /\
           m' = k (inl None)
       | _ => fun _ => False
       end) k
  end.

(** The barrier table, split into what fires NOW and what is PARKED. *)
Definition ebar_now (b : barrier_kind) : option (bool * bool * bool * bool) :=
  match b with
  | Barrier_RISCV_rw_rw => Some (true , true , true , true )
  | Barrier_RISCV_r_rw  => Some (true , false, true , true )
  | Barrier_RISCV_r_r   => Some (true , false, true , false)
  | Barrier_RISCV_rw_w  => Some (true , true , false, true )
  | Barrier_RISCV_w_w   => Some (false, true , false, true )
  | Barrier_RISCV_w_rw  => Some (false, true , true , true )
  | Barrier_RISCV_rw_r  => Some (true , true , true , false)
  | Barrier_RISCV_r_w   => Some (true , false, false, true )
  | Barrier_RISCV_w_r   => Some (false, true , true , false)
  | Barrier_RISCV_tso   => Some (true , false, true , false)
  | Barrier_RISCV_i     => None
  end.

Definition ebar_park (b : barrier_kind) : option (bool * bool * bool * bool) :=
  match b with
  | Barrier_RISCV_tso => Some (true, true, false, true)
  | _ => None
  end.

Definition efence_apply (ws : wstate) (o : option (bool * bool * bool * bool))
    : wstate :=
  match o with
  | Some (pr, pw, sr, sw) => fence_post ws pr pw sr sw
  | None => ws
  end.

Lemma efence_barrier_post ws b :
  efence_apply (efence_apply ws (ebar_now b)) (ebar_park b) = barrier_post ws b.
Proof. by destruct b. Qed.

Lemma efence_apply_le ws o : ws_le ws (efence_apply ws o).
Proof.
  destruct o as [[[[pr pw] sr] sw]|]; [apply fence_post_le|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 4. The hart's per-event step

    One arm per event kind, per the design's table, ON THE EXPRESSION: the
    successor names the residual monad, so the WP rules of S4 are syntactic
    descent and not a ghost protocol. *)

Section hart.
  Context (gen : nat) (σ : wgstate) (c : CPU).

  Local Notation rs0 := (wgregs σ c).
  Local Notation ws0 := (wgws σ c).
  Local Notation d0  := (wgdev σ).
  Local Notation lg0 := (wglog σ).

  (** The monad-node dispatch.  Mirrors [WeakSailLTS.sail_mstep] arm for arm,
      minus the labels and the oracles; the device arms use the PARTIAL
      accessors (delta (D1)).

      RAM READ is LABEL-FREE: the timestamps/values it takes are chosen here
      and constrained by [WeakPromise.read_ok] against the SHARED log and
      this hart's own view.  The FUSED RMW (delta (D3)) is the second
      disjunct of the same arm, with [excl_ok] at the fused top.  RAM WRITE
      COMPUTES its class (delta (D2)). *)
  Definition emonad_step (m : M unit) (e' : eexpr) (σ' : wgstate) : Prop :=
    match m with
    | Interface.Ret _ =>
        (* end of the instruction: back to the boundary token *)
        e' = ELoop gen c /\ σ' = σ
    | Interface.Next oc k =>
        (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
         | Interface.RegRead r _ => fun k =>
             e' = ECycle gen c (k (register_lookup r rs0)) None /\ σ' = σ
         | Interface.RegWrite r _ v => fun k =>
             e' = ECycle gen c (k tt) None /\
             σ' = ewg_reg σ c (register_set r v rs0)
         | Interface.MemRead n req => fun k =>
             if dev_addr (Interface.ReadReq.pa req)
             then (* MMIO: the SHARED fabric answers, partially (D1) *)
               exists (w : bv (8 * n)) (d' : dev_state),
                 dev_read d0 (Interface.ReadReq.pa req) n = Some (w, d') /\
                 e' = ECycle gen c (k (inl (w, None))) None /\
                 σ' = ewg_dev σ d'
             else
               ak_coh (classify (Interface.ReadReq.access_kind req)) = false /\
               ((* the PLAIN RAM read (exclusive or not: a bare exclusive
                   read is an ordinary load) *)
                (exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (wgimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   e' = ECycle gen c (k (inl (w, None))) None /\
                   σ' = ewg_ws σ c
                          (load_post_run ws0
                             (ak_sync (classify (Interface.ReadReq.access_kind req)))
                             (pa_z (Interface.ReadReq.pa req)) tvs.*1))
                \/
                (* THE FUSED RMW *)
                (ak_latest (classify (Interface.ReadReq.access_kind req)) = true /\
                 exists (w : bv (8 * n)) (tvs : list (nat * bv 8))
                        (data : list (bv 8)) (rl : bool) (m1 m2 : M unit)
                        (rs1 : regstate),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (wgimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   excl_ok lg0 (fin_to_nat c) (pa_z (Interface.ReadReq.pa req))
                     tvs (S (length lg0)) /\
                   data <> [] /\ length tvs = length data /\
                   esilent_run (k (inl (w, None)), rs0) (m1, rs1) /\
                   ewr_node m1 rl (pa_z (Interface.ReadReq.pa req)) data m2 /\
                   e' = ECycle gen c m2 None /\
                   σ' = ewg_rmw σ c rs1
                          (store_post_run
                             (load_post_run ws0
                                (ak_sync (classify (Interface.ReadReq.access_kind req)))
                                (pa_z (Interface.ReadReq.pa req)) tvs.*1)
                             rl (pa_z (Interface.ReadReq.pa req)) (length data)
                             (S (length lg0)))
                          (lg0 ++ [WMsg (pa_z (Interface.ReadReq.pa req)) data
                                     (Some (fin_to_nat c)) WCexcl])))
         | Interface.MemWrite n req => fun k =>
             if dev_addr (Interface.WriteReq.pa req)
             then
               exists d' : dev_state,
                 dev_write d0 (Interface.WriteReq.pa req) n
                   (Interface.WriteReq.value req) = Some d' /\
                 e' = ECycle gen c (k (inl None)) None /\ σ' = ewg_dev σ d'
             else
               n <> 0%N /\
               e' = ECycle gen c (k (inl None)) None /\
               σ' = ewg_store σ c
                      (store_post_run ws0
                         (ak_sync (classify (Interface.WriteReq.access_kind req)))
                         (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
                         (S (length lg0)))
                      (lg0 ++ [WMsg (pa_z (Interface.WriteReq.pa req))
                                 (wbytes n (Interface.WriteReq.value req))
                                 (Some (fin_to_nat c))
                                 (wm_class_of
                                    (classify (Interface.WriteReq.access_kind req))
                                    ws0)])
         | Interface.Barrier b => fun k =>
             e' = ECycle gen c (k tt) (ebar_park b) /\
             σ' = ewg_ws σ c (efence_apply ws0 (ebar_now b))
         | Interface.InstrAnnounce _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.BranchAnnounce _ _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.CacheOp _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TlbOp _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TakeException _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.ReturnException _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TranslationStart _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TranslationEnd _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.CycleCount => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.Message _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.GetCycleCount => fun k =>
             e' = ECycle gen c (k 0%Z) None /\ σ' = σ
         | Interface.Choose _ => fun k =>
             exists ch, e' = ECycle gen c (k ch) None /\ σ' = σ
         (* GenericFail / Discard / a raised Sail exception: STUCK. *)
         | _ => fun _ => False
         end) k
    end.

  (** THE CYCLE EVENT.  The parked fence gates everything (delta (D5)). *)
  Definition ecycle_step (m : M unit) (fn : option (bool * bool * bool * bool))
      (e' : eexpr) (σ' : wgstate) : Prop :=
    match fn with
    | Some (pr, pw, sr, sw) =>
        e' = ECycle gen c m None /\
        σ' = ewg_ws σ c (fence_post ws0 pr pw sr sw)
    | None => emonad_step m e' σ'
    end.

End hart.

(* ====================================================================== *)
(** ** 5. The device threads

    [WeakLang]'s three arms.  The UART and PLIC arms are literally
    [RiscvLang.uart_step]/[plic_step]; the disk arm is [WeakLang.wdisk_step]
    SPLIT into a burst and one emit per message — which is what makes it 1:1
    with the pf disk agent — with the burst buffer and the disk's own view in
    the EXPRESSION. *)

Definition euart_step (σ σ' : wgstate) : Prop :=
  exists d', uart_step (wgdev σ) d' /\ σ' = ewg_dev σ d'.

(** THE PLIC THREAD delivers ONE interrupt, to a hart it chooses: exactly
    [RiscvLang.plic_step]'s [PlicStepWire], and (delta (D4)) the ONLY
    interrupt-delivery arm in the language. *)
Definition eplic_step (σ σ' : wgstate) : Prop :=
  exists c : CPU,
    σ' = ewg_reg σ c
           (register_set sig_seip
              (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c))) (wgregs σ c)).

(** THE BURST: one [wdisk_step] at the flat projection of image+log, loading
    the canonical message list into the disk expression's buffer.  Only at an
    EMPTY buffer, so a burst never clobbers messages still owed to the log. *)
Definition edisk_burst (gen : nat) (pend : list wmsg) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  pend = [] /\
  exists d' w, wdisk_step (wgdev σ) (wflat (wgimg σ) (wglog σ)) d' w /\
    e' = EDisk gen (wmsgs_of_map w) dws /\ σ' = ewg_dev σ d'.

(** THE EMIT: pop one buffered message and append it.  Its tid is already
    [Some n_disk] ([WeakLang.wmsgs_of_map] stamps it), so the disk's own view
    moves by [store_post_run] exactly as a pf [PFStore] would. *)
Definition edisk_emit (gen : nat) (pend : list wmsg) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  exists m rest, pend = m :: rest /\
    (* the buffer is CANONICAL: [WeakLang.wmsgs_of_map] only ever produces
       one-byte messages stamped [Some n_disk], and the pf disk agent's
       [PFStore] needs both *)
    wm_data m <> [] /\ wm_tid m = Some n_disk /\
    e' = EDisk gen rest
           (store_post_run dws false (wm_pa m) (length (wm_data m))
              (S (length (wglog σ)))) /\
    σ' = ewg_log σ (wglog σ ++ [m]).

Definition edisk_step (gen : nat) (pend : list wmsg) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  edisk_burst gen pend dws σ e' σ' \/ edisk_emit gen pend dws σ e' σ'.

(* ====================================================================== *)
(** ** 6. Boot / crash reset

    [WeakLang.wboot_facts] UNCHANGED — the four clauses the pre-revision
    version added (every hart at a boundary, no parked fence, empty burst
    buffer, fresh disk view) are now facts about [epower_fork]'s
    expressions, so σ owes nothing. *)
Definition eboot_shape (σ σ' : wgstate) : Prop :=
  wggen σ' = wggen σ
  /\ (wgdev σ').(dvirtio) = virtio_reset (wgdev σ).(dvirtio)
  /\ wboot_facts σ'.

(* ====================================================================== *)
(** ** 7. [eprim_step]: the six arms

    [WeakLang.wprim_step]'s shape — same live/corpse gating, same PowerOff
    generation bump, same PowerOn fork — with the hart's single instruction
    arm split into the boundary arm and the cycle arm. *)

Definition ethread_live (σ : wgstate) (gen : nat) : Prop :=
  wgpow σ = true /\ wggen σ = gen.

Lemma ethread_live_wthread_live σ gen :
  ethread_live σ gen <-> wthread_live σ gen.
Proof. reflexivity. Qed.

Definition eprim_step
    (e : eexpr) (σ : wgstate) (κ : list eobs)
    (e' : eexpr) (σ' : wgstate) (efs : list eexpr) : Prop :=
  (* the BOUNDARY: fetch a fresh instruction (the tick nondeterminism is
     [RiscvLang.prim_step]'s, verbatim) *)
  (exists gen cpu, e = ELoop gen cpu /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ σ' = σ /\
      exists tick : bool, e' = ECycle gen cpu (riscv_step tick) None)
     \/ (~ ethread_live σ gen /\ e' = e /\ σ' = σ)))
  \/
  (* the CYCLE: one event of the instruction *)
  (exists gen cpu m fn, e = ECycle gen cpu m fn /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ ecycle_step gen σ cpu m fn e' σ')
     \/ (~ ethread_live σ gen /\ e' = e /\ σ' = σ)))
  \/
  (exists gen, e = EUart gen /\ e' = EUart gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ euart_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (exists gen pend dws, e = EDisk gen pend dws /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ edisk_step gen pend dws σ e' σ')
     \/ (~ ethread_live σ gen /\ e' = e /\ σ' = σ)))
  \/
  (exists gen, e = EPlic gen /\ e' = EPlic gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ eplic_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (e = EPower /\ e' = EPower /\ κ = [] /\
    ((wgpow σ = true /\ efs = [] /\
       σ' = WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
                    (S (wggen σ)) false)
     \/
     (wgpow σ = false /\ efs = epower_fork (wggen σ) /\ eboot_shape σ σ'))).

Lemma weak_ev_lang_mixin : LanguageMixin eof_val eto_val eprim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs _. reflexivity.
Qed.

Definition weak_ev_lang : language := Language weak_ev_lang_mixin.

(* ====================================================================== *)
(** ** 8. Per-arm inversion *)

Lemma eprim_step_loop_inv gen cpu σ κ e' σ' efs :
  eprim_step (ELoop gen cpu) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ σ' = σ /\
    exists tick : bool, e' = ECycle gen cpu (riscv_step tick) None)
   \/ (~ ethread_live σ gen /\ e' = ELoop gen cpu /\ σ' = σ)).
Proof.
  intros [(gen0 & cpu0 & Heq & ? & ? & Harm)
         | [(? & ? & ? & ? & Heq & _) | [(? & Heq & _)
         | [(? & ? & ? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]]];
    try discriminate Heq.
  injection Heq as -> ->. by split_and!.
Qed.

Lemma eprim_step_cycle_inv gen cpu m fn σ κ e' σ' efs :
  eprim_step (ECycle gen cpu m fn) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ ecycle_step gen σ cpu m fn e' σ')
   \/ (~ ethread_live σ gen /\ e' = ECycle gen cpu m fn /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(gen0 & cpu0 & m0 & fn0 & Heq & ? & ? & Harm)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]]];
    try discriminate Heq.
  injection Heq as -> -> -> ->. by split_and!.
Qed.

Lemma eprim_step_uart_inv gen σ κ e' σ' efs :
  eprim_step (EUart gen) σ κ e' σ' efs ->
  e' = EUart gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ euart_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & ? & ? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_disk_inv gen pend dws σ κ e' σ' efs :
  eprim_step (EDisk gen pend dws) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ edisk_step gen pend dws σ e' σ')
   \/ (~ ethread_live σ gen /\ e' = EDisk gen pend dws /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _)
         | [(gen0 & p0 & d0 & Heq & ? & ? & Harm)
         | [(? & Heq & _) | (Heq & _)]]]]];
    try discriminate Heq.
  injection Heq as -> -> ->. by split_and!.
Qed.

Lemma eprim_step_plic_inv gen σ κ e' σ' efs :
  eprim_step (EPlic gen) σ κ e' σ' efs ->
  e' = EPlic gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ eplic_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | (Heq & _)]]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_power_inv σ κ e' σ' efs :
  eprim_step EPower σ κ e' σ' efs ->
  e' = EPower /\ κ = [] /\
  ((wgpow σ = true /\ efs = [] /\
     σ' = WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
                  (S (wggen σ)) false)
   \/ (wgpow σ = false /\ efs = epower_fork (wggen σ) /\ eboot_shape σ σ')).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (_ & ? & ? & Harm)]]]]];
    try discriminate Heq.
  by split_and!.
Qed.

(* ====================================================================== *)
(** ** 9. Cross-arm sanity lemmas (S3/S4's state-interpretation obligations) *)

Lemma ecycle_step_img gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> wgimg σ' = wgimg σ.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { by intros (_ & ->). }
  destruct m as [y|T oc k]; [by intros (_ & ->)|].
  destruct oc; simpl; try (by intros (_ & ->)); try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)]); reflexivity.
  - (* MemWrite *)
    destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + by intros (_ & _ & ->).
  - (* Choose *) by intros (ch & _ & ->).
Qed.

Lemma ecycle_step_era gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> wgpow σ' = wgpow σ /\ wggen σ' = wggen σ.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { by intros (_ & ->). }
  destruct m as [y|T oc k]; [by intros (_ & ->)|].
  destruct oc; simpl; try (by intros (_ & ->)); try (by intros []).
  - destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)]); by split.
  - destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + by intros (_ & _ & ->).
  - by intros (ch & _ & ->).
Qed.

(** ... and its successor is always a hart expression of the SAME generation
    and hart: the cycle either advances or pops to the boundary. *)
Lemma ecycle_step_shape gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' ->
  e' = ELoop gen c \/ exists m' fn', e' = ECycle gen c m' fn'.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (-> & _). right. by do 2 eexists. }
  destruct m as [y|T oc k]; [intros (-> & _); by left|].
  destruct oc; simpl;
    try (intros (-> & _); right; by do 2 eexists); try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & -> & _). right. by do 2 eexists.
    + intros (_ & [(w & tvs & _ & _ & _ & -> & _)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & -> & _)]);
        right; by do 2 eexists.
  - destruct (dev_addr _).
    + intros (d' & _ & -> & _). right. by do 2 eexists.
    + intros (_ & -> & _). right. by do 2 eexists.
  - intros (ch & -> & _). right. by do 2 eexists.
Qed.

Lemma ecycle_step_log_app gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> exists ms, wglog σ' = wglog σ ++ ms.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). exists []. by rewrite app_nil_r. }
  destruct m as [y|T oc k];
    [intros (_ & ->); exists []; by rewrite app_nil_r|].
  destruct oc; simpl;
    try (intros (_ & ->); exists []; by rewrite app_nil_r);
    try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & _ & ->). exists []. by rewrite app_nil_r.
    + intros (_ & [(w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)]).
      * exists []. by rewrite app_nil_r.
      * by eexists.
  - destruct (dev_addr _).
    + intros (d' & _ & _ & ->). exists []. by rewrite app_nil_r.
    + intros (_ & _ & ->). by eexists.
  - intros (ch & _ & ->). exists []. by rewrite app_nil_r.
Qed.

Lemma ecycle_step_ws_other gen σ c m fn e' σ' c' :
  ecycle_step gen σ c m fn e' σ' -> c' <> c -> wgws σ' c' = wgws σ c'.
Proof.
  intros H Hne. revert H. rewrite /ecycle_step.
  destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). by rewrite /ewg_ws /= gws_insert_ne. }
  destruct m as [y|T oc k]; [by intros (_ & ->)|].
  destruct oc; simpl;
    try (by intros (_ & ->)); try (by intros []).
  - destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)]);
        [rewrite /ewg_ws /=|rewrite /ewg_rmw /=]; by rewrite gws_insert_ne.
  - destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + intros (_ & _ & ->). rewrite /ewg_store /=. by rewrite gws_insert_ne.
  - (* Barrier *) intros (_ & ->). rewrite /ewg_ws /=. by rewrite gws_insert_ne.
  - intros (ch & _ & ->). reflexivity.
Qed.

Lemma ecycle_step_ws_le gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> ws_le (wgws σ c) (wgws σ' c).
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). rewrite /ewg_ws /= gws_insert_eq. apply fence_post_le. }
  destruct m as [y|T oc k]; [intros (_ & ->); reflexivity|].
  destruct oc; simpl; try (by intros (_ & ->)); try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & _ & ->). reflexivity.
    + intros (_ & [(w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)]).
      * rewrite /ewg_ws /= gws_insert_eq. apply load_post_run_le.
      * rewrite /ewg_rmw /= gws_insert_eq.
        etrans; [apply load_post_run_le|apply store_post_run_le].
  - destruct (dev_addr _).
    + intros (d' & _ & _ & ->). reflexivity.
    + intros (_ & _ & ->). rewrite /ewg_store /= gws_insert_eq.
      apply store_post_run_le.
  - (* Barrier *) intros (_ & ->). rewrite /ewg_ws /= gws_insert_eq.
    apply efence_apply_le.
  - intros (ch & _ & ->). reflexivity.
Qed.

(** The device threads move NO hart's view. *)
Lemma euart_step_ws σ σ' : euart_step σ σ' -> wgws σ' = wgws σ.
Proof. by intros (d' & _ & ->). Qed.
Lemma eplic_step_ws σ σ' : eplic_step σ σ' -> wgws σ' = wgws σ.
Proof. by intros (c0 & ->). Qed.
Lemma edisk_step_ws gen pend dws σ e' σ' :
  edisk_step gen pend dws σ e' σ' -> wgws σ' = wgws σ.
Proof.
  by intros [(_ & d' & w & _ & _ & ->)|(m & rest & _ & _ & _ & _ & ->)].
Qed.

(* ====================================================================== *)
(** ** 10. Reducibility helpers

    A CORPSE always steps; a live boundary always steps (the fetch arm needs
    nothing); the live device threads always step; the power thread steps
    while the power is on.  A live CYCLE steps iff its node is not stuck —
    which is the ONE place the language is honestly partial (delta (D1) and
    the design's "stuck-is-fine"). *)

Lemma eprim_step_loop_dead gen cpu σ :
  ~ ethread_live σ gen -> eprim_step (ELoop gen cpu) σ [] (ELoop gen cpu) σ [].
Proof. intros Hd. left. exists gen, cpu. split_and!; try reflexivity. by right. Qed.

Lemma eprim_step_loop_live gen cpu σ (tick : bool) :
  ethread_live σ gen ->
  eprim_step (ELoop gen cpu) σ [] (ECycle gen cpu (riscv_step tick) None) σ [].
Proof.
  intros Hl. left. exists gen, cpu. split_and!; try reflexivity.
  left. split_and!; [exact Hl|reflexivity|]. by exists tick.
Qed.

Lemma eprim_step_cycle_dead gen cpu m fn σ :
  ~ ethread_live σ gen ->
  eprim_step (ECycle gen cpu m fn) σ [] (ECycle gen cpu m fn) σ [].
Proof.
  intros Hd. right; left. exists gen, cpu, m, fn.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_uart_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (EUart gen) σ [] (EUart gen) σ [].
Proof.
  intros Hd. right; right; left. exists gen. split_and!; try reflexivity.
  by right.
Qed.

Lemma eprim_step_disk_dead gen pend dws σ :
  ~ ethread_live σ gen ->
  eprim_step (EDisk gen pend dws) σ [] (EDisk gen pend dws) σ [].
Proof.
  intros Hd. right; right; right; left. exists gen, pend, dws.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_plic_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (EPlic gen) σ [] (EPlic gen) σ [].
Proof.
  intros Hd. right; right; right; right; left. exists gen.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_power_off σ :
  wgpow σ = true ->
  eprim_step EPower σ [] EPower
    (WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
             (S (wggen σ)) false) [].
Proof.
  intros Hon. right; right; right; right; right. split_and!; try reflexivity.
  left. by split_and!.
Qed.

Lemma eprim_step_uart_idle gen σ :
  ethread_live σ gen -> eprim_step (EUart gen) σ [] (EUart gen) σ [].
Proof.
  intros Hl. right; right; left. exists gen. split_and!; try reflexivity.
  left. split; [exact Hl|]. exists (wgdev σ). split; [apply UartStepIdle|].
  by destruct σ.
Qed.

Lemma eprim_step_plic_wire gen σ (c : CPU) :
  ethread_live σ gen ->
  eprim_step (EPlic gen) σ [] (EPlic gen)
    (ewg_reg σ c
       (register_set sig_seip
          (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c))) (wgregs σ c))) [].
Proof.
  intros Hl. right; right; right; right; left. exists gen.
  split_and!; try reflexivity. left. split; [exact Hl|]. by exists c.
Qed.

(** THE BUFFER INVARIANT: every message the burst arm can load is a ONE-BYTE
    message stamped [Some n_disk].  It is what makes the emit arm enabled,
    and it is what the pf disk agent's [PFStore] needs. *)
Definition epend_canon (pend : list wmsg) : Prop :=
  Forall (fun m => wm_data m <> [] /\ wm_tid m = Some n_disk) pend.

Lemma epend_canon_nil : epend_canon [].
Proof. apply Forall_nil_2. Qed.

Lemma epend_canon_step gen pend dws σ e' σ' :
  epend_canon pend -> edisk_step gen pend dws σ e' σ' ->
  exists pend' dws', e' = EDisk gen pend' dws' /\ epend_canon pend'.
Proof.
  intros Hc [(_ & d' & w & _ & -> & _)|(m & rest & Hp & _ & _ & -> & _)].
  - do 2 eexists. split; [reflexivity|].
    rewrite /epend_canon. apply Forall_forall. intros m0 Hm0.
    split; [by eapply wmsgs_of_map_data|by eapply wmsgs_of_map_tid].
  - do 2 eexists. split; [reflexivity|].
    rewrite /epend_canon Hp in Hc. by apply Forall_cons in Hc as [_ ?].
Qed.

(** The disk is ALWAYS reducible: an empty buffer takes the idle burst
    ([WeakLang.WDiskStepIdle], whose write set is [∅] and hence buffers
    nothing), a canonical nonempty one emits. *)
Lemma eprim_step_disk_reducible gen pend dws σ :
  ethread_live σ gen -> epend_canon pend ->
  exists e' σ', eprim_step (EDisk gen pend dws) σ [] e' σ' [].
Proof.
  intros Hl Hc. destruct pend as [|m rest].
  - do 2 eexists. right; right; right; left. exists gen, [], dws.
    split_and!; try reflexivity.
    left. split; [exact Hl|]. left. split; [reflexivity|].
    exists (wgdev σ), ∅. split; [apply WDiskStepIdle|].
    rewrite wmsgs_of_map_empty. split; [reflexivity|by destruct σ].
  - rewrite /epend_canon in Hc. apply Forall_cons in Hc as [[Hd Ht] _].
    do 2 eexists. right; right; right; left. exists gen, (m :: rest), dws.
    split_and!; try reflexivity.
    left. split; [exact Hl|]. right. exists m, rest. by split_and!.
Qed.
