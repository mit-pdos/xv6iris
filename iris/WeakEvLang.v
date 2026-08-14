(** * WeakEvLang.v — the EVENT-GRANULAR weak-memory language (spike S1)

    Design: [claude-notes/design/weak-memory-event-granular.md]; worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S1).

    [WeakLang.wprim_step]'s hart arm runs a WHOLE INSTRUCTION
    ([WeakInterp.wrun (riscv_step tick)]) in one language step.  THIS
    language's hart arm runs ONE EVENT of the Sail interaction monad — the
    same case analysis [WeakSailLTS.sail_mstep] performs, but WITHOUT the two
    oracles ([psail]'s [sp_dev] stream/fabric and [sp_irq]), because the
    residual monad, the parked fence and the device fabric all live in σ.

    WHAT IS REUSED, VERBATIM: the expression type [RiscvLang.mexpr] and its
    [mval]/[mobs]/[of_val]/[to_val] (so the pool, the generation/power
    machinery, [power_fork] and the corpse arms are literally today's), the
    device relations [RiscvLang.uart_step]/[plic_step], the disk relation
    [WeakLang.wdisk_step] with [WeakLang.wflat]/[wmsgs_of_map], and the
    [WeakMem]/[WeakPromise] view algebra ([read_ok], [excl_ok],
    [load_post_run], [store_post_run], [fence_post]).

    WHAT IS NEW: the state record [egstate] (§1) and the per-event hart
    relation [ehart_step] (§3).

    ------------------------------------------------------------------------
    DESIGN DELTAS AND RECORDED DECISIONS (read before extending).

    (D1) THE DEVICE ACCESSORS ARE THE **PARTIAL** ONES.
         [DevModel.dev_read]/[dev_write] decline a bad width or an undecoded
         offset inside a device window, and this language is STUCK there —
         it does NOT use [WeakSailLTS]'s totalized [dev_read_t]/[dev_write_t].
         Justified by the design's "stuck-is-fine": nothing in this tower ever
         has to know that an instruction COMPLETES (there is no [sail_live],
         no [sail_shaped], no reconstruction), so a stuck node costs nothing;
         and the partial reading is the one [WeakInterp.wrun] has always had,
         so a leaf certified against [wrun] transfers unchanged.  The
         totalized reading would have to be justified per access instead.

    (D2) THE STORE ARM **COMPUTES** THE MESSAGE CLASS
         ([WeakInterp.wm_class_of ak ws] at the storing hart's own [wstate]),
         so there is no free class binder and [cls_canonical]/the retag die by
         construction (design doc, decision 2 of three).  The FUSED RMW arm
         stamps [WCexcl] outright: its [ewr_node] premise pins
         [ak_latest = true], at which point [wm_class_of] IS [WCexcl].

    (D3) THE RMW STAYS FUSED — exclusive read, silent window, conditional
         write, ONE event ([esilent_run]/[ewr_node], mirroring
         [WeakSailLTS.sail_mstep]'s fused arm including [read_ok] + [excl_ok]
         at the SHARED log).  A bare exclusive read and a standalone
         conditional write each take the ordinary load/store arm (deltas (e)
         and (e'') of [WeakSailLTS]).

    (D4) THE DISK AGENT GETS ITS OWN [wstate] ([eg_dws]) — a DEVIATION from
         the S1 field list, forced by S2.  On the pf side the disk is an
         ORDINARY agent whose emit is a [WeakPromiseBridge.PFStore], which
         moves that agent's view by [store_post_run]; [WeakLang]'s [wgstate]
         has no slot for it (the disk's view was the "[wa_dd]/flat-pinning
         residue" the design says disappears at event granularity).  Without
         the field the erased ↔ pf correspondence is not a bijection, so the
         field is here.  Nothing else reads it: [WeakGhost.no_violation]
         quantifies over HARTS, and the projection [eg_to_wg] forgets it.

    (D5) INTERRUPT DELIVERY EXISTS TWICE, ON PURPOSE.  The event table makes
         it a HART event (§3, [eirq_step]: [register_set sig_seip] from the
         WIRE [DevModel.dev_seip], no oracle); [WeakLang]'s thread structure
         makes it the PLIC thread's arm ([RiscvLang.plic_step], which is the
         same register write at a hart the plic chooses).  Both are kept —
         the first is what the event table asks for and what makes the hart
         arm pool-position-local under the S2 correspondence, the second is
         [WeakLang]'s arm verbatim.  They have exactly the same effect on σ,
         so the redundancy is inert.

    (D6) THE PARKED FENCE GATES EVERYTHING ([WeakSailLTS] delta (c)): while
         [eg_fence σ c] is [Some _] the ONLY move hart [c] has is to fire it.
         So the two halves of a [fence.tso] cannot be separated by any other
         event of that hart — including an interrupt delivery. *)
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
(** ** 1. The global event-granular state

    [WeakLang.wgstate]'s seven fields (registers, era-initial image, log,
    per-hart view, device fabric, generation, power) PLUS the four σ-resident
    thread-state slots the event granularity needs:

      [eg_hs c]    — hart [c]'s RESIDUAL instruction monad ([None] = the
                     instruction boundary);
      [eg_fence c] — its parked second fence (delta (D6));
      [eg_pend]    — the disk's canonical message burst;
      [eg_dws]     — the disk agent's own view (delta (D4)). *)
Record egstate := EGState {
  egregs   : CPU -> regstate;
  egimg    : gmap Arch.pa (bv 8);
  eglog    : list wmsg;
  egws     : CPU -> wstate;
  egdev    : dev_state;
  eggen    : nat;
  egpow    : bool;
  eg_hs    : CPU -> option (M unit);
  eg_fence : CPU -> option (bool * bool * bool * bool);
  eg_pend  : list wmsg;
  eg_dws   : wstate;
}.
Add Printing Constructor egstate.

(** THE PROJECTION TO [WeakLang.wgstate] — forget the four new slots.  S3's
    state interpretation is [WeakGhost.weak_state_interp] composed with it,
    which is what makes the φ export reusable verbatim. *)
Definition eg_to_wg (σ : egstate) : wgstate :=
  WGState (egregs σ) (egimg σ) (eglog σ) (egws σ) (egdev σ) (eggen σ)
          (egpow σ).

Lemma eg_to_wg_log σ : wglog (eg_to_wg σ) = eglog σ.
Proof. reflexivity. Qed.
Lemma eg_to_wg_ws σ : wgws (eg_to_wg σ) = egws σ.
Proof. reflexivity. Qed.
Lemma eg_to_wg_img σ : wgimg (eg_to_wg σ) = egimg σ.
Proof. reflexivity. Qed.
Lemma eg_to_wg_dev σ : wgdev (eg_to_wg σ) = egdev σ.
Proof. reflexivity. Qed.
Lemma eg_to_wg_regs σ : wgregs (eg_to_wg σ) = egregs σ.
Proof. reflexivity. Qed.

(** Pointwise update of a per-hart slot.  ONE combinator for all four
    [CPU -> _] fields, rather than four [Insert] instances (the tree already
    has two, [RiscvLang.greg_insert] and [WeakLang.gws_insert], and a third
    and fourth would make instance resolution the reader's problem). *)
Definition eset_at {A} (f : CPU -> A) (c : CPU) (a : A) : CPU -> A :=
  fun c' => if decide (c' = c) then a else f c'.

Lemma eset_at_eq {A} (f : CPU -> A) c (a : A) : eset_at f c a c = a.
Proof. rewrite /eset_at. by destruct (decide (c = c)). Qed.

Lemma eset_at_ne {A} (f : CPU -> A) c c' (a : A) :
  c' <> c -> eset_at f c a c' = f c'.
Proof. intros Hne. rewrite /eset_at. by destruct (decide (c' = c)). Qed.

(** The hart write-back: ONE constructor serving every arm of §3, so that an
    arm is a single equation and the inversion lemmas of §5 are uniform. *)
Definition ehart_set (σ : egstate) (c : CPU)
    (m : option (M unit)) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (ws : wstate)
    (lg : list wmsg) (d : dev_state) : egstate :=
  EGState (eset_at (egregs σ) c rs) (egimg σ) lg (eset_at (egws σ) c ws) d
          (eggen σ) (egpow σ)
          (eset_at (eg_hs σ) c m) (eset_at (eg_fence σ) c fn)
          (eg_pend σ) (eg_dws σ).

Lemma ehart_set_img σ c m rs fn ws lg d :
  egimg (ehart_set σ c m rs fn ws lg d) = egimg σ.
Proof. reflexivity. Qed.
Lemma ehart_set_log σ c m rs fn ws lg d :
  eglog (ehart_set σ c m rs fn ws lg d) = lg.
Proof. reflexivity. Qed.
Lemma ehart_set_dev σ c m rs fn ws lg d :
  egdev (ehart_set σ c m rs fn ws lg d) = d.
Proof. reflexivity. Qed.
Lemma ehart_set_gen σ c m rs fn ws lg d :
  eggen (ehart_set σ c m rs fn ws lg d) = eggen σ.
Proof. reflexivity. Qed.
Lemma ehart_set_pow σ c m rs fn ws lg d :
  egpow (ehart_set σ c m rs fn ws lg d) = egpow σ.
Proof. reflexivity. Qed.
Lemma ehart_set_ws_eq σ c m rs fn ws lg d :
  egws (ehart_set σ c m rs fn ws lg d) c = ws.
Proof. apply eset_at_eq. Qed.
Lemma ehart_set_ws_ne σ c m rs fn ws lg d c' :
  c' <> c -> egws (ehart_set σ c m rs fn ws lg d) c' = egws σ c'.
Proof. apply eset_at_ne. Qed.
Lemma ehart_set_pend σ c m rs fn ws lg d :
  eg_pend (ehart_set σ c m rs fn ws lg d) = eg_pend σ.
Proof. reflexivity. Qed.
Lemma ehart_set_dws σ c m rs fn ws lg d :
  eg_dws (ehart_set σ c m rs fn ws lg d) = eg_dws σ.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 2. The fused-RMW ingredients

    [WeakSailLTS.silent1] / [silent_run] / [wr_node], RESTATED here rather
    than imported: [WeakSailLTS] exports [psail] with its [sp_dev]/[sp_irq]
    oracle fields, and this language must not depend on that file at all.
    The three definitions below are its three ORACLE-FREE ones, verbatim. *)

(** The outcomes that may sit BETWEEN an rmw's read half and its write half:
    register and trace traffic only.  No memory, no barrier — those would
    break the fusion, and the model never emits them there. *)
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

(** The write half of a fused rmw: [m] is a CONDITIONAL [MemWrite] to RAM,
    writing [data] at [base] with release annotation [rl], continuing as
    [m'].  The [ak_latest = true] conjunct is what makes this arm disjoint
    from the plain-store arm, and (delta (D2)) what pins the class. *)
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

(** The barrier table, split into what fires NOW and what is PARKED.
    Compare [WeakInterp.barrier_post] line for line: [fence.tso] is two
    chained [fence_post]s there and two EVENTS here (delta (D6)). *)
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

(** SANITY: firing [ebar_now b] and then [ebar_park b] is [barrier_post b] —
    i.e. the two-event fence.tso has the same net effect as [WeakInterp]'s
    one-shot one. *)
Lemma efence_barrier_post ws b :
  efence_apply (efence_apply ws (ebar_now b)) (ebar_park b) = barrier_post ws b.
Proof. by destruct b. Qed.

Lemma efence_apply_le ws o : ws_le ws (efence_apply ws o).
Proof.
  destruct o as [[[[pr pw] sr] sw]|]; [apply fence_post_le|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 3. The hart's per-event step

    One arm per event kind, per the design's table.  Every arm is ONE
    equation [σ' = ehart_set σ c …], so the whole relation is read off the
    outcome the residual monad is sitting at. *)

Section hart.
  Context (σ : egstate) (c : CPU).

  Local Notation rs0 := (egregs σ c).
  Local Notation ws0 := (egws σ c).
  Local Notation d0  := (egdev σ).
  Local Notation lg0 := (eglog σ).

  (** THE INTERRUPT-DELIVERY EVENT (delta (D5)): the S-mode external pin is
      driven from the WIRE — [DevModel.dev_seip] of the SHARED fabric.  No
      oracle, no stream, no consistency premise. *)
  Definition eirq_step (σ' : egstate) : Prop :=
    σ' = ehart_set σ c (eg_hs σ c)
           (register_set sig_seip (bool_to_bit (dev_seip d0 (fin_to_nat c))) rs0)
           (eg_fence σ c) ws0 lg0 d0.

  (** The monad-node dispatch.  Mirrors [WeakSailLTS.sail_mstep] arm for arm,
      minus the labels and the oracles; the device arms use the PARTIAL
      accessors (delta (D1)).

      THE THREE MEMORY ARMS ARE SPELLED INLINE, exactly as [sail_mstep]
      spells them, because the request record's type is what the dependent
      match binds — a factored-out [Definition] would have to spell
      [Interface.ReadReq.t …] by hand.

      RAM READ is LABEL-FREE: the timestamps/values it takes are chosen here
      and constrained by [WeakPromise.read_ok] against the SHARED log and
      this hart's own view; the S2 correspondence RECONSTRUCTS the [LLoad]
      label from them.  The FUSED RMW (delta (D3)) is the second disjunct of
      the same arm, with [excl_ok] at the fused top [S (length lg0)] exactly
      as [WeakPromiseBridge.PFRmw] takes it.  RAM WRITE COMPUTES its class
      (delta (D2)) and is nonempty because [n <> 0]. *)
  Definition emonad_step (m : M unit) (σ' : egstate) : Prop :=
    match m with
    | Interface.Ret _ =>
        (* end of the instruction: back to the boundary *)
        σ' = ehart_set σ c None rs0 None ws0 lg0 d0
    | Interface.Next oc k =>
        (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
         | Interface.RegRead r _ => fun k =>
             σ' = ehart_set σ c (Some (k (register_lookup r rs0))) rs0 None
                    ws0 lg0 d0
         | Interface.RegWrite r _ v => fun k =>
             σ' = ehart_set σ c (Some (k tt)) (register_set r v rs0) None
                    ws0 lg0 d0
         | Interface.MemRead n req => fun k =>
             if dev_addr (Interface.ReadReq.pa req)
             then (* MMIO: the SHARED fabric answers, partially (D1) *)
               exists (w : bv (8 * n)) (d' : dev_state),
                 dev_read d0 (Interface.ReadReq.pa req) n = Some (w, d') /\
                 σ' = ehart_set σ c (Some (k (inl (w, None)))) rs0 None
                        ws0 lg0 d'
             else
               ak_coh (classify (Interface.ReadReq.access_kind req)) = false /\
               ((* the PLAIN RAM read (exclusive or not — delta (e) of
                   [WeakSailLTS]: a bare exclusive read is an ordinary load) *)
                (exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (egimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   σ' = ehart_set σ c (Some (k (inl (w, None)))) rs0 None
                          (load_post_run ws0
                             (ak_sync (classify (Interface.ReadReq.access_kind req)))
                             (pa_z (Interface.ReadReq.pa req)) tvs.*1)
                          lg0 d0)
                \/
                (* THE FUSED RMW *)
                (ak_latest (classify (Interface.ReadReq.access_kind req)) = true /\
                 exists (w : bv (8 * n)) (tvs : list (nat * bv 8))
                        (data : list (bv 8)) (rl : bool) (m1 m2 : M unit)
                        (rs1 : regstate),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (egimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   excl_ok lg0 (fin_to_nat c) (pa_z (Interface.ReadReq.pa req))
                     tvs (S (length lg0)) /\
                   data <> [] /\ length tvs = length data /\
                   esilent_run (k (inl (w, None)), rs0) (m1, rs1) /\
                   ewr_node m1 rl (pa_z (Interface.ReadReq.pa req)) data m2 /\
                   σ' = ehart_set σ c (Some m2) rs1 None
                          (store_post_run
                             (load_post_run ws0
                                (ak_sync (classify (Interface.ReadReq.access_kind req)))
                                (pa_z (Interface.ReadReq.pa req)) tvs.*1)
                             rl (pa_z (Interface.ReadReq.pa req)) (length data)
                             (S (length lg0)))
                          (lg0 ++ [WMsg (pa_z (Interface.ReadReq.pa req)) data
                                     (Some (fin_to_nat c)) WCexcl]) d0))
         | Interface.MemWrite n req => fun k =>
             if dev_addr (Interface.WriteReq.pa req)
             then
               exists d' : dev_state,
                 dev_write d0 (Interface.WriteReq.pa req) n
                   (Interface.WriteReq.value req) = Some d' /\
                 σ' = ehart_set σ c (Some (k (inl None))) rs0 None ws0 lg0 d'
             else
               n <> 0%N /\
               σ' = ehart_set σ c (Some (k (inl None))) rs0 None
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
                      d0
         | Interface.Barrier b => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 (ebar_park b)
                    (efence_apply ws0 (ebar_now b)) lg0 d0
         | Interface.InstrAnnounce _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.BranchAnnounce _ _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.CacheOp _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.TlbOp _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.TakeException _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.ReturnException _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.TranslationStart _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.TranslationEnd _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.CycleCount => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.Message _ => fun k =>
             σ' = ehart_set σ c (Some (k tt)) rs0 None ws0 lg0 d0
         | Interface.GetCycleCount => fun k =>
             σ' = ehart_set σ c (Some (k 0%Z)) rs0 None ws0 lg0 d0
         | Interface.Choose _ => fun k =>
             exists ch, σ' = ehart_set σ c (Some (k ch)) rs0 None ws0 lg0 d0
         (* GenericFail / Discard / a raised Sail exception: STUCK.  Nothing
            in this tower needs an instruction to complete (design doc), so
            no arm is owed here. *)
         | _ => fun _ => False
         end) k
    end.

  (** THE HART EVENT.  The parked fence gates everything (delta (D6)); at
      the boundary a fresh instruction is generated ([riscv_step tick],
      [tick] chosen nondeterministically exactly as [RiscvLang.prim_step]
      does). *)
  Definition ehart_step (σ' : egstate) : Prop :=
    match eg_fence σ c with
    | Some (pr, pw, sr, sw) =>
        σ' = ehart_set σ c (eg_hs σ c) rs0 None
               (fence_post ws0 pr pw sr sw) lg0 d0
    | None =>
        eirq_step σ'
        \/ match eg_hs σ c with
           | None =>
               exists tick : bool,
                 σ' = ehart_set σ c (Some (riscv_step tick)) rs0 None ws0 lg0 d0
           | Some m => emonad_step m σ'
           end
    end.
End hart.

(* ====================================================================== *)
(** ** 4. The device threads

    [WeakLang]'s three arms, restated over [egstate].  The UART and PLIC arms
    are literally [RiscvLang.uart_step]/[plic_step]; the disk arm is
    [WeakLang.wdisk_step] SPLIT into a burst and one emit per message, which
    is what makes it 1:1 with the pf disk agent (design doc, the disk row). *)

Definition euart_step (σ σ' : egstate) : Prop :=
  exists d', uart_step (egdev σ) d' /\
    σ' = EGState (egregs σ) (egimg σ) (eglog σ) (egws σ) d' (eggen σ)
                 (egpow σ) (eg_hs σ) (eg_fence σ) (eg_pend σ) (eg_dws σ).

(** THE PLIC THREAD delivers ONE interrupt, to a hart it chooses: exactly
    [RiscvLang.plic_step]'s [PlicStepWire] (it writes [sig_seip] from the same
    wire [DevModel.dev_seip]), spelled through the hart's own delivery EVENT
    so that a plic-thread step and a hart-thread delivery produce the LITERALLY
    SAME successor — which is what makes the S2 correspondence map this arm to
    a pf step of the TARGET agent rather than of an agent-less thread.  (The
    [<[c := _]>] and [eset_at] spellings agree only pointwise, and this tree
    assumes no functional extensionality; going through [eirq_step] is how the
    two are kept syntactically equal.) *)
Definition eplic_step (σ σ' : egstate) : Prop :=
  exists c : CPU, eirq_step σ c σ'.

(** THE BURST: one [wdisk_step] at the flat projection of image+log, loading
    the canonical message list into [eg_pend].  Only at an EMPTY buffer, so
    a burst never clobbers messages still owed to the log. *)
Definition edisk_burst (σ σ' : egstate) : Prop :=
  eg_pend σ = [] /\
  exists d' w, wdisk_step (egdev σ) (wflat (egimg σ) (eglog σ)) d' w /\
    σ' = EGState (egregs σ) (egimg σ) (eglog σ) (egws σ) d' (eggen σ)
                 (egpow σ) (eg_hs σ) (eg_fence σ) (wmsgs_of_map w) (eg_dws σ).

(** THE EMIT: pop one buffered message and append it.  Its tid is already
    [Some n_disk] ([WeakLang.wmsgs_of_map] stamps it), so the disk's own
    view moves by [store_post_run] exactly as a pf [PFStore] would. *)
Definition edisk_emit (σ σ' : egstate) : Prop :=
  exists m rest, eg_pend σ = m :: rest /\
    (* the buffer is CANONICAL: [WeakLang.wmsgs_of_map] only ever produces
       one-byte messages stamped [Some n_disk] ([wmsgs_of_map_data],
       [wmsgs_of_map_tid]), and the pf disk agent's [PFStore] needs both *)
    wm_data m <> [] /\ wm_tid m = Some n_disk /\
    σ' = EGState (egregs σ) (egimg σ) (eglog σ ++ [m]) (egws σ) (egdev σ)
                 (eggen σ) (egpow σ) (eg_hs σ) (eg_fence σ) rest
                 (store_post_run (eg_dws σ) false (wm_pa m)
                    (length (wm_data m)) (S (length (eglog σ)))).

Definition edisk_step (σ σ' : egstate) : Prop :=
  edisk_burst σ σ' \/ edisk_emit σ σ'.

(* ====================================================================== *)
(** ** 5. Boot / crash reset

    [WeakLang.wboot_facts] with four clauses added for the new slots: every
    hart is AT A BOUNDARY with no parked fence, the disk's burst buffer is
    empty and its view is fresh. *)
Definition eboot_facts (σ' : egstate) : Prop :=
  wboot_facts (eg_to_wg σ')
  /\ (forall c : CPU, eg_hs σ' c = None)
  /\ (forall c : CPU, eg_fence σ' c = None)
  /\ eg_pend σ' = []
  /\ eg_dws σ' = ws_init.

Definition eboot_shape (σ σ' : egstate) : Prop :=
  eggen σ' = eggen σ
  /\ (egdev σ').(dvirtio) = virtio_reset (egdev σ).(dvirtio)
  /\ eboot_facts σ'.

Lemma eboot_facts_log σ' : eboot_facts σ' -> eglog σ' = [].
Proof. intros (H & _). exact (wboot_facts_log _ H). Qed.

Lemma eboot_facts_ws σ' : eboot_facts σ' -> forall c, egws σ' c = ws_init.
Proof. intros (H & _) c. exact (wboot_facts_ws _ H c). Qed.

(* ====================================================================== *)
(** ** 6. [eprim_step]: the five arms

    Exactly [WeakLang.wprim_step]'s shape — same live/corpse gating, same
    PowerOff generation bump, same PowerOn fork — with the hart arm replaced
    by ONE EVENT. *)

Definition ethread_live (σ : egstate) (gen : nat) : Prop :=
  egpow σ = true /\ eggen σ = gen.

Lemma ethread_live_wthread_live σ gen :
  ethread_live σ gen <-> wthread_live (eg_to_wg σ) gen.
Proof. reflexivity. Qed.

Definition eprim_step
    (e : mexpr) (σ : egstate) (κ : list mobs)
    (e' : mexpr) (σ' : egstate) (efs : list mexpr) : Prop :=
  (exists gen cpu, e = LoopE gen cpu /\ e' = LoopE gen cpu /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ ehart_step σ cpu σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (exists gen, e = UartLoopE gen /\ e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ euart_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (exists gen, e = DiskLoopE gen /\ e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ edisk_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (exists gen, e = PlicLoopE gen /\ e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ eplic_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (e = PowerLoopE /\ e' = PowerLoopE /\ κ = [] /\
    ((egpow σ = true /\ efs = [] /\
       σ' = EGState (egregs σ) (egimg σ) (eglog σ) (egws σ) (egdev σ)
                    (S (eggen σ)) false (eg_hs σ) (eg_fence σ) (eg_pend σ)
                    (eg_dws σ))
     \/
     (egpow σ = false /\ efs = power_fork (eggen σ) /\ eboot_shape σ σ'))).

Lemma weak_ev_lang_mixin : LanguageMixin of_val to_val eprim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs
      [(gen & cpu & -> & _) | [(gen & -> & _) | [(gen & -> & _)
       | [(gen & -> & _) | (-> & _)]]]];
      reflexivity.
Qed.

Definition weak_ev_lang : language := Language weak_ev_lang_mixin.

(* ====================================================================== *)
(** ** 7. Per-arm inversion *)

Lemma eprim_step_loop_inv gen cpu σ κ e' σ' efs :
  eprim_step (LoopE gen cpu) σ κ e' σ' efs ->
  e' = LoopE gen cpu /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ ehart_step σ cpu σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(gen0 & cpu0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as -> ->. by split_and!.
Qed.

Lemma eprim_step_uart_inv gen σ κ e' σ' efs :
  eprim_step (UartLoopE gen) σ κ e' σ' efs ->
  e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ euart_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_disk_inv gen σ κ e' σ' efs :
  eprim_step (DiskLoopE gen) σ κ e' σ' efs ->
  e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ edisk_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_plic_inv gen σ κ e' σ' efs :
  eprim_step (PlicLoopE gen) σ κ e' σ' efs ->
  e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ eplic_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_power_inv σ κ e' σ' efs :
  eprim_step PowerLoopE σ κ e' σ' efs ->
  e' = PowerLoopE /\ κ = [] /\
  ((egpow σ = true /\ efs = [] /\
     σ' = EGState (egregs σ) (egimg σ) (eglog σ) (egws σ) (egdev σ)
                  (S (eggen σ)) false (eg_hs σ) (eg_fence σ) (eg_pend σ)
                  (eg_dws σ))
   \/ (egpow σ = false /\ efs = power_fork (eggen σ) /\ eboot_shape σ σ')).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (_ & ? & ? & Harm)]]]];
    try discriminate Heq.
  by split_and!.
Qed.

(* ====================================================================== *)
(** ** 8. Cross-arm sanity lemmas (S3's state-interpretation obligations) *)

(** THE ERA-INITIAL IMAGE IS FIXED for the whole generation. *)
Lemma ehart_step_img σ c σ' : ehart_step σ c σ' -> egimg σ' = egimg σ.
Proof.
  rewrite /ehart_step. destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { by intros ->. }
  intros [Hirq|H]; [by rewrite Hirq|].
  destruct (eg_hs σ c) as [m|]; [|by destruct H as (tick & ->)].
  destruct m as [y|T oc k]; [by rewrite H|].
  destruct oc; simpl in H; try (by rewrite H); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _).
    + by destruct H as (w & d' & _ & ->).
    + destruct H as (_ & [(w & tvs & _ & _ & _ & ->)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           _ & _ & _ & _ & _ & _ & _ & _ & ->)]); reflexivity.
  - (* MemWrite *)
    destruct (dev_addr _).
    + by destruct H as (d' & _ & ->).
    + by destruct H as (_ & ->).
  - (* Choose *) by destruct H as (ch & ->).
Qed.

(** THE LOG IS APPEND-ONLY at every arm except a PowerOn. *)
Lemma ehart_step_log_app σ c σ' :
  ehart_step σ c σ' -> exists ms, eglog σ' = eglog σ ++ ms.
Proof.
  rewrite /ehart_step. destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { intros ->. exists []. by rewrite app_nil_r. }
  intros [Hirq|H]; [rewrite Hirq; exists []; by rewrite app_nil_r|].
  destruct (eg_hs σ c) as [m|];
    [|destruct H as (tick & ->); exists []; by rewrite app_nil_r].
  destruct m as [y|T oc k];
    [rewrite H; exists []; by rewrite app_nil_r|].
  destruct oc; simpl in H;
    try (rewrite H; exists []; by rewrite app_nil_r); try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _).
    + destruct H as (w & d' & _ & ->). exists []. by rewrite app_nil_r.
    + destruct H as (_ & [(w & tvs & _ & _ & _ & ->)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           _ & _ & _ & _ & _ & _ & _ & _ & ->)]).
      * exists []. by rewrite app_nil_r.
      * by eexists.
  - (* MemWrite *)
    destruct (dev_addr _).
    + destruct H as (d' & _ & ->). exists []. by rewrite app_nil_r.
    + destruct H as (_ & ->). by eexists.
  - (* Choose *) destruct H as (ch & ->). exists []. by rewrite app_nil_r.
Qed.

Lemma eprim_step_log_app e σ κ e' σ' efs :
  eprim_step e σ κ e' σ' efs ->
  (e = PowerLoopE -> egpow σ = true) ->
  exists ms, eglog σ' = eglog σ ++ ms.
Proof.
  intros Hstep Hpow.
  destruct Hstep as [(gen & cpu & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm) | (-> & _ & _ & Harm)]]]].
  - destruct Harm as [(_ & Hh)|(_ & ->)];
      [exact (ehart_step_log_app _ _ _ Hh)|exists []; by rewrite app_nil_r].
  - destruct Harm as [(_ & (d' & _ & ->))|(_ & ->)];
      exists []; by rewrite app_nil_r.
  - destruct Harm as [(_ & [(_ & d' & w & _ & ->)|(m & rest & _ & _ & _ & ->)])|(_ & ->)];
      [exists []; by rewrite app_nil_r|by eexists|exists []; by rewrite app_nil_r].
  - destruct Harm as [(_ & (c0 & ->))|(_ & ->)];
      exists []; by rewrite app_nil_r.
  - destruct Harm as [(_ & _ & ->)|(Hoff & _ & _)].
    + exists []. by rewrite app_nil_r.
    + rewrite (Hpow eq_refl) in Hoff. discriminate Hoff.
Qed.

Lemma eprim_step_img e σ κ e' σ' efs :
  eprim_step e σ κ e' σ' efs ->
  (e = PowerLoopE -> egpow σ = true) ->
  egimg σ' = egimg σ.
Proof.
  intros Hstep Hpow.
  destruct Hstep as [(gen & cpu & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm) | (-> & _ & _ & Harm)]]]].
  - destruct Harm as [(_ & Hh)|(_ & ->)]; [exact (ehart_step_img _ _ _ Hh)|reflexivity].
  - by destruct Harm as [(_ & (d' & _ & ->))|(_ & ->)].
  - by destruct Harm as [(_ & [(_ & d' & w & _ & ->)|(m & rest & _ & _ & _ & ->)])|(_ & ->)].
  - by destruct Harm as [(_ & (c0 & ->))|(_ & ->)].
  - destruct Harm as [(_ & _ & ->)|(Hoff & _ & _)]; [reflexivity|].
    rewrite (Hpow eq_refl) in Hoff. discriminate Hoff.
Qed.

(** VIEWS ONLY RISE, AND ONLY THE STEPPING HART'S. *)
Lemma ehart_step_ws_other σ c σ' c' :
  ehart_step σ c σ' -> c' <> c -> egws σ' c' = egws σ c'.
Proof.
  rewrite /ehart_step. intros H Hne.
  revert H. destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { by intros ->; apply ehart_set_ws_ne. }
  intros [Hirq|H]; [by rewrite Hirq; apply ehart_set_ws_ne|].
  destruct (eg_hs σ c) as [m|];
    [|destruct H as (tick & ->); by apply ehart_set_ws_ne].
  destruct m as [y|T oc k]; [by rewrite H; apply ehart_set_ws_ne|].
  destruct oc; simpl in H;
    try (by rewrite H; apply ehart_set_ws_ne); try (by destruct H).
  - destruct (dev_addr _).
    + destruct H as (w & d' & _ & ->). by apply ehart_set_ws_ne.
    + destruct H as (_ & [(w & tvs & _ & _ & _ & ->)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           _ & _ & _ & _ & _ & _ & _ & _ & ->)]);
        by apply ehart_set_ws_ne.
  - destruct (dev_addr _).
    + destruct H as (d' & _ & ->). by apply ehart_set_ws_ne.
    + destruct H as (_ & ->). by apply ehart_set_ws_ne.
  - destruct H as (ch & ->). by apply ehart_set_ws_ne.
Qed.

Lemma ehart_step_ws_le σ c σ' :
  ehart_step σ c σ' -> ws_le (egws σ c) (egws σ' c).
Proof.
  rewrite /ehart_step. destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { intros ->. rewrite ehart_set_ws_eq. apply fence_post_le. }
  intros [Hirq|H]; [rewrite Hirq ehart_set_ws_eq; reflexivity|].
  destruct (eg_hs σ c) as [m|];
    [|destruct H as (tick & ->); rewrite ehart_set_ws_eq; reflexivity].
  destruct m as [y|T oc k]; [rewrite H ehart_set_ws_eq; reflexivity|].
  destruct oc; simpl in H;
    try (rewrite H ehart_set_ws_eq; reflexivity); try (by destruct H).
  - destruct (dev_addr _).
    + destruct H as (w & d' & _ & ->). rewrite ehart_set_ws_eq. reflexivity.
    + destruct H as (_ & [(w & tvs & _ & _ & _ & ->)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           _ & _ & _ & _ & _ & _ & _ & _ & ->)]);
        rewrite ehart_set_ws_eq.
      * apply load_post_run_le.
      * etrans; [apply load_post_run_le|apply store_post_run_le].
  - destruct (dev_addr _).
    + destruct H as (d' & _ & ->). rewrite ehart_set_ws_eq. reflexivity.
    + destruct H as (_ & ->). rewrite ehart_set_ws_eq. apply store_post_run_le.
  - (* Barrier *) rewrite H ehart_set_ws_eq. apply efence_apply_le.
  - (* Choose *) destruct H as (ch & ->). rewrite ehart_set_ws_eq. reflexivity.
Qed.

(** The device threads move NO hart's view. *)
Lemma euart_step_ws σ σ' : euart_step σ σ' -> egws σ' = egws σ.
Proof. by intros (d' & _ & ->). Qed.
Lemma eplic_step_ws σ σ' : eplic_step σ σ' -> forall c, egws σ' c = egws σ c.
Proof.
  intros (c0 & ->) c. rewrite /eirq_step /=. rewrite /eset_at.
  by destruct (decide (c = c0)) as [->|].
Qed.
Lemma edisk_step_ws σ σ' : edisk_step σ σ' -> egws σ' = egws σ.
Proof. by intros [(_ & d' & w & _ & ->)|(m & rest & _ & _ & _ & ->)]. Qed.

(** THE DURABLE DISK IMAGE moves only in the disk's own burst arm. *)
Lemma ehart_step_v_disk σ c σ' :
  ehart_step σ c σ' ->
  exists d, egdev σ' = d /\
    (d = egdev σ \/
     (exists pa n w, dev_read (egdev σ) pa n = Some (w, d)) \/
     (exists pa n (v : bv (8 * n)), dev_write (egdev σ) pa n v = Some d)).
Proof.
  rewrite /ehart_step. destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { intros ->. eexists. split; [reflexivity|by left]. }
  intros [Hirq|H]; [rewrite Hirq; eexists; split; [reflexivity|by left]|].
  destruct (eg_hs σ c) as [m|];
    [|destruct H as (tick & ->); eexists; split; [reflexivity|by left]].
  destruct m as [y|T oc k];
    [rewrite H; eexists; split; [reflexivity|by left]|].
  destruct oc; simpl in H;
    try (rewrite H; eexists; split; [reflexivity|by left]); try (by destruct H).
  - destruct (dev_addr _) eqn:Hd.
    + destruct H as (w & d' & Hr & ->). eexists. split; [reflexivity|].
      right; left. by do 3 eexists.
    + destruct H as (_ & [(w & tvs & _ & _ & _ & ->)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           _ & _ & _ & _ & _ & _ & _ & _ & ->)]);
        eexists; (split; [reflexivity|by left]).
  - destruct (dev_addr _) eqn:Hd.
    + destruct H as (d' & Hw & ->). eexists. split; [reflexivity|].
      right; right. by do 3 eexists.
    + destruct H as (_ & ->). eexists. split; [reflexivity|by left].
  - destruct H as (ch & ->). eexists. split; [reflexivity|by left].
Qed.

(* ====================================================================== *)
(** ** 9. Reducibility helpers

    A CORPSE always steps; the live device threads always step (each relation
    has a premise-free stutter or an unconditional arm); the power thread
    steps while the power is on. *)

Lemma eprim_step_loop_dead gen cpu σ :
  ~ ethread_live σ gen -> eprim_step (LoopE gen cpu) σ [] (LoopE gen cpu) σ [].
Proof. intros Hd. left. exists gen, cpu. split_and!; try reflexivity. by right. Qed.

Lemma eprim_step_uart_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (UartLoopE gen) σ [] (UartLoopE gen) σ [].
Proof. intros Hd. right; left. exists gen. split_and!; try reflexivity. by right. Qed.

Lemma eprim_step_disk_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (DiskLoopE gen) σ [] (DiskLoopE gen) σ [].
Proof.
  intros Hd. right; right; left. exists gen. split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_plic_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (PlicLoopE gen) σ [] (PlicLoopE gen) σ [].
Proof.
  intros Hd. right; right; right; left. exists gen.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_power_off σ :
  egpow σ = true ->
  eprim_step PowerLoopE σ [] PowerLoopE
    (EGState (egregs σ) (egimg σ) (eglog σ) (egws σ) (egdev σ)
             (S (eggen σ)) false (eg_hs σ) (eg_fence σ) (eg_pend σ) (eg_dws σ))
    [].
Proof.
  intros Hon. right; right; right; right. split_and!; try reflexivity.
  left. by split_and!.
Qed.

Lemma eprim_step_uart_idle gen σ :
  ethread_live σ gen -> eprim_step (UartLoopE gen) σ [] (UartLoopE gen) σ [].
Proof.
  intros Hl. right; left. exists gen. split_and!; try reflexivity.
  left. split; [exact Hl|]. exists (egdev σ). split; [apply UartStepIdle|].
  by destruct σ.
Qed.

Lemma eprim_step_plic_wire gen σ (c : CPU) :
  ethread_live σ gen ->
  exists σ', eirq_step σ c σ' /\
    eprim_step (PlicLoopE gen) σ [] (PlicLoopE gen) σ' [].
Proof.
  intros Hl. eexists. split; [reflexivity|].
  right; right; right; left. exists gen.
  split_and!; try reflexivity. left. split; [exact Hl|].
  by exists c.
Qed.

(** THE BUFFER INVARIANT: every message the burst arm can load is a
    ONE-BYTE message stamped [Some n_disk] ([WeakLang.wmsgs_of_map_data],
    [wmsgs_of_map_tid]).  It is what makes the emit arm enabled, and it is
    what the pf disk agent's [PFStore] needs. *)
Definition epend_canon (σ : egstate) : Prop :=
  Forall (fun m => wm_data m <> [] /\ wm_tid m = Some n_disk) (eg_pend σ).

Lemma epend_canon_burst σ σ' : edisk_burst σ σ' -> epend_canon σ'.
Proof.
  intros (_ & d' & w & _ & ->). rewrite /epend_canon /=.
  apply Forall_forall. intros m Hm.
  split; [by eapply wmsgs_of_map_data|by eapply wmsgs_of_map_tid].
Qed.

Lemma epend_canon_emit σ σ' : epend_canon σ -> edisk_emit σ σ' -> epend_canon σ'.
Proof.
  intros Hc (m & rest & Hp & _ & _ & ->). rewrite /epend_canon /= .
  rewrite /epend_canon Hp in Hc. by apply Forall_cons in Hc as [_ ?].
Qed.

(** The disk is ALWAYS reducible: an empty buffer takes the idle burst
    ([WeakLang.WDiskStepIdle], whose write set is [∅] and hence buffers
    nothing), a canonical nonempty one emits. *)
Lemma eprim_step_disk_reducible gen σ :
  ethread_live σ gen -> epend_canon σ ->
  exists σ', eprim_step (DiskLoopE gen) σ [] (DiskLoopE gen) σ' [].
Proof.
  intros Hl Hc. destruct (eg_pend σ) as [|m rest] eqn:Hp.
  - eexists. right; right; left. exists gen. split_and!; try reflexivity.
    left. split; [exact Hl|]. left. split; [exact Hp|].
    exists (egdev σ), ∅. split; [apply WDiskStepIdle|].
    rewrite wmsgs_of_map_empty. by destruct σ.
  - rewrite /epend_canon Hp in Hc. apply Forall_cons in Hc as [[Hd Ht] _].
    eexists. right; right; left. exists gen. split_and!; try reflexivity.
    left. split; [exact Hl|]. right. exists m, rest. by split_and!.
Qed.

(** A LIVE HART is always reducible too — the interrupt-delivery arm needs
    nothing (delta (D5)), and a parked fence fires unconditionally.  This is
    the event-granular replacement for the instruction-level totality
    argument: no [sail_live], no completion premise. *)
Lemma eprim_step_loop_reducible gen cpu σ :
  ethread_live σ gen ->
  exists σ', eprim_step (LoopE gen cpu) σ [] (LoopE gen cpu) σ' [].
Proof.
  intros Hl. destruct (eg_fence σ cpu) as [[[[pr pw] sr] sw]|] eqn:Hf.
  - eexists. left. exists gen, cpu. split_and!; try reflexivity.
    left. split; [exact Hl|]. rewrite /ehart_step Hf. reflexivity.
  - eexists. left. exists gen, cpu. split_and!; try reflexivity.
    left. split; [exact Hl|]. rewrite /ehart_step Hf. left. reflexivity.
Qed.
