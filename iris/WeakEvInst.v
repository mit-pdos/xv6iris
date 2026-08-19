(** * WeakEvInst.v — THE PROGRAM/MEMORY FACTORIZATION of the event language's
      step (Phase B, part 1)

    Worklist: [claude-notes/projects/weak-memory-soundness.md] (Phase B, items
    B2 and B3, phase 1 = the LANGUAGE-SIDE half).  Design:
    [claude-notes/design/weak-memory-event-granular.md].

    ------------------------------------------------------------------------
    ** WHAT THIS FILE IS **

    Layer 1's promise-free machine is parametric in a PROGRAM STEP
    [P -> D -> wlabel -> P -> D -> Prop] which is LOG-BLIND and WSTATE-BLIND:
    everything the machine does to the log and to the views it does FROM THE
    LABEL alone.  [WeakEvLang]'s step relation is not written that way — each
    arm does its own σ-update inline.  This file FACTORS every arm of
    [WeakEvLang.ecycle_step] / [eplic_step] / [euart_step] / [edisk_step] into

      * a PROGRAM half   ([pstep_node] / [pstep_plic] / [pstep_disk]), which
        sees only the agent's own program state and the device fabric, and
      * a MEMORY half     ([elab_ok] + [elab_apply], and [edlab_ok] +
        [edlab_apply] + [edlab_ws] for the disk agent), which is a FUNCTION OF
        THE LABEL,

    and proves the two halves recompose to the language's own step, in BOTH
    directions (§5).  The pf-side wrapper (the actual [wp_pf_step] instance)
    is a LATER step and is deliberately not in this file: nothing here
    mentions Layer 1 at all, so this file is stable under Layer-1 edits.

    THE PLACEMENT RULE, restated for this file: the program half owns exactly
    what the language reads out of the EXPRESSION (the hart's residual monad
    and parked fence, the disk's residual DEVICE PROGRAM) plus the two
    σ-components that are agent-private or fabric-shared but label-invisible
    — the hart's REGISTERS and the DEVICE FABRIC.  The memory half owns the
    log and the [wstate]s.

    ------------------------------------------------------------------------
    ** THE FABRIC MARKER [LDev] (M5, LANDED) **

    Every arm that READS OR MOVES the device fabric carries the marker label
    [WeakPromise.LDev], whose memory half is [LSilent]'s verbatim: on the
    hart side the MMIO read, the MMIO write and the PLIC wire
    ([pstep_plic]); on the disk side the program START, the burst COMMIT,
    the PLIC LATCH and the UART thread.  [pdev_ev] therefore reads the
    marker off the LABEL alone, and [pdev_ev_ok] discharges
    [WeakPromiseFact.pdev_ok]: every other arm mentions the fabric exactly
    once, as [d' = d].

    ONE LABEL DECISION IS RECORDED IN THE OTHER DIRECTION: the [DWild] arm
    (a malformed descriptor chain becomes an arbitrary store chain) is
    [LSilent], NOT [LDev].  It reads nothing and moves nothing — it only
    replaces the residual program — so it is fabric-blind and
    fabric-preserving, [pdev_ok] holds for it, and marking it [LDev] would
    only put a spurious device event into the replay's device order.

    ** THE DISK IS AN ORDINARY AGENT (M5) **

    There is NO existential memory anywhere in this file any more.  The
    disk runs [VirtioProg.virtio_prog] node by node at its own [wstate]:
    [DRead] is a hart's plain RAM read ([LLoad aq false]), [DWrite] a
    hart's RAM write ([LStore false]), [DFence] a [fence rw,rw]
    ([LFence true true true true]).  So the ⇒ direction holds for EVERY
    disk arm, and [pdisk_burst]/[pstep_disk_at]/[pstep_disk_of_at] — the
    flat-memory scaffolding of the pre-M5 file — are GONE, together with
    [pdisk_emit] and the burst buffer's class hack.

    [pcls_ev] at the disk is now [WeakEvLang.ddev_class ws] — the class
    [WeakInterp.wm_class_of] computes for a PLAIN EXPLICIT store at the
    disk's own view, i.e. [WCrel] exactly when [w_relp] is armed (right
    after the device's [DFence]) and [WCplain] otherwise.  That is what the
    language's [DWrite] arm stamps, so the two agree by construction.

    ------------------------------------------------------------------------
    ** TWO RECORDED DEVIATIONS FROM THE COMMISSIONED SHAPE, AND WHY **

    (D1) THE REGISTER UPDATE IS AN [option regstate], NOT A [regstate].
         [WeakLang.wgstate]'s register file is a FUNCTION [CPU -> regstate]
         and [RiscvLang.greg_insert] is its pointwise update, so
         [<[c := gr c]> gr = gr] is NOT provable without functional
         extensionality — and this tree takes no such axiom.  A σ-transformer
         that ALWAYS inserts therefore cannot reproduce the language's
         [σ' = σ] on the arms that do not write registers.  So the program
         half reports whether it wrote registers: [None] = unchanged,
         [Some rs'] = written.  This costs nothing at the Layer-1 seam — the
         successor program state is [PHart c m' (default rs ors) fn'] — and it
         keeps every equation in §5 a LITERAL equality of [wgstate]s.

    (D2) [fence.i] CARRIES THE INERT LABEL [LFence false false false false],
         not [LSilent].  Same reason, one level down: the language's barrier
         arm ALWAYS re-inserts the hart's [wstate]
         ([ewg_ws σ c (efence_apply ws (ebar_now b))]), including at
         [Barrier_RISCV_i] where the value is unchanged, so an [LSilent]
         label — under which the memory half must leave [wgws] alone — could
         not reproduce it.  [fence_post ws false false false false = ws]
         ([fence_post_id]), so the label is inert in the machine as well; and
         it is arguably the more faithful reading, a [fence.i] being a fence
         event that happens to order nothing.

    ------------------------------------------------------------------------
    ** THE LAYOUT **

      §1  the program state (from [WeakEvPf]) and the class function
      §2  the program half: [pnode_step], [pstep_node], [pstep_plic],
          [pstep_hart], [pdisk_prog], [pdisk_uart], [pstep_disk],
          [pstep_ev], [pdev_ev]
      §3  the memory half: [elab_ok] / [elab_apply] (harts),
          [edlab_ok] / [edlab_apply] / [edlab_ws] (the disk agent)
      §4  the σ-shape lemmas ([elab_apply] = the language's named updater)
      §5  THE FACTORIZATION THEOREMS
      §6  lat-freedom and timestamp-obliviousness of the program half
      §7  [pdev_ev_ok] : [WeakPromiseFact.pdev_ok pstep_ev pdev_ev] *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
(* required BEFORE [WeakInterpProj]: see [WeakEvLang]'s note on [wbytes] *)
Require Import VirtioProg.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The program state and the class it writes

    The program type is [WeakEvPf.pexv6] — [PHart cpu m rs fn] (the CPU is
    carried because the PLIC wire's hart index is program data) and
    [PDisk pend].  [pcls_ev] is the class the LANGUAGE stamps on the message
    its store event appends: [WeakEvLang.emonad_step]'s [MemWrite] arm
    computes [wm_class_of (classify ak) ws] at the storing hart's own view,
    the fused RMW stamps [WCexcl] outright, and the disk emits the message
    its burst buffered. *)

(** The class off the [MemWrite] node the hart is sitting at. *)
Definition pnode_wclass (m : M unit) (ws : wstate) : wm_class :=
  match m with
  | Interface.Ret _ => WCplain
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> wm_class with
       | Interface.MemWrite n req => fun _ =>
           wm_class_of (classify (Interface.WriteReq.access_kind req)) ws
       | _ => fun _ => WCplain
       end) k
  end.

Definition pcls_ev (p : pexv6) (l : wlabel) (ws : wstate) : wm_class :=
  match l with
  | LRmw _ _ _ _ _ _ _ => WCexcl
  | LStore _ _ _ _ _ =>
      match p with
      | PHart _ m _ _ _ => pnode_wclass m ws
      (* M5: the device's stores are plain explicit stores, so their class
         is [WeakEvLang.ddev_class] — [WCrel] exactly when the disk's own
         [w_relp] is armed, i.e. right after its [DFence]. *)
      | PDisk _ => ddev_class ws
      end
  (* THE RMW SPLIT (S3): the conditional write COMPUTES its class exactly as
     a plain store does, and that computation returns [WCexcl] — the fused
     [LRmw]'s constant — because [WeakInterp.wm_class_of] answers [WCexcl]
     at [ak_latest], which is precisely what a conditional
     ([Write_RISCV_conditional*], i.e. [AK_explicit AV_exclusive]) write
     sets.  See [pcls_ev_exstore_excl] below: the walker's A/D write-back
     and every AMO keep the class they had before the split.  Computing it
     (rather than stamping [WCexcl]) is what keeps the factorization
     theorem's conditional-write arm a CONVERSION. *)
  | LExStore _ _ _ _ _ =>
      match p with
      | PHart _ m _ _ _ => pnode_wclass m ws
      | PDisk _ => ddev_class ws
      end
  | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
  | LCtrl _ | LInstr | LExLoad _ _ _ _ => WCplain
  end.

(** THE CLASS DID NOT MOVE (RMW split S3), machine-checked: at the node the
    conditional write is emitted from, [pcls_ev] returns the fused arm's
    [WCexcl]. *)
Lemma pcls_ev_exstore_excl (cpu : CPU) (n : N) (req : Interface.WriteReq.t n)
    K rs fn ib ws rl base data asrc vsrc :
  ak_latest (classify (Interface.WriteReq.access_kind req)) = true ->
  pcls_ev (PHart cpu (Interface.Next (Interface.MemWrite n req) K) rs fn ib)
    (LExStore rl base data asrc vsrc) ws = WCexcl.
Proof. intros Hlat. rewrite /pcls_ev /pnode_wclass /wm_class_of Hlat //. Qed.

Lemma pcls_ev_silent p ws : pcls_ev p LSilent ws = WCplain.
Proof. reflexivity. Qed.

Lemma pcls_ev_ldev p ws : pcls_ev p LDev ws = WCplain.
Proof. reflexivity. Qed.

Lemma pcls_ev_fence p ws pr pw sr sw : pcls_ev p (LFence pr pw sr sw) ws = WCplain.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 2. The program half

    [WeakEvLang.emonad_step] ARM FOR ARM, with every log/[wstate] side
    condition and every σ-effect replaced by the LABEL that carries it.  What
    is left is exactly what a Layer-1 program step may see: the residual
    monad, the registers, the parked fence and the device fabric. *)

(** The inert-fence-inclusive barrier label (deviation (D2)). *)
Definition ebar_label (b : barrier_kind) : wlabel :=
  match ebar_now b with
  | Some (pr, pw, sr, sw) => LFence pr pw sr sw
  | None => LFence false false false false
  end.

(** THE MONAD-NODE DISPATCH.  [ors] is the register write (deviation (D1)). *)
Definition pnode_step (m : M unit) (rs : regstate) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) : Prop :=
  match m with
  | Interface.Ret _ =>
      (* THE BOUNDARY: the hart is at the monad's terminal value and fetches
         a fresh instruction. *)
      exists tick : bool,
        l = LSilent /\ m' = riscv_step tick /\ ors = None /\ fn' = None /\
        d' = d /\
        (* D3: THE BOUNDARY CLEARS THE ANNOUNCED BITS ([WeakEvLang]'s
           [ewg_ib σ c None]) — a hart between instructions has no roles. *)
        oib = Some None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       | Interface.RegRead r _ => fun k =>
           l = LSilent /\ m' = k (register_lookup r rs) /\ ors = None /\
           fn' = None /\ d' = d /\ oib = None
       (* D3-2: PARM's [step_assign] at the instruction's architectural
          destination, PARM's [step_if] at [nextPC], [LSilent] elsewhere —
          all three are [WeakEvLang.erw_label] of the classification. *)
       | Interface.RegWrite r _ v => fun k =>
           l = erw_label (erw_of (deps_of_ib ib) r) /\
           m' = k tt /\ ors = Some (register_set r v rs) /\
           fn' = None /\ d' = d /\ oib = None
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req)
           then (* MMIO READ — FABRIC-TOUCHING, hence the marker [LDev] *)
             exists w : bv (8 * n),
               dev_read d (Interface.ReadReq.pa req) n = Some (w, d') /\
               l = LDev /\ m' = k (inl (w, None)) /\ ors = None /\
               fn' = None /\ oib = None
           else
             ak_coh (classify (Interface.ReadReq.access_kind req)) = false /\
             ((* the PLAIN RAM read; NO [read_ok] here — that is the
                 machine's, and it is [elab_ok] of the label *)
              (ak_latest (classify (Interface.ReadReq.access_kind req)) = false /\
               exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                 length tvs = N.to_nat n /\
                 (forall j : nat, (j < N.to_nat n)%nat ->
                    tvs.*2 !! j = Some (nth_byte w j)) /\
                 l = LLoad (ak_sync (classify (Interface.ReadReq.access_kind req)))
                       false (pa_z (Interface.ReadReq.pa req)) tvs [] /\
                 m' = k (inl (w, None)) /\ ors = None /\ fn' = None /\ d' = d /\
                 oib = None)
              \/
              (* THE EXCLUSIVE READ (RMW split S3); NO [read_ok] here
                 either — that is the machine's, i.e. [elab_ok] *)
              (ak_latest (classify (Interface.ReadReq.access_kind req)) = true /\
               exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                 length tvs = N.to_nat n /\
                 (forall j : nat, (j < N.to_nat n)%nat ->
                    tvs.*2 !! j = Some (nth_byte w j)) /\
                 l = LExLoad (ak_sync (classify (Interface.ReadReq.access_kind req)))
                       (pa_z (Interface.ReadReq.pa req)) tvs
                       (deps_asrc (deps_of_ib ib)) /\
                 m' = k (inl (w, None)) /\ ors = None /\ fn' = None /\ d' = d /\
                 oib = None))
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req)
           then (* MMIO WRITE — FABRIC-TOUCHING, hence the marker [LDev] *)
             dev_write d (Interface.WriteReq.pa req) n
               (Interface.WriteReq.value req) = Some d' /\
             l = LDev /\ m' = k (inl None) /\ ors = None /\ fn' = None /\
             oib = None
           else
             n <> 0%N /\
             ((ak_latest (classify (Interface.WriteReq.access_kind req)) = false /\
               l = LStore (ak_sync (classify (Interface.WriteReq.access_kind req)))
                     (pa_z (Interface.WriteReq.pa req))
                     (wbytes n (Interface.WriteReq.value req))
                     (deps_asrc (deps_of_ib ib)) (deps_vsrc (deps_of_ib ib)) /\
               m' = k (inl None) /\ ors = None /\ fn' = None /\ d' = d /\
               oib = None)
              \/
              (ak_latest (classify (Interface.WriteReq.access_kind req)) = true /\
               ((* THE CONDITIONAL WRITE (RMW split S3); the reservation and
                   the window are the machine's, i.e. [elab_ok] *)
                (l = LExStore (ak_sync (classify (Interface.WriteReq.access_kind req)))
                       (pa_z (Interface.WriteReq.pa req))
                       (wbytes n (Interface.WriteReq.value req))
                       (deps_asrc (deps_of_ib ib)) (deps_vsrc (deps_of_ib ib)) /\
                 m' = k (inl None) /\ ors = None /\ fn' = None /\ d' = d /\
                 oib = None)
                \/
                (* THE RETRY SELF-LOOP (design §5).  Memory-blind, as every
                   arm of the program half is: the node simply always ALSO
                   has a silent step back to itself, and [elab_ok LSilent]
                   admits it unconditionally. *)
                (l = LSilent /\
                 m' = Interface.Next (Interface.MemWrite n req) k /\
                 ors = None /\ fn' = None /\ d' = d /\ oib = None))))
       | Interface.Barrier b => fun k =>
           l = ebar_label b /\ m' = k tt /\ ors = None /\
           fn' = ebar_park b /\ d' = d /\ oib = None
       (* D3: THE ANNOUNCE RECORDS THE BITS.  Silent for the log, the
          views and the register file — a σ-write of [wgib] alone. *)
       | Interface.InstrAnnounce ob => fun k =>
           (* D3-2: the instruction START — [LInstr] resets the load-result
              bank (PARM's [res]) and the node records the bits. *)
           l = LInstr /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = Some (Some (ib_of_bvn ob))
       | Interface.BranchAnnounce _ _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.CacheOp _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.TlbOp _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.TakeException _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.ReturnException _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.TranslationStart _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.TranslationEnd _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.CycleCount => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.Message _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.GetCycleCount => fun k =>
           l = LSilent /\ m' = k (0%Z) /\ ors = None /\ fn' = None /\ d' = d /\
           oib = None
       | Interface.Choose _ => fun k =>
           exists ch, l = LSilent /\ m' = k ch /\ ors = None /\ fn' = None /\
             d' = d /\ oib = None
       (* GenericFail / Discard / a raised Sail exception: STUCK. *)
       | _ => fun _ => False
       end) k
  end.

(** THE HART'S OWN STEP, parked fence and all.  [cpu] is unused here (it is
    the PLIC disjunct that needs it); it is kept so that [pstep_node] and
    [pstep_plic] have the SAME signature. *)
Definition pstep_node (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) : Prop :=
  match fn with
  | Some (pr, pw, sr, sw) =>
      (* THE PARKED FENCE GATES EVERYTHING (WeakEvLang delta (D5)). *)
      l = LFence pr pw sr sw /\ m' = m /\ ors = None /\ fn' = None /\ d' = d /\
      oib = None
  | None => pnode_step m rs ib d l m' ors fn' d' oib
  end.

(** THE PLIC WIRE — a FABRIC-TOUCHING arm, its own disjunct (P1).  It is the
    PLIC thread's step DELIVERED TO HART [cpu]: available at ANY hart state,
    moving neither the monad nor the parked fence nor the fabric. *)
Definition pstep_plic (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) : Prop :=
  l = LDev /\ m' = m /\ fn' = fn /\ d' = d /\ oib = None /\
  ors = Some (register_set sig_seip (bool_to_bit (dev_seip d (fin_to_nat cpu)))
                rs).

Definition pstep_hart (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) : Prop :=
  pstep_node cpu m rs fn ib d l m' ors fn' d' oib
  \/ pstep_plic cpu m rs fn ib d l m' ors fn' d' oib.

(** THE DISK AGENT (M5).  One disjunct per node of the residual device
    program plus the three fabric arms; the UART thread is kept SEPARATE
    ([pdisk_uart]) because it is a step of the same agent but not of the
    device program, so the two language relations
    ([WeakEvLang.edisk_step] / [euart_step]) factor one each.  There is no
    existential memory anywhere any more: every arm that reads memory reads
    THROUGH THE LABEL. *)
Definition pdisk_prog (dp : option (DM dres)) (d : dev_state) (l : wlabel)
    (dp' : option (DM dres)) (d' : dev_state) : Prop :=
  (* START — reads the fabric *)
  (dp = None /\ l = LDev /\ dp' = Some (virtio_prog (dvirtio d)) /\ d' = d)
  \/
  (* DRead — a hart's plain RAM read, the continuation at the label's bytes *)
  (exists pa n aq k tvs,
     dp = Some (DRead pa n aq k) /\ length tvs = n /\
     l = LLoad aq false (pa_z pa) tvs [] /\ dp' = Some (k tvs.*2) /\ d' = d)
  \/
  (* DWrite — a hart's RAM write *)
  (exists pa bs k,
     dp = Some (DWrite pa bs k) /\ bs <> [] /\
     l = LStore false (pa_z pa) bs [] [] /\ dp' = Some k /\ d' = d)
  \/
  (* DFence — the device-side write barrier *)
  (exists k,
     dp = Some (DFence k) /\ l = LFence true true true true /\
     dp' = Some k /\ d' = d)
  \/
  (* COMMIT — moves the fabric *)
  (exists delta,
     dp = Some (DRet (DDone delta)) /\ l = LDev /\ dp' = None /\
     d' = set_dvirtio d (delta (dvirtio d)))
  \/
  (* the malformed chain.  LABEL DECISION (recorded): [LSilent], not
     [LDev] — this step reads nothing and moves nothing, it only replaces
     the residual program by an arbitrary store chain, so it is
     fabric-blind and fabric-preserving and [pdev_ok] holds for it.
     Marking it [LDev] would put a spurious device event into the
     replay's device order for no gain. *)
  (exists prog',
     dp = Some (DRet DWild) /\ dm_wild_chain prog' /\
     l = LSilent /\ dp' = Some prog' /\ d' = d)
  \/
  (* nothing pending *)
  (dp = Some (DRet DIdle) /\ l = LSilent /\ dp' = None /\ d' = d)
  \/
  (* THE PLIC LATCH — reads and moves the fabric *)
  (exists p',
     dev_irq_level d virtio_irq_id = true /\
     plic_latch (dplic d) virtio_irq_id = Some p' /\
     l = LDev /\ dp' = dp /\ d' = set_dplic d p').

(** THE UART THREAD, a fabric move of the disk agent that touches neither
    the residual program nor the log nor any view. *)
Definition pdisk_uart (dp : option (DM dres)) (d : dev_state) (l : wlabel)
    (dp' : option (DM dres)) (d' : dev_state) : Prop :=
  dp' = dp /\ l = LDev /\ uart_step d d'.

Definition pstep_disk (dp : option (DM dres)) (d : dev_state) (l : wlabel)
    (dp' : option (DM dres)) (d' : dev_state) : Prop :=
  pdisk_prog dp d l dp' d' \/ pdisk_uart dp d l dp' d'.

(** THE PROGRAM STEP, at Layer 1's type [P -> D -> wlabel -> P -> D -> Prop].
    Mismatched constructors are [False]. *)
Definition pstep_ev (p : pexv6) (d : dev_state) (l : wlabel)
    (p' : pexv6) (d' : dev_state) : Prop :=
  match p, p' with
  | PHart cpu m rs fn ib, PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu /\
      exists ors oib, rs' = default rs ors /\ ib' = default ib oib /\
        pstep_hart cpu m rs fn ib d l m' ors fn' d' oib
  | PDisk dp, PDisk dp' => pstep_disk dp d l dp' d'
  | _, _ => False
  end.

(** THE FABRIC MARKER.  [LDev] is exactly the label of the arms that read or
    move the device fabric — the two MMIO arms and the PLIC wire on the hart
    side, start/commit/latch and the UART on the disk side — so the marker
    is a function of the LABEL alone. *)
Definition pdev_ev (p : pexv6) (l : wlabel) (p' : pexv6) : bool :=
  match l with
  | LDev => true
  | LSilent | LLoad _ _ _ _ _ | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _
  | LFence _ _ _ _ | LRegW _ _ | LCtrl _ | LInstr
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => false
  end.

(* ====================================================================== *)
(** ** 3. The memory half: a SIDE CONDITION and a σ-TRANSFORMER, both
       functions of the LABEL

    [elab_ok] is exactly the per-label side condition of the promise-free
    machine's five arms; [elab_apply] is exactly its σ-effect.  Neither looks
    at the program. *)

Definition elab_ok (σ : wgstate) (c : CPU) (l : wlabel) : Prop :=
  match l with
  | LSilent => True
  | LLoad aq lat base tvs asrc =>
      asrc = [] /\
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq lat base tvs
  (* D3-2: the operand lists are REAL now, so the pins are gone and the
     RMW's read half is admissible at ITS OWN address view (PARM's
     [Local.read]: [view_pre ⊒ view(addr)]).  The LOAD arm keeps its pin —
     that IS deviation D-8. *)
  | LStore _ _ data asrc vsrc => data <> []
  | LRmw aq rl base tvs data asrc vsrc =>
      data <> [] /\ length tvs = length data /\
      read_ok_d (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs
        (srcs_view (wgws σ c) asrc) /\
      excl_ok (wglog σ) (fin_to_nat c) base tvs (S (length (wglog σ)))
  | LFence _ _ _ _ => True
  | LDev => True                (* the fabric marker: [LSilent]'s twin *)
  | LRegW _ _ | LCtrl _ | LInstr => True
  (* THE RMW SPLIT (S3): the side conditions of [WeakPromise.WPExLoad] /
     [WeakPromiseBridge.PFExLoad] and of [WPExStore]/[PFExStore], at this
     hart's own log and view.  The read half is [LLoad]'s at [lat := false]
     and at its OWN address view (deviation D-2, unpinned — see
     [WeakPromise.lb_ldepfree]); the write half is [LStore]'s plus §4's
     window, spelled once as [WeakPromise.exwin_ok]. *)
  | LExLoad aq base tvs asrc =>
      read_ok_d (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs
        (srcs_view (wgws σ c) asrc)
  | LExStore _ base data _ _ =>
      data <> [] /\
      exwin_ok (wglog σ) (fin_to_nat c) (wgws σ c) base (length data)
        (S (length (wglog σ)))
  end.

Definition eregs_apply (σ : wgstate) (c : CPU) (ors : option regstate)
    : CPU -> regstate :=
  match ors with
  | Some rs' => <[c := rs']> (wgregs σ)
  | None => wgregs σ
  end.

Definition elab_ws (σ : wgstate) (c : CPU) (l : wlabel) : CPU -> wstate :=
  match l with
  | LSilent => wgws σ
  | LLoad aq lat base tvs _ =>
      <[c := load_post_run (wgws σ c) aq base tvs.*1]> (wgws σ)
  | LStore rl base data asrc vsrc =>
      <[c := store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
               (srcs_view (wgws σ c) vsrc) base (length data)
               (S (length (wglog σ)))]> (wgws σ)
  | LRmw aq rl base tvs data asrc vsrc =>
      <[c := store_post_run_d
               (load_post_run_d (wgws σ c) aq (srcs_view (wgws σ c) asrc)
                  base tvs.*1)
               rl (srcs_view (wgws σ c) asrc) (srcs_view (wgws σ c) vsrc)
               base (length data) (S (length (wglog σ)))]> (wgws σ)
  | LFence pr pw sr sw => <[c := fence_post (wgws σ c) pr pw sr sw]> (wgws σ)
  | LDev => wgws σ              (* the fabric marker: [LSilent]'s twin *)
  | LRegW rd srcs =>
      <[c := regw_post (wgws σ c) rd (srcs_view (wgws σ c) srcs)]> (wgws σ)
  | LCtrl srcs =>
      <[c := ctrl_post (wgws σ c) (srcs_view (wgws σ c) srcs)]> (wgws σ)
  | LInstr => <[c := instr_post (wgws σ c)]> (wgws σ)
  | LExLoad aq base tvs asrc =>
      <[c := exload_post_run_d (wgws σ c) aq (srcs_view (wgws σ c) asrc)
               base tvs.*1]> (wgws σ)
  | LExStore rl base data asrc vsrc =>
      <[c := store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
               (srcs_view (wgws σ c) vsrc) base (length data)
               (S (length (wglog σ)))]> (wgws σ)
  end.

Definition elab_log (σ : wgstate) (c : CPU) (l : wlabel) (k : wm_class)
    : list wmsg :=
  match l with
  | LStore _ base data _ _ =>
      wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]
  | LRmw _ _ base _ data _ _ =>
      wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]
  (* THE RMW SPLIT (S3): the conditional write APPENDS, like a store. *)
  | LExStore _ base data _ _ =>
      wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]
  | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
  | LCtrl _ | LInstr | LExLoad _ _ _ _ => wglog σ
  end.

(** D3: the [eregs_apply] twin for the announced instruction bits.  [None]
    means "this node does not move them", exactly as for the register file;
    that is what keeps [elab_apply_silent] & co. record eta-equalities and
    keeps FUNCTIONAL EXTENSIONALITY out of the development. *)
Definition eib_apply (σ : wgstate) (c : CPU) (oib : option oib32)
    : CPU -> oib32 :=
  match oib with
  | Some v => <[c := v]> (wgib σ)
  | None => wgib σ
  end.

Definition elab_apply (σ : wgstate) (c : CPU) (l : wlabel) (k : wm_class)
    (ors : option regstate) (oib : option oib32) (d' : dev_state) : wgstate :=
  WGState (eregs_apply σ c ors) (wgimg σ) (elab_log σ c l k)
          (elab_ws σ c l) d' (wggen σ) (wgpow σ) (eib_apply σ c oib).

(** THE DISK AGENT'S VERSION.  Its [wstate] lives in the EXPRESSION
    ([WeakEvLang.EDisk]'s [dws]), not in σ, so the transformer splits in two:
    [edlab_apply] for σ and [edlab_ws] for the agent's own view.  The message
    tid is [WeakLang.n_disk]. *)
Definition edlab_ok (σ : wgstate) (dws : wstate) (l : wlabel) : Prop :=
  match l with
  | LSilent => True
  | LLoad aq lat base tvs asrc =>
      asrc = [] /\ read_ok (img_z (wgimg σ)) (wglog σ) dws aq lat base tvs
  | LStore _ _ data asrc vsrc => asrc = [] /\ vsrc = [] /\ data <> []
  | LFence _ _ _ _ => True
  | LDev => True                (* the fabric marker: [LSilent]'s twin *)
  (* the device has no atomic read-modify-write *)
  | LRmw _ _ _ _ _ _ _ => False
  | LRegW _ _ | LCtrl _ | LInstr => True
  (* THE RMW SPLIT (S3): the disk has no exclusives — the [LRmw]
     precedent one line up, and [pstep_disk_no_ex] is the proof. *)
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => False
  end.

Definition edlab_ws (σ : wgstate) (dws : wstate) (l : wlabel) : wstate :=
  match l with
  | LSilent => dws
  | LLoad aq lat base tvs _ => load_post_run dws aq base tvs.*1
  | LStore rl base data _ _ =>
      store_post_run dws rl base (length data) (S (length (wglog σ)))
  | LRmw aq rl base tvs data _ _ =>
      store_post_run (load_post_run dws aq base tvs.*1) rl base (length data)
        (S (length (wglog σ)))
  | LFence pr pw sr sw => fence_post dws pr pw sr sw
  | LDev => dws                 (* the fabric marker: [LSilent]'s twin *)
  | LRegW rd srcs => regw_post dws rd (srcs_view dws srcs)
  | LCtrl srcs => ctrl_post dws (srcs_view dws srcs)
  | LInstr => instr_post dws
  | LExLoad aq base tvs _ => load_post_run dws aq base tvs.*1
  | LExStore rl base data _ _ =>
      store_post_run dws rl base (length data) (S (length (wglog σ)))
  end.

Definition edlab_log (σ : wgstate) (l : wlabel) (k : wm_class) : list wmsg :=
  match l with
  | LStore _ base data _ _ => wglog σ ++ [WMsg base data (Some n_disk) k]
  | LRmw _ _ base _ data _ _ => wglog σ ++ [WMsg base data (Some n_disk) k]
  (* THE RMW SPLIT (S3): the conditional write APPENDS, like a store. *)
  | LExStore _ base data _ _ => wglog σ ++ [WMsg base data (Some n_disk) k]
  | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
  | LCtrl _ | LInstr | LExLoad _ _ _ _ => wglog σ
  end.

Definition edlab_apply (σ : wgstate) (l : wlabel) (k : wm_class)
    (d' : dev_state) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (edlab_log σ l k) (wgws σ) d' (wggen σ)
          (wgpow σ) (wgib σ).

(* ====================================================================== *)
(** ** 4. [elab_apply] IS the language's named σ-updater

    One lemma per shape of [WeakEvLang] §2 — this is where the factorization
    is actually paid for, and every one of them is a conversion. *)

Lemma fence_post_id ws : fence_post ws false false false false = ws.
Proof. rewrite /fence_post /=. by destruct ws. Qed.

Lemma elab_apply_silent σ c k : elab_apply σ c LSilent k None None (wgdev σ) = σ.
Proof. rewrite /elab_apply /=. by destruct σ. Qed.

Lemma elab_apply_dev σ c k d' :
  elab_apply σ c LSilent k None None d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

(** ... and the same at the FABRIC MARKER, whose memory half is [LSilent]'s
    verbatim.  These are what the MMIO arms and the PLIC wire use since M5. *)
Lemma elab_apply_ldev σ c k d' :
  elab_apply σ c LDev k None None d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

Lemma elab_apply_ldev_reg σ c k rs' :
  elab_apply σ c LDev k (Some rs') None (wgdev σ) = ewg_reg σ c rs'.
Proof. reflexivity. Qed.

Lemma elab_apply_reg σ c k rs' :
  elab_apply σ c LSilent k (Some rs') None (wgdev σ) = ewg_reg σ c rs'.
Proof. reflexivity. Qed.

Lemma elab_apply_load σ c k aq lat base tvs :
  elab_apply σ c (LLoad aq lat base tvs []) k None None (wgdev σ)
  = ewg_ws σ c (load_post_run (wgws σ c) aq base tvs.*1).
Proof. reflexivity. Qed.

Lemma elab_apply_fence σ c k pr pw sr sw :
  elab_apply σ c (LFence pr pw sr sw) k None None (wgdev σ)
  = ewg_ws σ c (fence_post (wgws σ c) pr pw sr sw).
Proof. reflexivity. Qed.

Lemma elab_apply_store σ c k rl base data asrc vsrc :
  elab_apply σ c (LStore rl base data asrc vsrc) k None None (wgdev σ)
  = ewg_store σ c
      (store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
         (srcs_view (wgws σ c) vsrc) base (length data)
         (S (length (wglog σ))))
      (wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]).
Proof. reflexivity. Qed.

(** THE RMW SPLIT (S3): the two halves' σ-shapes.  The exclusive read is a
    pure view move ([ewg_ws], exactly the plain load's shape) and the
    conditional write is the plain store's ([ewg_store]) — which is the
    whole content of "the split reuses the ordinary node rules". *)
Lemma elab_apply_exload σ c k aq base tvs asrc :
  elab_apply σ c (LExLoad aq base tvs asrc) k None None (wgdev σ)
  = ewg_ws σ c (exload_post_run_d (wgws σ c) aq (srcs_view (wgws σ c) asrc)
                  base tvs.*1).
Proof. reflexivity. Qed.

Lemma elab_apply_exstore σ c k rl base data asrc vsrc :
  elab_apply σ c (LExStore rl base data asrc vsrc) k None None (wgdev σ)
  = ewg_store σ c
      (store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
         (srcs_view (wgws σ c) vsrc) base (length data)
         (S (length (wglog σ))))
      (wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]).
Proof. reflexivity. Qed.

(** D3-2: THE REGISTER WRITE, all three kinds at once — the label and the
    σ-effect are [WeakEvLang.erw_label] / [ewg_rw] of the SAME
    classification, so this one conversion covers [LSilent], [LRegW] and
    [LCtrl]. *)
Lemma elab_apply_rw σ c k rs' (w : erw_kind) :
  elab_apply σ c (erw_label w) k (Some rs') None (wgdev σ)
  = ewg_rw σ c rs' w.
Proof. by destruct w. Qed.

(** ... and the announce: [LInstr]'s view effect plus the bits. *)
Lemma elab_apply_instr σ c k v :
  elab_apply σ c LInstr k None (Some v) (wgdev σ)
  = ewg_ibws σ c v (instr_post (wgws σ c)).
Proof. reflexivity. Qed.

(** D3: THE ANNOUNCE AND THE BOUNDARY — a σ-write of [wgib] and nothing
    else.  [WeakGhost.weak_state_interp] does not mention [wgib], so this
    shape is invisible to every WP rule (the acceptance test). *)
Lemma elab_apply_ib σ c k v :
  elab_apply σ c LSilent k None (Some v) (wgdev σ) = ewg_ib σ c v.
Proof. reflexivity. Qed.

(** The barrier arm: the label of (D2) reproduces [efence_apply] exactly. *)
Lemma elab_apply_barrier σ c k b :
  elab_apply σ c (ebar_label b) k None None (wgdev σ)
  = ewg_ws σ c (efence_apply (wgws σ c) (ebar_now b)).
Proof.
  destruct b; try reflexivity.
  cbn [ebar_label ebar_now efence_apply].
  by rewrite elab_apply_fence fence_post_id.
Qed.

Lemma edlab_apply_silent σ k : edlab_apply σ LSilent k (wgdev σ) = σ.
Proof. rewrite /edlab_apply /=. by destruct σ. Qed.

Lemma edlab_apply_ldev_id σ k : edlab_apply σ LDev k (wgdev σ) = σ.
Proof. rewrite /edlab_apply /=. by destruct σ. Qed.

Lemma edlab_apply_load_id σ k aq lat base tvs :
  edlab_apply σ (LLoad aq lat base tvs []) k (wgdev σ) = σ.
Proof. rewrite /edlab_apply /=. by destruct σ. Qed.

Lemma edlab_apply_fence_id σ k pr pw sr sw :
  edlab_apply σ (LFence pr pw sr sw) k (wgdev σ) = σ.
Proof. rewrite /edlab_apply /=. by destruct σ. Qed.

Lemma edlab_apply_dev σ k d' : edlab_apply σ LSilent k d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

Lemma edlab_apply_ldev σ k d' : edlab_apply σ LDev k d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

Lemma edlab_apply_store σ k rl base data :
  edlab_apply σ (LStore rl base data [] []) k (wgdev σ)
  = ewg_log σ (wglog σ ++ [WMsg base data (Some n_disk) k]).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 5. THE FACTORIZATION THEOREMS

    Each is an ↔ between one relation of [WeakEvLang] and the composition of
    §2's program half with §3's memory half.  The pf-side wrapper is then one
    line per arm. *)

(** Four goals, in the order of the statement: the expression, the program
    half, the side condition, the σ-update. *)
Local Ltac efac4 := split; [|split; [|split]].

Local Ltac esil_case :=
  split;
  [ intros (-> & ->); do 6 eexists; efac4;
    [reflexivity|split_and!; reflexivity|exact I
    |by rewrite elab_apply_silent]
  | intros (l & m' & ors & fn' & d' & oib & He & Hp & _ & Hs);
    destruct Hp as (-> & -> & -> & -> & -> & ->); subst;
    split; [reflexivity|by rewrite elab_apply_silent] ].

Local Ltac estuck_case :=
  split; [by intros []
         |intros (? & ? & ? & ? & ? & ? & ? & HF & ?); destruct HF].

Theorem ecycle_step_factor gen σ (c : CPU) (m : M unit)
    (fn : option (bool * bool * bool * bool)) e' σ' :
  ecycle_step gen σ c m fn e' σ' <->
  exists (l : wlabel) (m' : M unit) (ors : option regstate)
         (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
         (oib : option oib32),
    e' = Sail gen c m' fn' /\
    pstep_node c m (wgregs σ c) fn (wgib σ c) (wgdev σ) l m' ors fn' d' oib /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l
           (pcls_ev (PHart c m (wgregs σ c) fn (wgib σ c)) l (wgws σ c))
           ors oib d'.
Proof.
  rewrite /ecycle_step /pstep_node.
  destruct fn as [[[[pr pw] sr] sw]|].
  { (* THE PARKED FENCE gates everything *)
    split.
    - intros (-> & ->). do 6 eexists. efac4;
        [reflexivity|split_and!; reflexivity|exact I
        |by rewrite elab_apply_fence].
    - intros (l & m' & ors & fn' & d' & oib & He & Hp & _ & Hs).
      destruct Hp as (-> & -> & -> & -> & -> & ->). subst.
      split; [reflexivity|by rewrite elab_apply_fence]. }
  rewrite /emonad_step /pnode_step.
  destruct m as [y|T oc k].
  { (* THE BOUNDARY: the terminal value fetches a fresh instruction *)
    split.
    - intros (tick & -> & ->). do 6 eexists. efac4;
        [reflexivity|by exists tick|exact I|by rewrite elab_apply_ib].
    - intros (l & m' & ors & fn' & d' & oib & He
              & (tick & -> & -> & -> & -> & -> & ->) & _ & Hs); subst.
      exists tick. split; [reflexivity|by rewrite elab_apply_ib]. }
  destruct oc; simpl; try esil_case; try estuck_case.
  - (* RegWrite — D3-2: the label is the classification's, and [elab_ok] of
       all three kinds is [True] *)
    split.
    + intros (-> & ->). do 6 eexists. efac4;
        [reflexivity|split_and!; reflexivity
        |by destruct (erw_of _ _)
        |by rewrite elab_apply_rw].
    + intros (l & m' & ors & fn' & d' & oib & He & Hp & _ & Hs).
      destruct Hp as (-> & -> & -> & -> & -> & ->). subst.
      split; [reflexivity|by rewrite elab_apply_rw].
  - (* MemRead *)
    destruct (dev_addr _).
    + (* MMIO READ — the fabric answers (P1) *)
      split.
      * intros (w & d1 & Hrd & -> & ->). do 6 eexists. efac4;
          [reflexivity
          |exists w; split_and!; [exact Hrd|reflexivity..]
          |exact I
          |by rewrite elab_apply_ldev].
      * intros (l & m' & ors & fn' & d' & oib & He
                & (w & Hrd & -> & -> & -> & -> & ->) & _ & Hs); subst.
        exists w, d'. split_and!; [exact Hrd|reflexivity|].
        by rewrite elab_apply_ldev.
    + split.
      * intros (Hcoh & [(Hlat & w & tvs & Hlen & Hby & Hrd & -> & ->)
                       |(Hlat & w & tvs & Hlen & Hby & Hrd & -> & ->)]).
        { (* the PLAIN RAM read *)
          do 6 eexists. efac4;
            [reflexivity
            |split; [exact Hcoh|]; left; split; [exact Hlat|];
             exists w, tvs; split_and!; [exact Hlen|exact Hby|reflexivity..]
            |split; [reflexivity|exact Hrd]
            |by rewrite elab_apply_load]. }
        { (* THE EXCLUSIVE READ (RMW split S3) *)
          do 6 eexists. efac4;
            [reflexivity
            |split; [exact Hcoh|]; right; split; [exact Hlat|];
             exists w, tvs; split_and!; [exact Hlen|exact Hby|reflexivity..]
            |exact Hrd
            |by rewrite elab_apply_exload]. }
      * intros (l & m' & ors & fn' & d' & oib & He &
                (Hcoh & [(Hlat & w & tvs & Hlen & Hby & -> & -> & -> & -> & ->
                          & ->)
                        |(Hlat & w & tvs & Hlen & Hby & -> & -> & -> & -> & ->
                          & ->)]) & Hok & Hs); subst.
        { split; [exact Hcoh|]. left. split; [exact Hlat|].
          exists w, tvs. split_and!;
            [exact Hlen|exact Hby|by destruct Hok as (_ & Hrd)|reflexivity
            |by rewrite elab_apply_load]. }
        { split; [exact Hcoh|]. right. split; [exact Hlat|].
          exists w, tvs. split_and!;
            [exact Hlen|exact Hby|exact Hok|reflexivity
            |by rewrite elab_apply_exload]. }
  - (* MemWrite *)
    destruct (dev_addr _).
    + (* MMIO WRITE — the fabric absorbs it (P1) *)
      split.
      * intros (d1 & Hwr & -> & ->). do 6 eexists. efac4;
          [reflexivity|split_and!; [exact Hwr|reflexivity..]|exact I
          |by rewrite elab_apply_ldev].
      * intros (l & m' & ors & fn' & d' & oib & He
                & (Hwr & -> & -> & -> & -> & ->) & _ & Hs); subst.
        exists d'. split_and!; [exact Hwr|reflexivity|].
        by rewrite elab_apply_ldev.
    + split.
      * intros (Hn & [(Hlat & -> & ->)
                     |(Hlat & [(Hex & -> & ->)|(-> & ->)])]).
        { do 6 eexists. efac4;
            [reflexivity
            |split; [exact Hn|]; left; split_and!; [exact Hlat|reflexivity..]
            |by apply wbytes_ne|].
          rewrite elab_apply_store /= wbytes_length. reflexivity. }
        { (* THE CONDITIONAL WRITE (RMW split S3) *)
          do 6 eexists. efac4;
            [reflexivity
            |split; [exact Hn|]; right; split; [exact Hlat|];
             left; split_and!; reflexivity
            |split; [by apply wbytes_ne|rewrite wbytes_length; exact Hex]|].
          rewrite elab_apply_exstore /= wbytes_length. reflexivity. }
        { (* THE RETRY SELF-LOOP (design §5) *)
          do 6 eexists. efac4;
            [reflexivity
            |split; [exact Hn|]; right; split; [exact Hlat|];
             right; split_and!; reflexivity
            |exact I
            |by rewrite elab_apply_silent]. }
      * intros (l & m' & ors & fn' & d' & oib & He
                & (Hn & [(Hlat & -> & -> & -> & -> & -> & ->)
                        |(Hlat & [(-> & -> & -> & -> & -> & ->)
                                 |(-> & -> & -> & -> & -> & ->)])])
                & Hok & Hs); subst.
        { split; [exact Hn|]. left. split; [exact Hlat|]. split; [reflexivity|].
          rewrite elab_apply_store /= wbytes_length. reflexivity. }
        { destruct Hok as (_ & Hex). rewrite wbytes_length in Hex.
          split; [exact Hn|]. right. split; [exact Hlat|]. left.
          split_and!; [exact Hex|reflexivity|].
          rewrite elab_apply_exstore /= wbytes_length. reflexivity. }
        { split; [exact Hn|]. right. split; [exact Hlat|]. right.
          split; [reflexivity|by rewrite elab_apply_silent]. }
  - (* D3: THE ANNOUNCE — the instruction start.  It writes the bits ([oib],
       which is why it does not fall to [esil_case]) and, since D3-2, emits
       [LInstr]: the load-result bank is reset, and nothing else moves. *)
    split.
    + intros (-> & ->). do 6 eexists. efac4;
        [reflexivity|split_and!; reflexivity|exact I
        |by rewrite elab_apply_instr].
    + intros (l & m' & ors & fn' & d' & oib & He
              & (-> & -> & -> & -> & -> & ->) & _ & Hs); subst.
      split; [reflexivity|by rewrite elab_apply_instr].
  - (* Barrier — the inert [fence.i] label is deviation (D2) *)
    split.
    + intros (-> & ->). do 6 eexists. efac4;
        [reflexivity|split_and!; reflexivity| |by rewrite elab_apply_barrier].
      rewrite /elab_ok. by destruct b.
    + intros (l & m' & ors & fn' & d' & oib & He
              & (-> & -> & -> & -> & -> & ->) & _ & Hs); subst.
      split; [reflexivity|by rewrite elab_apply_barrier].
  - (* Choose *)
    split.
    + intros (ch & -> & ->). do 6 eexists. efac4;
        [reflexivity|by exists ch|exact I|by rewrite elab_apply_silent].
    + intros (l & m' & ors & fn' & d' & oib & He
              & (ch & -> & -> & -> & -> & -> & ->) & _ & Hs); subst.
      exists ch. split; [reflexivity|by rewrite elab_apply_silent].
Qed.

(** THE PLIC WIRE.  [pstep_plic] is available at ANY hart state, which is why
    the monad and the parked fence are universally quantified INSIDE. *)
Theorem eplic_step_factor σ σ' :
  eplic_step σ σ' <->
  exists (c : CPU) (l : wlabel) (ors : option regstate) (d' : dev_state),
    (forall (m : M unit) (fn : option (bool * bool * bool * bool)) (ib : oib32),
       pstep_plic c m (wgregs σ c) fn ib (wgdev σ) l m ors fn d' None) /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l WCplain ors None d'.
Proof.
  rewrite /eplic_step /pstep_plic. split.
  - intros (c & ->).
    exists c, LDev,
      (Some (register_set sig_seip
               (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c)))
               (wgregs σ c))), (wgdev σ).
    split_and!; [by intros m fn ib; split_and!|exact I|].
    by rewrite elab_apply_ldev_reg.
  - intros (c & l & ors & d' & Hp & _ & Hs).
    destruct (Hp (Interface.Ret tt) None None) as (-> & _ & _ & -> & _ & ->).
    exists c. by rewrite Hs elab_apply_ldev_reg.
Qed.

(** THE UART THREAD, a FABRIC move of the disk agent: it moves neither the
    residual device program nor the disk's own view. *)
Theorem euart_step_factor (dp : option (DM dres)) (dws : wstate) σ σ' :
  euart_step σ σ' <->
  exists (l : wlabel) (dp' : option (DM dres)) (d' : dev_state),
    pdisk_uart dp (wgdev σ) l dp' d' /\
    dp' = dp /\ edlab_ws σ dws l = dws /\
    edlab_ok σ dws l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk dp) l dws) d'.
Proof.
  rewrite /euart_step /pdisk_uart. split.
  - intros (d1 & Hu & ->). exists LDev, dp, d1.
    split_and!; try reflexivity; try exact I; try exact Hu;
      try (by rewrite edlab_apply_ldev).
  - intros (l & dp' & d' & (-> & -> & Hu) & _ & _ & _ & Hs).
    exists d'. split; [exact Hu|]. by rewrite Hs edlab_apply_ldev.
Qed.

(** THE DISK THREAD (M5) — the whole device program, arm for arm, with NO
    memory existential anywhere: every arm that reads memory reads through
    its label, exactly as a hart does.  The disk's [wstate] lives in the
    EXPRESSION, so the memory half splits: [edlab_ws] updates the
    expression's view and [edlab_apply] updates σ (the log and the
    fabric). *)
Theorem edisk_step_factor gen (dp : option (DM dres)) (dws : wstate) σ e' σ' :
  edisk_step gen dp dws σ e' σ' <->
  exists (l : wlabel) (dp' : option (DM dres)) (d' : dev_state),
    e' = EDisk gen dp' (edlab_ws σ dws l) /\
    pdisk_prog dp (wgdev σ) l dp' d' /\
    edlab_ok σ dws l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk dp) l dws) d'.
Proof.
  rewrite /edisk_step /pdisk_prog. split.
  - intros [(-> & -> & ->)
           |[(pa & n & aq & k & tvs & Hdp & Hlen & Hrd & -> & ->)
           |[(pa & bs & k & Hdp & Hne & -> & ->)
           |[(k & Hdp & -> & ->)
           |[(delta & Hdp & -> & ->)
           |[(prog' & Hdp & Hch & -> & ->)
           |[(Hdp & -> & ->)
           |(p' & Hlv & Hlt & -> & ->)]]]]]]].
    + (* START *)
      exists LDev, (Some (virtio_prog (dvirtio (wgdev σ)))), (wgdev σ).
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_ldev_id].
      left. by split_and!.
    + (* DRead *)
      eexists (LLoad aq false (pa_z pa) tvs []), (Some (k tvs.*2)), (wgdev σ).
      split_and!; [reflexivity| |split; [reflexivity|exact Hrd]
                  |by rewrite edlab_apply_load_id].
      right; left. exists pa, n, aq, k, tvs. by split_and!.
    + (* DWrite *)
      exists (LStore false (pa_z pa) bs [] []), (Some k), (wgdev σ).
      split_and!;
        [reflexivity| |split_and!; [reflexivity|reflexivity|exact Hne]
        |reflexivity].
      right; right; left. exists pa, bs, k. by split_and!.
    + (* DFence *)
      exists (LFence true true true true), (Some k), (wgdev σ).
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_fence_id].
      right; right; right; left. by exists k.
    + (* COMMIT *)
      exists LDev, None,
        (set_dvirtio (wgdev σ) (delta (dvirtio (wgdev σ)))).
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_ldev].
      right; right; right; right; left. by exists delta.
    + (* DWild *)
      exists LSilent, (Some prog'), (wgdev σ).
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_silent].
      right; right; right; right; right; left. by exists prog'.
    + (* DIdle *)
      exists LSilent, None, (wgdev σ).
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_silent].
      right; right; right; right; right; right; left. by split_and!.
    + (* the PLIC latch *)
      exists LDev, dp, (set_dplic (wgdev σ) p').
      split_and!; [reflexivity| |exact I|by rewrite edlab_apply_ldev].
      right; right; right; right; right; right; right. by exists p'.
  - intros (l & dp' & d' & He &
            [(-> & -> & -> & ->)
            |[(pa & n & aq & k & tvs & -> & Hlen & -> & -> & ->)
            |[(pa & bs & k & -> & Hne & -> & -> & ->)
            |[(k & -> & -> & -> & ->)
            |[(delta & -> & -> & -> & ->)
            |[(prog' & -> & Hch & -> & -> & ->)
            |[(-> & -> & -> & ->)
            |(p' & Hlv & Hlt & -> & -> & ->)]]]]]]] & Hok & Hs); subst.
    + left. split_and!; [reflexivity|reflexivity
                        |by rewrite edlab_apply_ldev_id].
    + right; left. exists pa, (length tvs), aq, k, tvs.
      split_and!; [reflexivity|reflexivity|by destruct Hok as (_ & Hrd)
                  |reflexivity|by rewrite edlab_apply_load_id].
    + right; right; left. exists pa, bs, k.
      split_and!; [reflexivity|by destruct Hok as (_ & _ & Hne')|reflexivity
                  |reflexivity].
    + right; right; right; left. exists k.
      split_and!; [reflexivity|reflexivity|by rewrite edlab_apply_fence_id].
    + right; right; right; right; left. exists delta.
      split_and!; [reflexivity|reflexivity|by rewrite edlab_apply_ldev].
    + right; right; right; right; right; left. exists prog'.
      split_and!; [reflexivity|exact Hch|reflexivity
                  |by rewrite edlab_apply_silent].
    + right; right; right; right; right; right; left.
      split_and!; [reflexivity|reflexivity|by rewrite edlab_apply_silent].
    + right; right; right; right; right; right; right. exists p'.
      split_and!; [exact Hlv|exact Hlt|reflexivity
                  |by rewrite edlab_apply_ldev].
Qed.

(** The two disk relations at the [pstep_disk] shape. *)
Corollary edisk_step_pstep_disk gen (dp : option (DM dres)) (dws : wstate)
    σ e' σ' :
  edisk_step gen dp dws σ e' σ' ->
  exists (l : wlabel) (dp' : option (DM dres)) (d' : dev_state),
    e' = EDisk gen dp' (edlab_ws σ dws l) /\
    pstep_disk dp (wgdev σ) l dp' d' /\
    edlab_ok σ dws l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk dp) l dws) d'.
Proof.
  intros H. apply edisk_step_factor in H as (l & dp' & d' & ? & Hd & ? & ?).
  exists l, dp', d'. split_and!; [done|by left|done|done].
Qed.

Corollary euart_step_pstep_disk (dp : option (DM dres)) (dws : wstate) σ σ' :
  euart_step σ σ' ->
  exists (l : wlabel) (d' : dev_state),
    pstep_disk dp (wgdev σ) l dp d' /\
    edlab_ws σ dws l = dws /\ edlab_ok σ dws l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk dp) l dws) d'.
Proof.
  intros H. apply (euart_step_factor dp dws) in H
    as (l & dp' & d' & Hu & -> & Hws & Hok & Hs).
  exists l, d'. split_and!; [by right|done|done|done].
Qed.

(** THE HART ARMS AT THE [pstep_hart] SHAPE: both the cycle event and the
    PLIC wire are one disjunct of the same program step. *)
Corollary ecycle_step_pstep_hart gen σ (c : CPU) m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' ->
  exists (l : wlabel) (m' : M unit) (ors : option regstate) fn' (d' : dev_state)
         (oib : option oib32),
    e' = Sail gen c m' fn' /\
    pstep_hart c m (wgregs σ c) fn (wgib σ c) (wgdev σ) l m' ors fn' d' oib /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l
           (pcls_ev (PHart c m (wgregs σ c) fn (wgib σ c)) l (wgws σ c))
           ors oib d'.
Proof.
  intros H. apply ecycle_step_factor in H
    as (l & m' & ors & fn' & d' & oib & ? & ? & ? & ?).
  exists l, m', ors, fn', d', oib. split_and!; [done|by left|done|done].
Qed.

Corollary eplic_step_pstep_hart σ σ' :
  eplic_step σ σ' ->
  exists (c : CPU) (l : wlabel) (ors : option regstate) (d' : dev_state),
    (forall (m : M unit) fn (ib : oib32),
       pstep_hart c m (wgregs σ c) fn ib (wgdev σ) l m ors fn d' None) /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l WCplain ors None d'.
Proof.
  intros H. apply eplic_step_factor in H as (c & l & ors & d' & Hp & ? & ?).
  exists c, l, ors, d'. split_and!; [|done|done].
  intros m fn ib. right. apply Hp.
Qed.

(* ====================================================================== *)
(** ** 6. Two properties of the program half alone

    LAT-FREEDOM: no arm ever emits a [lat = true] load — the language has no
    latest-read event at all (the fetch and the walker classify as ordinary
    coherent reads and are excluded from the RAM arm by [ak_coh]; the
    exclusive read is FUSED into [LRmw]).

    TIMESTAMP-OBLIVIOUSNESS: the continuation and the register write depend
    on the read VALUES only ([tvs.*2]), never on the timestamps — which is
    what lets the robustness replay re-time a run. *)

Lemma pnode_step_lat_free m rs ib d aq base tvs m' ors fn' d' oib :
  ~ pnode_step m rs ib d (LLoad aq true base tvs []) m' ors fn' d' oib.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _));
    try (intros (Hl & _); by destruct (erw_of (deps_of_ib ib) reg));
    try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (_ & [(_ & w & tvs0 & _ & _ & Hl & _)
                  |(_ & w & tvs0 & _ & _ & Hl & _)]); by simplify_eq.
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & [(_ & ? & _)|(_ & [(? & _)|(? & _)])]).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pstep_node_lat_free cpu m rs fn ib d aq base tvs m' ors fn' d' oib :
  ~ pstep_node cpu m rs fn ib d (LLoad aq true base tvs []) m' ors fn' d' oib.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (? & _).
  - apply pnode_step_lat_free.
Qed.

Lemma pstep_hart_lat_free cpu m rs fn ib d aq base tvs m' ors fn' d' oib :
  ~ pstep_hart cpu m rs fn ib d (LLoad aq true base tvs []) m' ors fn' d' oib.
Proof.
  intros [H|(H & _)]; [by eapply pstep_node_lat_free|done].
Qed.

(** The disk DOES load since M5 — but, exactly like a hart, never with
    [lat = true]: the device has no coherent/latest read. *)
Lemma pdisk_prog_lat_free dp d aq base tvs dp' d' :
  ~ pdisk_prog dp d (LLoad aq true base tvs []) dp' d'.
Proof.
  intros [(_ & Hl & _)
         |[(pa & n & aq0 & k & tvs0 & _ & _ & Hl & _)
         |[(pa & bs & k & _ & _ & Hl & _)
         |[(k & _ & Hl & _)
         |[(delta & _ & Hl & _)
         |[(prog' & _ & _ & Hl & _)
         |[(_ & Hl & _)
         |(p' & _ & _ & Hl & _)]]]]]]]; by simplify_eq.
Qed.

Lemma pstep_disk_lat_free dp d aq base tvs dp' d' :
  ~ pstep_disk dp d (LLoad aq true base tvs []) dp' d'.
Proof. intros [H|(_ & Hl & _)]; [by eapply pdisk_prog_lat_free|done]. Qed.

(** ... and no disk arm ever emits an [LRmw]. *)
Lemma pstep_disk_no_rmw dp d aq rl base tvs data asrc vsrc dp' d' :
  ~ pstep_disk dp d (LRmw aq rl base tvs data asrc vsrc) dp' d'.
Proof.
  intros [[(_ & Hl & _)
          |[(pa & n & aq0 & k & tvs0 & _ & _ & Hl & _)
          |[(pa & bs & k & _ & _ & Hl & _)
          |[(k & _ & Hl & _)
          |[(delta & _ & Hl & _)
          |[(prog' & _ & _ & Hl & _)
          |[(_ & Hl & _)
          |(p' & _ & _ & Hl & _)]]]]]]]
         |(_ & Hl & _)]; by simplify_eq.
Qed.

(** THE TIMESTAMP-OBLIVIOUSNESS of the disk's own load: the continuation
    takes [tvs.*2] and nothing else. *)
Lemma pdisk_prog_ts_load dp d aq base tvs tvs' dp' d' :
  pdisk_prog dp d (LLoad aq false base tvs []) dp' d' ->
  tvs'.*2 = tvs.*2 ->
  pdisk_prog dp d (LLoad aq false base tvs' []) dp' d'.
Proof.
  intros [(_ & Hl & _)
         |[(pa & n & aq0 & k & tvs0 & Hdp & Hlen & Hl & Hdp' & Hd)
         |[(pa & bs & k & _ & _ & Hl & _)
         |[(k & _ & Hl & _)
         |[(delta & _ & Hl & _)
         |[(prog' & _ & _ & Hl & _)
         |[(_ & Hl & _)
         |(p' & _ & _ & Hl & _)]]]]]]] Hts; try by simplify_eq.
  simplify_eq/=.
  have Hlen' : length tvs' = length tvs0.
  { by rewrite -(length_fmap snd tvs') -(length_fmap snd tvs0) Hts. }
  right; left. exists pa, (length tvs0), aq0, k, tvs'.
  split_and!; [reflexivity|exact Hlen'|reflexivity|by rewrite Hts|reflexivity].
Qed.

Lemma pstep_disk_ts_load dp d aq base tvs tvs' dp' d' :
  pstep_disk dp d (LLoad aq false base tvs []) dp' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_disk dp d (LLoad aq false base tvs' []) dp' d'.
Proof.
  intros [H|(_ & Hl & _)] Hts; [|done].
  left. by eapply pdisk_prog_ts_load.
Qed.

Theorem pstep_ev_lat_free p d aq base tvs p' d' :
  ~ pstep_ev p d (LLoad aq true base tvs []) p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn ib|dp], p' as [cpu' m' rs' fn' ib'|dp']; simpl;
    try (by intros []).
  - intros (_ & ors & oib & _ & _ & H). by eapply pstep_hart_lat_free.
  - apply pstep_disk_lat_free.
Qed.

Lemma pnode_step_ts_load m rs ib d aq base tvs tvs' m' ors fn' d' oib :
  pnode_step m rs ib d (LLoad aq false base tvs []) m' ors fn' d' oib ->
  tvs'.*2 = tvs.*2 ->
  pnode_step m rs ib d (LLoad aq false base tvs' []) m' ors fn' d' oib.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _));
    try (intros (Hl & _); by destruct (erw_of (deps_of_ib ib) reg));
    try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (Hcoh & [(Hlat & w & tvs0 & Hlen & Hby & Hl & Hrest)
                     |(_ & w & tvs0 & _ & _ & Hl & _)]) Hts; [|by simplify_eq].
      simplify_eq/=.
      have Hlen' : length tvs' = length tvs0.
      { by rewrite -(length_fmap snd tvs') -(length_fmap snd tvs0) Hts. }
      split; [exact Hcoh|]. left. split; [exact Hlat|].
      exists w, tvs'. split_and!; [by rewrite Hlen'|by rewrite Hts| | | | | |];
        by destruct Hrest as (-> & -> & -> & -> & ->).
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & [(_ & ? & _)|(_ & [(? & _)|(? & _)])]).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

(** THE RMW SPLIT (S3): NO HART ARM EMITS THE FUSED LABEL any more, so the
    fused clause of [WeakRobustSim.ts_oblivious] is discharged by refutation
    rather than by re-timing.  (The clause itself stays until the tower's
    pair-form re-index, S4.) *)
Lemma pnode_step_no_rmw m rs ib d aq rl base tvs data asrc vsrc m' ors fn' d' oib :
  ~ pnode_step m rs ib d (LRmw aq rl base tvs data asrc vsrc) m' ors fn' d' oib.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _));
    try (intros (Hl & _); by destruct (erw_of (deps_of_ib ib) reg));
    try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (_ & [(_ & w & tvs0 & _ & _ & Hl & _)
                  |(_ & w & tvs0 & _ & _ & Hl & _)]); by simplify_eq.
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & [(_ & ? & _)|(_ & [(? & _)|(? & _)])]).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pstep_node_ts_load cpu m rs fn ib d aq base tvs tvs' m' ors fn' d' oib :
  pstep_node cpu m rs fn ib d (LLoad aq false base tvs []) m' ors fn' d' oib ->
  tvs'.*2 = tvs.*2 ->
  pstep_node cpu m rs fn ib d (LLoad aq false base tvs' []) m' ors fn' d' oib.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (? & _).
  - apply pnode_step_ts_load.
Qed.

Lemma pstep_hart_no_rmw cpu m rs fn ib d aq rl base tvs data asrc vsrc m' ors fn' d' oib :
  ~ pstep_hart cpu m rs fn ib d (LRmw aq rl base tvs data asrc vsrc) m' ors fn' d' oib.
Proof.
  intros [Hn|(Hl & _)]; [|done].
  rewrite /pstep_node in Hn. destruct fn as [[[[pr pw] sr] sw]|].
  - by destruct Hn as (? & _).
  - by eapply pnode_step_no_rmw.
Qed.

Theorem pstep_ev_ts_load p d aq base tvs tvs' p' d' :
  pstep_ev p d (LLoad aq false base tvs []) p' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_ev p d (LLoad aq false base tvs' []) p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn ib|dp], p' as [cpu' m' rs' fn' ib'|dp']; simpl;
    try (by intros ? ?).
  - intros (-> & ors & oib & -> & -> & [H|(H & _)]) Hts; [|done].
    split; [reflexivity|]. exists ors, oib. split_and!; [reflexivity..|].
    left. by eapply pstep_node_ts_load.
  - apply pstep_disk_ts_load.
Qed.

Theorem pstep_ev_no_rmw p d aq rl base tvs data asrc vsrc p' d' :
  ~ pstep_ev p d (LRmw aq rl base tvs data asrc vsrc) p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn ib|dp], p' as [cpu' m' rs' fn' ib'|dp']; simpl;
    try (by intros []).
  - intros (_ & ors & oib & _ & _ & H). by eapply pstep_hart_no_rmw.
  - apply pstep_disk_no_rmw.
Qed.

Theorem pstep_ev_ts_rmw p d aq rl base tvs tvs' data asrc vsrc p' d' :
  pstep_ev p d (LRmw aq rl base tvs data asrc vsrc) p' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_ev p d (LRmw aq rl base tvs' data asrc vsrc) p' d'.
Proof. intros H. by destruct (pstep_ev_no_rmw _ _ _ _ _ _ _ _ _ _ _ H). Qed.

(* ====================================================================== *)
(** ** 7. THE FABRIC MARKER IS SOUND ([WeakPromiseFact.pdev_ok])

    The one law Layer 1's factorization asks of the marker: a step the
    marker calls NOT fabric-touching must leave the fabric alone AND be
    available at every fabric.  Since [pdev_ev] reads the marker off the
    LABEL, this is a case analysis in which every arm whose label is not
    [LDev] mentions the fabric exactly once, as [d' = d]. *)

Lemma pnode_step_dev_free m rs ib d l m' ors fn' d' oib :
  pnode_step m rs ib d l m' ors fn' d' oib -> l <> LDev ->
  d' = d /\ forall d0, pnode_step m rs ib d0 l m' ors fn' d0 oib.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { intros (tick & Hl & -> & -> & -> & -> & ->) _. split; [reflexivity|].
    intros d0. exists tick. by split_and!. }
  destruct oc; simpl;
    try (intros (Hl & -> & -> & -> & -> & ->) _; split; [reflexivity|];
         intros d0; by split_and!);
    try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + intros (w & Hrd & Hl & _) Hne. by destruct (Hne Hl).
    + intros (Hcoh & [(Hlat & w & tvs & Hlen & Hby & Hl & -> & -> & -> & ->
                       & ->)
                     |(Hlat & w & tvs & Hlen & Hby & Hl
                       & -> & -> & -> & -> & ->)]) _;
        (split; [reflexivity|]); intros d0.
      * split; [exact Hcoh|]. left. split; [exact Hlat|].
        exists w, tvs. by split_and!.
      * split; [exact Hcoh|]. right. split; [exact Hlat|].
        exists w, tvs. by split_and!.
  - (* MemWrite *) destruct (dev_addr _).
    + intros (Hwr & Hl & _) Hne. by destruct (Hne Hl).
    + intros (Hn & [(Hlat & Hl & -> & -> & -> & -> & ->)
                   |(Hlat & [(Hl & -> & -> & -> & -> & ->)
                            |(Hl & -> & -> & -> & -> & ->)])]) _;
        (split; [reflexivity|]); intros d0; split; try exact Hn.
      * left. by split_and!.
      * right. split; [exact Hlat|]. left. by split_and!.
      * right. split; [exact Hlat|]. right. by split_and!.
  - (* Choose *) intros (ch & Hl & -> & -> & -> & -> & ->) _.
    split; [reflexivity|]. intros d0. exists ch. by split_and!.
Qed.

Lemma pstep_node_dev_free cpu m rs fn ib d l m' ors fn' d' oib :
  pstep_node cpu m rs fn ib d l m' ors fn' d' oib -> l <> LDev ->
  d' = d /\ forall d0, pstep_node cpu m rs fn ib d0 l m' ors fn' d0 oib.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - intros (Hl & -> & -> & -> & -> & ->) _. split; [reflexivity|].
    intros d0. by split_and!.
  - apply pnode_step_dev_free.
Qed.

Lemma pdisk_prog_dev_free dp d l dp' d' :
  pdisk_prog dp d l dp' d' -> l <> LDev ->
  d' = d /\ forall d0, pdisk_prog dp d0 l dp' d0.
Proof.
  intros [(Hdp & Hl & _)
         |[(pa & n & aq & k & tvs & Hdp & Hlen & Hl & Hdp' & ->)
         |[(pa & bs & k & Hdp & Hbs & Hl & Hdp' & ->)
         |[(k & Hdp & Hl & Hdp' & ->)
         |[(delta & Hdp & Hl & _)
         |[(prog' & Hdp & Hch & Hl & Hdp' & ->)
         |[(Hdp & Hl & Hdp' & ->)
         |(p' & Hlv & Hlt & Hl & Hdp' & _)]]]]]]] Hne;
    try by destruct (Hne Hl).
  - split; [reflexivity|]. intros d0. right; left.
    exists pa, n, aq, k, tvs. by split_and!.
  - split; [reflexivity|]. intros d0. right; right; left.
    exists pa, bs, k. by split_and!.
  - split; [reflexivity|]. intros d0. right; right; right; left.
    exists k. by split_and!.
  - split; [reflexivity|]. intros d0.
    right; right; right; right; right; left. exists prog'. by split_and!.
  - split; [reflexivity|]. intros d0.
    right; right; right; right; right; right; left. by split_and!.
Qed.

Lemma pstep_disk_dev_free dp d l dp' d' :
  pstep_disk dp d l dp' d' -> l <> LDev ->
  d' = d /\ forall d0, pstep_disk dp d0 l dp' d0.
Proof.
  intros [H|(_ & Hl & _)] Hne; [|by destruct (Hne Hl)].
  destruct (pdisk_prog_dev_free _ _ _ _ _ H Hne) as (-> & Hall).
  split; [reflexivity|]. intros d0. by left.
Qed.

Theorem pdev_ev_ok : pdev_ok pstep_ev pdev_ev.
Proof.
  intros p d l p' d' Hs Hm.
  have Hne : l <> LDev.
  { intros ->. by rewrite /pdev_ev in Hm. }
  revert Hs. rewrite /pstep_ev.
  destruct p as [cpu m rs fn ib|dp], p' as [cpu' m' rs' fn' ib'|dp']; try done.
  - intros (-> & ors & oib & -> & -> & [Hn|(Hl & _)]); [|by destruct (Hne Hl)].
    destruct (pstep_node_dev_free _ _ _ _ _ _ _ _ _ _ _ _ Hn Hne)
      as (-> & Hall).
    split; [reflexivity|]. intros d0. split; [reflexivity|].
    exists ors, oib. split_and!; [reflexivity..|]. left. apply Hall.
  - intros Hs. destruct (pstep_disk_dev_free _ _ _ _ _ Hs Hne) as (-> & Hall).
    split; [reflexivity|]. intros d0. apply Hall.
Qed.

(** D3-2: THE **LOAD**-DEPENDENCY-FREEDOM OF THE INSTANCE.

    D2's [pstep_ev_depfree] is FALSE now — that is the whole point of the
    stage: stores and the fused RMW carry [deps_asrc]/[deps_vsrc], and the
    three dependency-only labels are emitted at the announce, at [nextPC]
    and at the architectural destination register.  What SURVIVES is the
    pin on LOADS ([WeakPromise.lb_ldepfree]), and that is deviation D-8: a
    load's data read and the page walker's PTE read are indistinguishable at
    the node, so attaching the base register to a read would be a
    STRENGTHENING beyond RVWMO's syntactic dependencies (the wrong
    polarity).  It is exactly the premise the capstone's uniform-shape
    inversion ([WeakEvCapstone.wp_pf_step_inv]) still needs.

    THE DISK is unchanged: [pstep_disk_depfree] below still gives the FULL
    [lb_depfree] (deviation D-6 — [virtio_prog] is not an ISA program and
    its ordering is aq/fence-based). *)
Lemma pnode_step_ldepfree m rs ib d l m' ors fn' d' oib :
  pnode_step m rs ib d l m' ors fn' d' oib -> lb_ldepfree l.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & -> & _). }
  destruct oc; simpl; try (by intros (-> & _));
    try (intros (-> & _); by destruct (erw_of (deps_of_ib ib) reg));
    try done.
  - (* MemRead *)
    destruct (dev_addr _); [by intros (? & _ & -> & _)|].
    intros (_ & [(_ & w & tvs & _ & _ & -> & _)
                |(_ & w & tvs & _ & _ & -> & _)]); done.
  - (* MemWrite *)
    destruct (dev_addr _); [by intros (_ & -> & _)|].
    by intros (_ & [(_ & -> & _)|(_ & [(-> & _)|(-> & _)])]).
  - (* Barrier *) intros (-> & _). by destruct b.
  - (* Choose *) by intros (ch & -> & _).
Qed.

Lemma pstep_node_ldepfree cpu m rs fn ib d l m' ors fn' d' oib :
  pstep_node cpu m rs fn ib d l m' ors fn' d' oib -> lb_ldepfree l.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (-> & _).
  - apply pnode_step_ldepfree.
Qed.

Lemma pstep_plic_ldepfree cpu m rs fn ib d l m' ors fn' d' oib :
  pstep_plic cpu m rs fn ib d l m' ors fn' d' oib -> lb_ldepfree l.
Proof. rewrite /pstep_plic. by intros (-> & _). Qed.

Lemma pstep_hart_ldepfree cpu m rs fn ib d l m' ors fn' d' oib :
  pstep_hart cpu m rs fn ib d l m' ors fn' d' oib -> lb_ldepfree l.
Proof.
  intros [H|H]; [by eapply pstep_node_ldepfree|by eapply pstep_plic_ldepfree].
Qed.

Lemma pstep_disk_depfree dp d l dp' d' :
  pstep_disk dp d l dp' d' -> lb_depfree l.
Proof.
  rewrite /pstep_disk /pdisk_prog /pdisk_uart.
  intros [[(_ & -> & _)
          |[(pa & n & aq & k & tvs & _ & _ & -> & _)
          |[(pa & bs & k & _ & _ & -> & _)
          |[(k & _ & -> & _)
          |[(dl & _ & -> & _)
          |[(pg & _ & _ & -> & _)
          |[(_ & -> & _)
          |(p' & _ & _ & -> & _)]]]]]]]
         |(_ & -> & _)]; by (exact I || split).
Qed.

Theorem pstep_ev_ldepfree p d l p' d' : pstep_ev p d l p' d' -> lb_ldepfree l.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn ib|dp], p' as [cpu' m' rs' fn' ib'|dp']; simpl;
    try (by intros []).
  - intros (_ & ors & oib & _ & _ & H). by eapply pstep_hart_ldepfree.
  - intros H. by apply lb_depfree_ldepfree, (pstep_disk_depfree _ _ _ _ _ H).
Qed.

(* ---------------------------------------------------------------------- *)
(** THE RMW SPLIT (S3): THE HART'S PRE-SPLIT-ALPHABET LEMMAS ARE GONE.
    [pnode_step_fused] / [pstep_node_fused] / [pstep_plic_fused] /
    [pstep_hart_fused] / [pstep_ev_fused] were the S2 residue "no producer
    emits the split pair yet"; the producers now do, so they are FALSE and
    are DELETED (the R3/S4 coupling ruling).  What the old capstone still
    needs is therefore an explicit hypothesis — see
    [WeakEvCapstone.xv6_ev_weak_robust]'s [Hfused].

    WHAT SURVIVES IS THE DISK'S HALF, and it is exactly what the task calls
    [pstep_disk_no_ex]: the device program has no exclusive access at all,
    so no disk arm emits [LExLoad] or [LExStore] (nor, as before, [LRmw]). *)

Lemma pstep_disk_no_ex dp d l dp' d' : pstep_disk dp d l dp' d' -> lb_fused l.
Proof.
  rewrite /pstep_disk /pdisk_prog /pdisk_uart.
  intros [[(_ & -> & _)
          |[(pa & n & aq & k & tvs & _ & _ & -> & _)
          |[(pa & bs & k & _ & _ & -> & _)
          |[(k & _ & -> & _)
          |[(dl & _ & -> & _)
          |[(pg & _ & _ & -> & _)
          |[(_ & -> & _)
          |(p' & _ & _ & -> & _)]]]]]]]
         |(_ & -> & _)]; exact I.
Qed.
