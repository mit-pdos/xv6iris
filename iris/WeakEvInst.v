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
    what the language reads out of the EXPRESSION (the residual monad, the
    parked fence, the disk's burst buffer) plus the two σ-components that are
    agent-private or fabric-shared but label-invisible — the hart's REGISTERS
    and the DEVICE FABRIC.  The memory half owns the log and the [wstate]s.

    ------------------------------------------------------------------------
    ** THE THREE PROVISIONAL POINTS (do not build on them) **

    (P1) [LDev].  A Layer-1 label [LDev] for fabric-touching silent steps is
         coming (the PLIC wire and the MMIO arms must be MARKED as device
         steps, and that is not decidable from [(p, LSilent, p')]).  Every
         fabric-touching arm is therefore ITS OWN DISJUNCT here — the MMIO
         read ([pnode_step]'s [dev_addr]-true branch), the MMIO write, the
         PLIC wire ([pstep_plic]), the disk burst ([pdisk_burst]) and the
         UART ([pdisk_uart]) — so that swapping its label to [LDev] is a
         ONE-LINE change per arm.

    (P2) THE BURST'S MEMORY IS EXISTENTIAL.  [pdisk_burst] takes the DMA's
         memory as an argument and [pstep_disk] quantifies it existentially,
         because a Layer-1 program step cannot read the log.  That is an
         OVER-approximation of the language (whose burst reads
         [WeakLang.wflat] of image+log), and it is why the ⇒ direction of the
         eventual instance does not hold at the burst arm.  Phase C (M5)
         replaces this arm outright; until then the factorization theorem
         [edisk_step_factor] is stated at the FLAT memory
         ([pdisk_burst (wflat (wgimg σ) (wglog σ))]), which is an honest ↔,
         and [pstep_disk_of_at] is the (one-way) weakening to the
         existential form.

    (P3) [pcls_ev] AT THE DISK reads the class off the head of the burst
         buffer ([wm_ak]) rather than being the constant [WCplain].  On every
         reachable configuration the two agree ([WeakLang.wmsgs_of_map]
         stamps [WCplain] and [WeakEvLang.epend_canon] is preserved), but
         only the [wm_ak] form makes [edisk_step_factor] an ↔ without an
         extra canonicity hypothesis.

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
          [pstep_hart], [pdisk_*], [pstep_disk], [pstep_ev]
      §3  the memory half: [elab_ok] / [elab_apply] (harts),
          [edlab_ok] / [edlab_apply] / [edlab_ws] (the disk agent)
      §4  the σ-shape lemmas ([elab_apply] = the language's named updater)
      §5  THE FACTORIZATION THEOREMS
      §6  lat-freedom and timestamp-obliviousness of the program half *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
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
  | LRmw _ _ _ _ _ => WCexcl
  | LStore _ _ _ =>
      match p with
      | PHart _ m _ _ => pnode_wclass m ws
      | PDisk (msg :: _) => wm_ak msg      (* (P3) *)
      | PDisk [] => WCplain
      end
  | _ => WCplain
  end.

Lemma pcls_ev_silent p ws : pcls_ev p LSilent ws = WCplain.
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
Definition pnode_step (m : M unit) (rs : regstate) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state) : Prop :=
  match m with
  | Interface.Ret _ =>
      (* THE BOUNDARY: the hart is at the monad's terminal value and fetches
         a fresh instruction. *)
      exists tick : bool,
        l = LSilent /\ m' = riscv_step tick /\ ors = None /\ fn' = None /\
        d' = d
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       | Interface.RegRead r _ => fun k =>
           l = LSilent /\ m' = k (register_lookup r rs) /\ ors = None /\
           fn' = None /\ d' = d
       | Interface.RegWrite r _ v => fun k =>
           l = LSilent /\ m' = k tt /\ ors = Some (register_set r v rs) /\
           fn' = None /\ d' = d
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req)
           then (* MMIO READ — a FABRIC-TOUCHING arm, its own disjunct (P1) *)
             exists w : bv (8 * n),
               dev_read d (Interface.ReadReq.pa req) n = Some (w, d') /\
               l = LSilent /\ m' = k (inl (w, None)) /\ ors = None /\
               fn' = None
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
                       false (pa_z (Interface.ReadReq.pa req)) tvs /\
                 m' = k (inl (w, None)) /\ ors = None /\ fn' = None /\ d' = d)
              \/
              (* THE FUSED RMW; NO [read_ok]/[excl_ok] here either *)
              (ak_latest (classify (Interface.ReadReq.access_kind req)) = true /\
               exists (w : bv (8 * n)) (tvs : list (nat * bv 8))
                      (data : list (bv 8)) (rl : bool) (m1 m2 : M unit)
                      (rs1 : regstate),
                 length tvs = N.to_nat n /\
                 (forall j : nat, (j < N.to_nat n)%nat ->
                    tvs.*2 !! j = Some (nth_byte w j)) /\
                 data <> [] /\ length tvs = length data /\
                 esilent_run (k (inl (w, None)), rs) (m1, rs1) /\
                 ewr_node m1 rl (pa_z (Interface.ReadReq.pa req)) data m2 /\
                 l = LRmw (ak_sync (classify (Interface.ReadReq.access_kind req)))
                       rl (pa_z (Interface.ReadReq.pa req)) tvs data /\
                 m' = m2 /\ ors = Some rs1 /\ fn' = None /\ d' = d))
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req)
           then (* MMIO WRITE — a FABRIC-TOUCHING arm, its own disjunct (P1) *)
             dev_write d (Interface.WriteReq.pa req) n
               (Interface.WriteReq.value req) = Some d' /\
             l = LSilent /\ m' = k (inl None) /\ ors = None /\ fn' = None
           else
             n <> 0%N /\
             l = LStore (ak_sync (classify (Interface.WriteReq.access_kind req)))
                   (pa_z (Interface.WriteReq.pa req))
                   (wbytes n (Interface.WriteReq.value req)) /\
             m' = k (inl None) /\ ors = None /\ fn' = None /\ d' = d
       | Interface.Barrier b => fun k =>
           l = ebar_label b /\ m' = k tt /\ ors = None /\
           fn' = ebar_park b /\ d' = d
       | Interface.InstrAnnounce _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.BranchAnnounce _ _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.CacheOp _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.TlbOp _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.TakeException _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.ReturnException _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.TranslationStart _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.TranslationEnd _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.CycleCount => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.Message _ => fun k =>
           l = LSilent /\ m' = k tt /\ ors = None /\ fn' = None /\ d' = d
       | Interface.GetCycleCount => fun k =>
           l = LSilent /\ m' = k (0%Z) /\ ors = None /\ fn' = None /\ d' = d
       | Interface.Choose _ => fun k =>
           exists ch, l = LSilent /\ m' = k ch /\ ors = None /\ fn' = None /\
             d' = d
       (* GenericFail / Discard / a raised Sail exception: STUCK. *)
       | _ => fun _ => False
       end) k
  end.

(** THE HART'S OWN STEP, parked fence and all.  [cpu] is unused here (it is
    the PLIC disjunct that needs it); it is kept so that [pstep_node] and
    [pstep_plic] have the SAME signature. *)
Definition pstep_node (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state) : Prop :=
  match fn with
  | Some (pr, pw, sr, sw) =>
      (* THE PARKED FENCE GATES EVERYTHING (WeakEvLang delta (D5)). *)
      l = LFence pr pw sr sw /\ m' = m /\ ors = None /\ fn' = None /\ d' = d
  | None => pnode_step m rs d l m' ors fn' d'
  end.

(** THE PLIC WIRE — a FABRIC-TOUCHING arm, its own disjunct (P1).  It is the
    PLIC thread's step DELIVERED TO HART [cpu]: available at ANY hart state,
    moving neither the monad nor the parked fence nor the fabric. *)
Definition pstep_plic (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state) : Prop :=
  l = LSilent /\ m' = m /\ fn' = fn /\ d' = d /\
  ors = Some (register_set sig_seip (bool_to_bit (dev_seip d (fin_to_nat cpu)))
                rs).

Definition pstep_hart (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state) : Prop :=
  pstep_node cpu m rs fn d l m' ors fn' d'
  \/ pstep_plic cpu m rs fn d l m' ors fn' d'.

(** THE DISK AGENT.  Three disjuncts, one per fabric event (P1): the DMA
    burst (whose memory is a parameter — (P2)), the emit of one buffered
    message, and the UART thread's move, which is a silent step of the
    fabric-owning agent. *)
Definition pdisk_burst (mem : gmap Arch.pa (bv 8)) (pend : list wmsg)
    (d : dev_state) (l : wlabel) (pend' : list wmsg) (d' : dev_state) : Prop :=
  pend = [] /\
  exists w, wdisk_step d mem d' w /\ pend' = wmsgs_of_map w /\ l = LSilent.

Definition pdisk_emit (pend : list wmsg) (d : dev_state) (l : wlabel)
    (pend' : list wmsg) (d' : dev_state) : Prop :=
  exists msg rest, pend = msg :: rest /\ pend' = rest /\ d' = d /\
    wm_data msg <> [] /\ wm_tid msg = Some n_disk /\
    l = LStore false (wm_pa msg) (wm_data msg).

Definition pdisk_uart (pend : list wmsg) (d : dev_state) (l : wlabel)
    (pend' : list wmsg) (d' : dev_state) : Prop :=
  pend' = pend /\ l = LSilent /\ uart_step d d'.

(** The disk agent's step AT A GIVEN DMA memory — the honest, language-side
    form. *)
Definition pstep_disk_at (mem : gmap Arch.pa (bv 8)) (pend : list wmsg)
    (d : dev_state) (l : wlabel) (pend' : list wmsg) (d' : dev_state) : Prop :=
  pdisk_burst mem pend d l pend' d' \/ pdisk_emit pend d l pend' d'
  \/ pdisk_uart pend d l pend' d'.

(** ... and the LAYER-1 form, whose burst memory is existential (P2). *)
Definition pstep_disk (pend : list wmsg) (d : dev_state) (l : wlabel)
    (pend' : list wmsg) (d' : dev_state) : Prop :=
  (exists mem, pdisk_burst mem pend d l pend' d')
  \/ pdisk_emit pend d l pend' d' \/ pdisk_uart pend d l pend' d'.

Lemma pstep_disk_of_at mem pend d l pend' d' :
  pstep_disk_at mem pend d l pend' d' -> pstep_disk pend d l pend' d'.
Proof. intros [H|[H|H]]; [left; by exists mem|by right;left|by right;right]. Qed.

(** THE PROGRAM STEP, at Layer 1's type [P -> D -> wlabel -> P -> D -> Prop].
    Mismatched constructors are [False]. *)
Definition pstep_ev (p : pexv6) (d : dev_state) (l : wlabel)
    (p' : pexv6) (d' : dev_state) : Prop :=
  match p, p' with
  | PHart cpu m rs fn, PHart cpu' m' rs' fn' =>
      cpu' = cpu /\
      exists ors, rs' = default rs ors /\
        pstep_hart cpu m rs fn d l m' ors fn' d'
  | PDisk pend, PDisk pend' => pstep_disk pend d l pend' d'
  | _, _ => False
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
  | LLoad aq lat base tvs =>
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq lat base tvs
  | LStore _ _ data => data <> []
  | LRmw aq rl base tvs data =>
      data <> [] /\ length tvs = length data /\
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs /\
      excl_ok (wglog σ) (fin_to_nat c) base tvs (S (length (wglog σ)))
  | LFence _ _ _ _ => True
  | LDev => True                (* the fabric marker: [LSilent]'s twin *)
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
  | LLoad aq lat base tvs =>
      <[c := load_post_run (wgws σ c) aq base tvs.*1]> (wgws σ)
  | LStore rl base data =>
      <[c := store_post_run (wgws σ c) rl base (length data)
               (S (length (wglog σ)))]> (wgws σ)
  | LRmw aq rl base tvs data =>
      <[c := store_post_run (load_post_run (wgws σ c) aq base tvs.*1)
               rl base (length data) (S (length (wglog σ)))]> (wgws σ)
  | LFence pr pw sr sw => <[c := fence_post (wgws σ c) pr pw sr sw]> (wgws σ)
  | LDev => wgws σ              (* the fabric marker: [LSilent]'s twin *)
  end.

Definition elab_log (σ : wgstate) (c : CPU) (l : wlabel) (k : wm_class)
    : list wmsg :=
  match l with
  | LStore _ base data =>
      wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]
  | LRmw _ _ base _ data =>
      wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]
  | _ => wglog σ
  end.

Definition elab_apply (σ : wgstate) (c : CPU) (l : wlabel) (k : wm_class)
    (ors : option regstate) (d' : dev_state) : wgstate :=
  WGState (eregs_apply σ c ors) (wgimg σ) (elab_log σ c l k)
          (elab_ws σ c l) d' (wggen σ) (wgpow σ).

(** THE DISK AGENT'S VERSION.  Its [wstate] lives in the EXPRESSION
    ([WeakEvLang.EDisk]'s [dws]), not in σ, so the transformer splits in two:
    [edlab_apply] for σ and [edlab_ws] for the agent's own view.  The message
    tid is [WeakLang.n_disk]. *)
Definition edlab_ok (σ : wgstate) (l : wlabel) : Prop :=
  match l with
  | LSilent => True
  | LStore _ _ data => data <> []
  | LFence _ _ _ _ => True
  | LDev => True                (* the fabric marker: [LSilent]'s twin *)
  | _ => False
  end.

Definition edlab_ws (σ : wgstate) (dws : wstate) (l : wlabel) : wstate :=
  match l with
  | LSilent => dws
  | LLoad aq lat base tvs => load_post_run dws aq base tvs.*1
  | LStore rl base data =>
      store_post_run dws rl base (length data) (S (length (wglog σ)))
  | LRmw aq rl base tvs data =>
      store_post_run (load_post_run dws aq base tvs.*1) rl base (length data)
        (S (length (wglog σ)))
  | LFence pr pw sr sw => fence_post dws pr pw sr sw
  | LDev => dws                 (* the fabric marker: [LSilent]'s twin *)
  end.

Definition edlab_log (σ : wgstate) (l : wlabel) (k : wm_class) : list wmsg :=
  match l with
  | LStore _ base data => wglog σ ++ [WMsg base data (Some n_disk) k]
  | LRmw _ _ base _ data => wglog σ ++ [WMsg base data (Some n_disk) k]
  | _ => wglog σ
  end.

Definition edlab_apply (σ : wgstate) (l : wlabel) (k : wm_class)
    (d' : dev_state) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (edlab_log σ l k) (wgws σ) d' (wggen σ)
          (wgpow σ).

(* ====================================================================== *)
(** ** 4. [elab_apply] IS the language's named σ-updater

    One lemma per shape of [WeakEvLang] §2 — this is where the factorization
    is actually paid for, and every one of them is a conversion. *)

Lemma fence_post_id ws : fence_post ws false false false false = ws.
Proof. rewrite /fence_post /=. by destruct ws. Qed.

Lemma elab_apply_silent σ c k : elab_apply σ c LSilent k None (wgdev σ) = σ.
Proof. rewrite /elab_apply /=. by destruct σ. Qed.

Lemma elab_apply_dev σ c k d' :
  elab_apply σ c LSilent k None d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

Lemma elab_apply_reg σ c k rs' :
  elab_apply σ c LSilent k (Some rs') (wgdev σ) = ewg_reg σ c rs'.
Proof. reflexivity. Qed.

Lemma elab_apply_load σ c k aq lat base tvs :
  elab_apply σ c (LLoad aq lat base tvs) k None (wgdev σ)
  = ewg_ws σ c (load_post_run (wgws σ c) aq base tvs.*1).
Proof. reflexivity. Qed.

Lemma elab_apply_fence σ c k pr pw sr sw :
  elab_apply σ c (LFence pr pw sr sw) k None (wgdev σ)
  = ewg_ws σ c (fence_post (wgws σ c) pr pw sr sw).
Proof. reflexivity. Qed.

Lemma elab_apply_store σ c k rl base data :
  elab_apply σ c (LStore rl base data) k None (wgdev σ)
  = ewg_store σ c
      (store_post_run (wgws σ c) rl base (length data) (S (length (wglog σ))))
      (wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]).
Proof. reflexivity. Qed.

Lemma elab_apply_rmw σ c k aq rl base tvs data rs1 :
  elab_apply σ c (LRmw aq rl base tvs data) k (Some rs1) (wgdev σ)
  = ewg_rmw σ c rs1
      (store_post_run (load_post_run (wgws σ c) aq base tvs.*1) rl base
         (length data) (S (length (wglog σ))))
      (wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]).
Proof. reflexivity. Qed.

(** The barrier arm: the label of (D2) reproduces [efence_apply] exactly. *)
Lemma elab_apply_barrier σ c k b :
  elab_apply σ c (ebar_label b) k None (wgdev σ)
  = ewg_ws σ c (efence_apply (wgws σ c) (ebar_now b)).
Proof.
  destruct b; try reflexivity.
  cbn [ebar_label ebar_now efence_apply].
  by rewrite elab_apply_fence fence_post_id.
Qed.

Lemma edlab_apply_silent σ k : edlab_apply σ LSilent k (wgdev σ) = σ.
Proof. rewrite /edlab_apply /=. by destruct σ. Qed.

Lemma edlab_apply_dev σ k d' : edlab_apply σ LSilent k d' = ewg_dev σ d'.
Proof. reflexivity. Qed.

Lemma edlab_apply_store σ k rl base data :
  edlab_apply σ (LStore rl base data) k (wgdev σ)
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
  [ intros (-> & ->); do 5 eexists; efac4;
    [reflexivity|split_and!; reflexivity|exact I
    |by rewrite elab_apply_silent]
  | intros (l & m' & ors & fn' & d' & He & Hp & _ & Hs);
    destruct Hp as (-> & -> & -> & -> & ->); subst;
    split; [reflexivity|by rewrite elab_apply_silent] ].

Local Ltac estuck_case :=
  split; [by intros []
         |intros (? & ? & ? & ? & ? & ? & HF & ?); destruct HF].

Theorem ecycle_step_factor gen σ (c : CPU) (m : M unit)
    (fn : option (bool * bool * bool * bool)) e' σ' :
  ecycle_step gen σ c m fn e' σ' <->
  exists (l : wlabel) (m' : M unit) (ors : option regstate)
         (fn' : option (bool * bool * bool * bool)) (d' : dev_state),
    e' = Sail gen c m' fn' /\
    pstep_node c m (wgregs σ c) fn (wgdev σ) l m' ors fn' d' /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l
           (pcls_ev (PHart c m (wgregs σ c) fn) l (wgws σ c)) ors d'.
Proof.
  rewrite /ecycle_step /pstep_node.
  destruct fn as [[[[pr pw] sr] sw]|].
  { (* THE PARKED FENCE gates everything *)
    split.
    - intros (-> & ->). do 5 eexists. efac4;
        [reflexivity|split_and!; reflexivity|exact I
        |by rewrite elab_apply_fence].
    - intros (l & m' & ors & fn' & d' & He & Hp & _ & Hs).
      destruct Hp as (-> & -> & -> & -> & ->). subst.
      split; [reflexivity|by rewrite elab_apply_fence]. }
  rewrite /emonad_step /pnode_step.
  destruct m as [y|T oc k].
  { (* THE BOUNDARY: the terminal value fetches a fresh instruction *)
    split.
    - intros (tick & -> & ->). do 5 eexists. efac4;
        [reflexivity|by exists tick|exact I|by rewrite elab_apply_silent].
    - intros (l & m' & ors & fn' & d' & He & (tick & -> & -> & -> & -> & ->)
              & _ & Hs); subst.
      exists tick. split; [reflexivity|by rewrite elab_apply_silent]. }
  destruct oc; simpl; try esil_case; try estuck_case.
  - (* RegWrite *)
    split.
    + intros (-> & ->). do 5 eexists. efac4;
        [reflexivity|split_and!; reflexivity|exact I
        |by rewrite elab_apply_reg].
    + intros (l & m' & ors & fn' & d' & He & Hp & _ & Hs).
      destruct Hp as (-> & -> & -> & -> & ->). subst.
      split; [reflexivity|by rewrite elab_apply_reg].
  - (* MemRead *)
    destruct (dev_addr _).
    + (* MMIO READ — the fabric answers (P1) *)
      split.
      * intros (w & d1 & Hrd & -> & ->). do 5 eexists. efac4;
          [reflexivity
          |exists w; split_and!; [exact Hrd|reflexivity..]
          |exact I
          |by rewrite elab_apply_dev].
      * intros (l & m' & ors & fn' & d' & He & (w & Hrd & -> & -> & -> & ->)
                & _ & Hs); subst.
        exists w, d'. split_and!; [exact Hrd|reflexivity|].
        by rewrite elab_apply_dev.
    + split.
      * intros (Hcoh & [(Hlat & w & tvs & Hlen & Hby & Hrd & -> & ->)
                       |(Hlat & w & tvs & data & rl & m1 & m2 & rs1 &
                         Hlen & Hby & Hrd & Hex & Hne & Hlend & Hsil & Hwr
                         & -> & ->)]).
        { (* the PLAIN RAM read *)
          do 5 eexists. efac4;
            [reflexivity
            |split; [exact Hcoh|]; left; split; [exact Hlat|];
             exists w, tvs; split_and!; [exact Hlen|exact Hby|reflexivity..]
            |exact Hrd
            |by rewrite elab_apply_load]. }
        { (* the FUSED RMW *)
          do 5 eexists. efac4;
            [reflexivity
            |split; [exact Hcoh|]; right; split; [exact Hlat|];
             exists w, tvs, data, rl, m1, m2, rs1;
             split_and!; [exact Hlen|exact Hby|exact Hne|exact Hlend
                         |exact Hsil|exact Hwr|reflexivity..]
            |split_and!; [exact Hne|exact Hlend|exact Hrd|exact Hex]
            |by rewrite elab_apply_rmw]. }
      * intros (l & m' & ors & fn' & d' & He &
                (Hcoh & [(Hlat & w & tvs & Hlen & Hby & -> & -> & -> & -> & ->)
                        |(Hlat & w & tvs & data & rl & m1 & m2 & rs1 &
                          Hlen & Hby & Hne & Hlend & Hsil & Hwr & -> & -> & ->
                          & -> & ->)]) & Hok & Hs); subst.
        { split; [exact Hcoh|]. left. split; [exact Hlat|].
          exists w, tvs. split_and!;
            [exact Hlen|exact Hby|exact Hok|reflexivity
            |by rewrite elab_apply_load]. }
        { destruct Hok as (_ & _ & Hrd & Hex).
          split; [exact Hcoh|]. right. split; [exact Hlat|].
          exists w, tvs, data, rl, m1, m2, rs1.
          split_and!; [exact Hlen|exact Hby|exact Hrd|exact Hex|exact Hne
                      |exact Hlend|exact Hsil|exact Hwr|reflexivity
                      |by rewrite elab_apply_rmw]. }
  - (* MemWrite *)
    destruct (dev_addr _).
    + (* MMIO WRITE — the fabric absorbs it (P1) *)
      split.
      * intros (d1 & Hwr & -> & ->). do 5 eexists. efac4;
          [reflexivity|split_and!; [exact Hwr|reflexivity..]|exact I
          |by rewrite elab_apply_dev].
      * intros (l & m' & ors & fn' & d' & He & (Hwr & -> & -> & -> & ->)
                & _ & Hs); subst.
        exists d'. split_and!; [exact Hwr|reflexivity|].
        by rewrite elab_apply_dev.
    + split.
      * intros (Hn & -> & ->). do 5 eexists. efac4;
          [reflexivity|split_and!; [exact Hn|reflexivity..]
          |by apply wbytes_ne|].
        rewrite elab_apply_store /= wbytes_length. reflexivity.
      * intros (l & m' & ors & fn' & d' & He & (Hn & -> & -> & -> & -> & ->)
                & _ & Hs); subst.
        split; [exact Hn|]. split; [reflexivity|].
        rewrite elab_apply_store /= wbytes_length. reflexivity.
  - (* Barrier — the inert [fence.i] label is deviation (D2) *)
    split.
    + intros (-> & ->). do 5 eexists. efac4;
        [reflexivity|split_and!; reflexivity| |by rewrite elab_apply_barrier].
      rewrite /elab_ok. by destruct b.
    + intros (l & m' & ors & fn' & d' & He & (-> & -> & -> & -> & ->) & _ & Hs);
        subst.
      split; [reflexivity|by rewrite elab_apply_barrier].
  - (* Choose *)
    split.
    + intros (ch & -> & ->). do 5 eexists. efac4;
        [reflexivity|by exists ch|exact I|by rewrite elab_apply_silent].
    + intros (l & m' & ors & fn' & d' & He & (ch & -> & -> & -> & -> & ->)
              & _ & Hs); subst.
      exists ch. split; [reflexivity|by rewrite elab_apply_silent].
Qed.

(** THE PLIC WIRE.  [pstep_plic] is available at ANY hart state, which is why
    the monad and the parked fence are universally quantified INSIDE. *)
Theorem eplic_step_factor σ σ' :
  eplic_step σ σ' <->
  exists (c : CPU) (l : wlabel) (ors : option regstate) (d' : dev_state),
    (forall (m : M unit) (fn : option (bool * bool * bool * bool)),
       pstep_plic c m (wgregs σ c) fn (wgdev σ) l m ors fn d') /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l WCplain ors d'.
Proof.
  rewrite /eplic_step /pstep_plic. split.
  - intros (c & ->).
    exists c, LSilent,
      (Some (register_set sig_seip
               (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c)))
               (wgregs σ c))), (wgdev σ).
    split_and!; [by intros m fn; split_and!|exact I|].
    by rewrite elab_apply_reg.
  - intros (c & l & ors & d' & Hp & _ & Hs).
    destruct (Hp (Interface.Ret tt) None) as (-> & _ & _ & -> & ->).
    exists c. by rewrite Hs elab_apply_reg.
Qed.

(** THE UART THREAD, as a silent fabric move of the disk agent: it moves
    neither the burst buffer nor the disk's own view. *)
Theorem euart_step_factor (pend : list wmsg) (dws : wstate) σ σ' :
  euart_step σ σ' <->
  exists (l : wlabel) (pend' : list wmsg) (d' : dev_state),
    pdisk_uart pend (wgdev σ) l pend' d' /\
    pend' = pend /\ edlab_ws σ dws l = dws /\
    edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  rewrite /euart_step /pdisk_uart. split.
  - intros (d1 & Hu & ->). exists LSilent, pend, d1.
    split_and!; try reflexivity; try exact I; try exact Hu;
      try (by rewrite edlab_apply_dev).
  - intros (l & pend' & d' & (-> & -> & Hu) & _ & _ & _ & Hs).
    exists d'. split; [exact Hu|]. by rewrite Hs edlab_apply_dev.
Qed.

(** THE DISK'S EMIT. *)
Theorem edisk_emit_factor gen (pend : list wmsg) (dws : wstate) σ e' σ' :
  edisk_emit gen pend dws σ e' σ' <->
  exists (l : wlabel) (pend' : list wmsg) (d' : dev_state),
    e' = EDisk gen pend' (edlab_ws σ dws l) /\
    pdisk_emit pend (wgdev σ) l pend' d' /\
    edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  rewrite /edisk_emit /pdisk_emit. split.
  - intros (msg & rest & -> & Hne & Htid & -> & ->).
    exists (LStore false (wm_pa msg) (wm_data msg)), rest, (wgdev σ).
    split_and!; [reflexivity| |exact Hne|].
    + exists msg, rest. by split_and!.
    + rewrite edlab_apply_store /=. do 2 f_equal.
      rewrite -Htid. by destruct msg.
  - intros (l & pend' & d' & He & (msg & rest & -> & -> & -> & Hne & Htid & ->)
            & _ & Hs).
    exists msg, rest. split_and!; [reflexivity|exact Hne|exact Htid| |].
    + by rewrite He.
    + rewrite Hs edlab_apply_store /=. do 2 f_equal.
      rewrite -Htid. by destruct msg.
Qed.

(** THE DISK'S DMA BURST, at the LANGUAGE's flat memory (P2). *)
Theorem edisk_burst_factor gen (pend : list wmsg) (dws : wstate) σ e' σ' :
  edisk_burst gen pend dws σ e' σ' <->
  exists (l : wlabel) (pend' : list wmsg) (d' : dev_state),
    e' = EDisk gen pend' (edlab_ws σ dws l) /\
    pdisk_burst (wflat (wgimg σ) (wglog σ)) pend (wgdev σ) l pend' d' /\
    edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  rewrite /edisk_burst /pdisk_burst. split.
  - intros (-> & d1 & w & Hst & -> & ->).
    exists LSilent, (wmsgs_of_map w), d1.
    split_and!; try reflexivity; try exact I; try (by exists w);
      try (by rewrite edlab_apply_dev).
  - intros (l & pend' & d' & He & (-> & w & Hst & -> & ->) & _ & Hs).
    split; [reflexivity|]. exists d', w. split_and!; [exact Hst| |].
    + by rewrite He.
    + by rewrite Hs edlab_apply_dev.
Qed.

(** ... and the two together, which is [WeakEvLang.edisk_step]. *)
Theorem edisk_step_factor gen (pend : list wmsg) (dws : wstate) σ e' σ' :
  edisk_step gen pend dws σ e' σ' <->
  exists (l : wlabel) (pend' : list wmsg) (d' : dev_state),
    e' = EDisk gen pend' (edlab_ws σ dws l) /\
    (pdisk_burst (wflat (wgimg σ) (wglog σ)) pend (wgdev σ) l pend' d'
     \/ pdisk_emit pend (wgdev σ) l pend' d') /\
    edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  rewrite /edisk_step. split.
  - intros [Hb|He].
    + apply edisk_burst_factor in Hb as (l & pend' & d' & ? & ? & ? & ?).
      exists l, pend', d'. split_and!; [done|by left|done|done].
    + apply edisk_emit_factor in He as (l & pend' & d' & ? & ? & ? & ?).
      exists l, pend', d'. split_and!; [done|by right|done|done].
  - intros (l & pend' & d' & He & [Hb|Hm] & Hok & Hs).
    + left. apply edisk_burst_factor. exists l, pend', d'. by split_and!.
    + right. apply edisk_emit_factor. exists l, pend', d'. by split_and!.
Qed.

(** THE ⇐ COROLLARY AT THE LAYER-1 SHAPE: every disk-agent event of the
    language is a [pstep_disk] (whose burst memory is existential).  The ⇒
    direction is the one that does NOT hold, by (P2). *)
Corollary edisk_step_pstep_disk gen (pend : list wmsg) (dws : wstate) σ e' σ' :
  edisk_step gen pend dws σ e' σ' ->
  exists (l : wlabel) (pend' : list wmsg) (d' : dev_state),
    e' = EDisk gen pend' (edlab_ws σ dws l) /\
    pstep_disk pend (wgdev σ) l pend' d' /\
    edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  intros H. apply edisk_step_factor in H as (l & pend' & d' & ? & Hd & ? & ?).
  exists l, pend', d'. split_and!; [done| |done|done].
  apply (pstep_disk_of_at (wflat (wgimg σ) (wglog σ))).
  destruct Hd as [Hb|Hm]; [by left|by right;left].
Qed.

Corollary euart_step_pstep_disk (pend : list wmsg) (dws : wstate) σ σ' :
  euart_step σ σ' ->
  exists (l : wlabel) (d' : dev_state),
    pstep_disk pend (wgdev σ) l pend d' /\
    edlab_ws σ dws l = dws /\ edlab_ok σ l /\
    σ' = edlab_apply σ l (pcls_ev (PDisk pend) l dws) d'.
Proof.
  intros H. apply (euart_step_factor pend dws) in H
    as (l & pend' & d' & Hu & -> & Hws & Hok & Hs).
  exists l, d'. split_and!; [|done|done|done].
  apply (pstep_disk_of_at ∅). by right; right.
Qed.

(** THE HART ARMS AT THE [pstep_hart] SHAPE: both the cycle event and the
    PLIC wire are one disjunct of the same program step. *)
Corollary ecycle_step_pstep_hart gen σ (c : CPU) m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' ->
  exists (l : wlabel) (m' : M unit) (ors : option regstate) fn' (d' : dev_state),
    e' = Sail gen c m' fn' /\
    pstep_hart c m (wgregs σ c) fn (wgdev σ) l m' ors fn' d' /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l
           (pcls_ev (PHart c m (wgregs σ c) fn) l (wgws σ c)) ors d'.
Proof.
  intros H. apply ecycle_step_factor in H
    as (l & m' & ors & fn' & d' & ? & ? & ? & ?).
  exists l, m', ors, fn', d'. split_and!; [done|by left|done|done].
Qed.

Corollary eplic_step_pstep_hart σ σ' :
  eplic_step σ σ' ->
  exists (c : CPU) (l : wlabel) (ors : option regstate) (d' : dev_state),
    (forall (m : M unit) fn,
       pstep_hart c m (wgregs σ c) fn (wgdev σ) l m ors fn d') /\
    elab_ok σ c l /\
    σ' = elab_apply σ c l WCplain ors d'.
Proof.
  intros H. apply eplic_step_factor in H as (c & l & ors & d' & Hp & ? & ?).
  exists c, l, ors, d'. split_and!; [|done|done]. intros m fn. right. apply Hp.
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

Lemma pnode_step_lat_free m rs d aq base tvs m' ors fn' d' :
  ~ pnode_step m rs d (LLoad aq true base tvs) m' ors fn' d'.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _)); try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (_ & [(_ & w & tvs0 & _ & _ & Hl & _)
                  |(_ & w & tvs0 & data & rl & m1 & m2 & rs1 &
                    _ & _ & _ & _ & _ & _ & Hl & _)]); by simplify_eq.
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & ? & _).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pstep_node_lat_free cpu m rs fn d aq base tvs m' ors fn' d' :
  ~ pstep_node cpu m rs fn d (LLoad aq true base tvs) m' ors fn' d'.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (? & _).
  - apply pnode_step_lat_free.
Qed.

Lemma pstep_hart_lat_free cpu m rs fn d aq base tvs m' ors fn' d' :
  ~ pstep_hart cpu m rs fn d (LLoad aq true base tvs) m' ors fn' d'.
Proof.
  intros [H|(H & _)]; [by eapply pstep_node_lat_free|done].
Qed.

Lemma pstep_disk_lat_free pend d aq lat base tvs pend' d' :
  ~ pstep_disk pend d (LLoad aq lat base tvs) pend' d'.
Proof.
  intros [(mem & _ & w & _ & _ & Hl)
         |[(msg & rest & _ & _ & _ & _ & _ & Hl)|(_ & Hl & _)]]; done.
Qed.

Theorem pstep_ev_lat_free p d aq base tvs p' d' :
  ~ pstep_ev p d (LLoad aq true base tvs) p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn|pend], p' as [cpu' m' rs' fn'|pend']; simpl;
    try (by intros []).
  - intros (_ & ors & _ & H). by eapply pstep_hart_lat_free.
  - apply pstep_disk_lat_free.
Qed.

Lemma pnode_step_ts_load m rs d aq base tvs tvs' m' ors fn' d' :
  pnode_step m rs d (LLoad aq false base tvs) m' ors fn' d' ->
  tvs'.*2 = tvs.*2 ->
  pnode_step m rs d (LLoad aq false base tvs') m' ors fn' d'.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _)); try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (Hcoh & [(Hlat & w & tvs0 & Hlen & Hby & Hl & Hrest)
                     |(_ & w & tvs0 & data & rl & m1 & m2 & rs1 &
                       _ & _ & _ & _ & _ & _ & Hl & _)]) Hts; [|by simplify_eq].
      simplify_eq/=.
      have Hlen' : length tvs' = length tvs0.
      { by rewrite -(length_fmap snd tvs') -(length_fmap snd tvs0) Hts. }
      split; [exact Hcoh|]. left. split; [exact Hlat|].
      exists w, tvs'. split_and!; [by rewrite Hlen'|by rewrite Hts| | | | |];
        by destruct Hrest as (-> & -> & -> & ->).
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & ? & _).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pnode_step_ts_rmw m rs d aq rl base tvs tvs' data m' ors fn' d' :
  pnode_step m rs d (LRmw aq rl base tvs data) m' ors fn' d' ->
  tvs'.*2 = tvs.*2 ->
  pnode_step m rs d (LRmw aq rl base tvs' data) m' ors fn' d'.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _)); try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (Hcoh & [(_ & w & tvs0 & _ & _ & Hl & _)
                     |(Hlat & w & tvs0 & data0 & rl0 & m1 & m2 & rs1 &
                       Hlen & Hby & Hne & Hlend & Hsil & Hwr & Hl & Hrest)])
              Hts; [by simplify_eq|].
      simplify_eq/=. destruct Hrest as (-> & -> & -> & ->).
      have Hlen' : length tvs' = length tvs0.
      { by rewrite -(length_fmap snd tvs') -(length_fmap snd tvs0) Hts. }
      split; [exact Hcoh|]. right. split; [exact Hlat|].
      exists w, tvs', data0, rl0, m1, m2, rs1.
      split_and!; [by rewrite Hlen'|by rewrite Hts|exact Hne
                  |by rewrite Hlen'|exact Hsil|exact Hwr|reflexivity..].
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & ? & _).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pstep_node_ts_load cpu m rs fn d aq base tvs tvs' m' ors fn' d' :
  pstep_node cpu m rs fn d (LLoad aq false base tvs) m' ors fn' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_node cpu m rs fn d (LLoad aq false base tvs') m' ors fn' d'.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (? & _).
  - apply pnode_step_ts_load.
Qed.

Lemma pstep_node_ts_rmw cpu m rs fn d aq rl base tvs tvs' data m' ors fn' d' :
  pstep_node cpu m rs fn d (LRmw aq rl base tvs data) m' ors fn' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_node cpu m rs fn d (LRmw aq rl base tvs' data) m' ors fn' d'.
Proof.
  rewrite /pstep_node. destruct fn as [[[[pr pw] sr] sw]|].
  - by intros (? & _).
  - apply pnode_step_ts_rmw.
Qed.

Theorem pstep_ev_ts_load p d aq base tvs tvs' p' d' :
  pstep_ev p d (LLoad aq false base tvs) p' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_ev p d (LLoad aq false base tvs') p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn|pend], p' as [cpu' m' rs' fn'|pend']; simpl;
    try (by intros ? ?).
  - intros (-> & ors & -> & [H|(H & _)]) Hts; [|done].
    split; [reflexivity|]. exists ors. split; [reflexivity|].
    left. by eapply pstep_node_ts_load.
  - intros H. by apply pstep_disk_lat_free in H.
Qed.

Theorem pstep_ev_ts_rmw p d aq rl base tvs tvs' data p' d' :
  pstep_ev p d (LRmw aq rl base tvs data) p' d' ->
  tvs'.*2 = tvs.*2 ->
  pstep_ev p d (LRmw aq rl base tvs' data) p' d'.
Proof.
  rewrite /pstep_ev.
  destruct p as [cpu m rs fn|pend], p' as [cpu' m' rs' fn'|pend']; simpl;
    try (by intros ? ?).
  - intros (-> & ors & -> & [H|(H & _)]) Hts; [|done].
    split; [reflexivity|]. exists ors. split; [reflexivity|].
    left. by eapply pstep_node_ts_rmw.
  - intros [(mem & _ & w & _ & _ & Hl)
           |[(msg & rest & _ & _ & _ & _ & _ & Hl)|(_ & Hl & _)]]; done.
Qed.
