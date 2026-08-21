(** * WeakEvPf.v — the definitional correspondence (spike S2, revised)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    "expression-resident monad" section); worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S2).

    ------------------------------------------------------------------------
    ** THE S2 ROUTE, AND WHY (unchanged by the revision — read it) **

    THE OBSTRUCTION, stated exactly.  [WeakPromise.wpcfg P] has EXACTLY TWO
    shared components — the era-initial image and the write log — plus a LIST
    of per-agent records.  A [WeakPromiseBridge.wp_pf_step] of agent [i]
    reads the two shared components and agent [i], and writes the log and
    agent [i].  There is no third shared component and no arm that writes
    another agent's slot.

    THE EVENT LANGUAGE HAS A THIRD SHARED COMPONENT: the device fabric
    [wgdev].  It is genuinely shared — hart A's MMIO write is visible to hart
    B's MMIO read, the PLIC wire hart A reads is driven by state the UART and
    the disk move, and the disk's DMA is a function of it.  A private per-agent
    copy (what [WeakSailLTS.psail]'s [sp_dev] does, and the only thing [wpcfg]
    can express) breaks BOTH containments; free device answers break ⇐; stuck
    device arms give a machine xv6 does not run on.  Since ⇐ is the direction
    the φ export needs, THE FABRIC MUST BE IN THE CONFIGURATION.

    LAYER-1 PARAMETRICITY DOES NOT SUPPLY IT.  [WeakRobustMain]'s [Section
    main] is parametric in the PROGRAM TYPE [P] and the program LTS, but NOT
    in the configuration functor: every statement is over the concrete
    three-field record [wpcfg P].

    THE ROUTE TAKEN: the FABRIC-SHARED promise-free machine, stated over the
    language's own configuration.  [epf_step i l ρ ρ'] (§3) LITERALLY CONTAINS
    the language's own step, decorated with the label its memory effect
    determines; ⇐ is therefore a PROJECTION ([epf_step_erased], §4) and ⇒ is a
    LABEL EXHIBITION ([ecycle_step_label], §5) — one case analysis, no
    invariant, no simulation relation.

    WHAT THE REVISION CHANGED, AND WHAT IT DID NOT.  The agents' PROGRAM state
    ([WeakPromise.pa_st]) now comes from the POOL rather than from σ, which is
    what the pf machine wanted all along: [wpcfg]'s agents carry [pa_st], so
    pool-of-expressions maps to agent-list FIELD FOR FIELD ([eags], §1), and
    the disk expression [EDisk gen dp dws] IS the pf [PDisk] agent.  What
    did NOT change is the finding: the fabric obstruction is a property of
    [wpcfg]'s SHAPE, not of the granularity or of where the program state
    lives.  Layer 1 still does not instantiate at [epf_step]; §6 states the
    projection that does exist and the sense in which it is the wrong way
    round.

    RECORDED DEVIATION (budget).  §5 delivers ⇒ at the STEP level (every
    language event carries a label) but not the run-level [erased_rtc_epf] of
    the pre-revision file: with the pool now moving, that direction needs a
    pool-shape INVERSION (an arbitrary erased step's thread must be located in
    [epool_list]) where ⇐ needs only pool CONSTRUCTION.  ⇐ is the direction
    S3 consumes; the ⇒ run-level theorem is not used anywhere.

    ------------------------------------------------------------------------
    ** THE LAYOUT **

    Pool positions ↔ agent indices, exactly [WeakCompose.xv6_ps]'s layout:
    hart [c] at index [fin_to_nat c] (so [0 .. NCPU-1]) and the disk at
    [WeakLang.n_disk = NCPU].  The UART thread has NO agent of its own: its
    arm touches neither the log nor any [wstate] nor any agent's program
    state, so it is a SILENT step of the fabric-owning agent (the disk).  The
    PLIC thread likewise has no agent: its arm is a cross-thread register
    write at the hart it targets, hence a silent step of THAT agent. *)
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
Require Import WeakPromise.
Require Import WeakPromiseBridge.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakGhost.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. [fin]-indexed lookup, once *)

Lemma fin_enum_lookup (n : nat) (i : fin n) :
  fin_enum n !! (fin_to_nat i) = Some i.
Proof.
  induction n as [|n IH]; [inversion i|].
  inv_fin i; [done|]. intros i. cbn [fin_enum fin_to_nat].
  rewrite lookup_cons list_lookup_fmap IH //.
Qed.

Lemma fin_enum_lookup_nat (n : nat) :
  forall (j : nat) (x : fin n), fin_enum n !! j = Some x -> @fin_to_nat n x = j.
Proof.
  induction n as [|n IH]; intros j x Hj; [by rewrite lookup_nil in Hj|].
  destruct j as [|j]; cbn [fin_enum] in Hj.
  - rewrite lookup_cons in Hj. by simplify_eq.
  - rewrite lookup_cons list_lookup_fmap in Hj.
    destruct (fin_enum n !! j) as [y|] eqn:Hy; simplify_eq/=.
    cbn [fin_to_nat]. by rewrite (IH j y Hy).
Qed.

Lemma fin_enum_length (n : nat) : length (fin_enum n) = n.
Proof. induction n as [|n IH]; [done|]. cbn. by rewrite length_fmap IH. Qed.

Lemma enum_CPU_lookup (c : CPU) : enum CPU !! (fin_to_nat c) = Some c.
Proof. apply fin_enum_lookup. Qed.

Lemma enum_CPU_length : length (enum CPU) = NCPU.
Proof. apply fin_enum_length. Qed.

(* ====================================================================== *)
(** ** 1. The pool, the program type and the agent layout

    The canonical pool of one era, as a RECORD: the per-hart expressions and
    the disk's two operation fields.  [epool_list] is [WeakEvLang.epower_fork]
    generalised to an arbitrary reachable pool, and every reachable pool of
    the era has this shape (no arm forks and every arm returns an expression
    of its own kind). *)

(** A hart's whole thread state: [None] at the boundary, [Some (m, fn)] mid
    instruction.  Keeping it as DATA (rather than as an [eexpr]) is what makes
    every reachable pool well formed by construction — a pool field cannot
    accidentally hold [EPower]. *)
Definition ehst := option (M unit * option (bool * bool * bool * bool)).

Definition ehexp (gen : nat) (c : CPU) (h : ehst) : eexpr :=
  match h with
  | None => ELoop gen c
  | Some (m, fn) => ECycle gen c m fn
  end.

Record epool := EPool {
  ep_gen  : nat;
  ep_h    : CPU -> ehst;
  ep_dp   : option (DM dres);   (* M5: the RESIDUAL DEVICE PROGRAM *)
  ep_dws  : wstate;
}.

Definition ehexpr (P : epool) (c : CPU) : eexpr := ehexp (ep_gen P) c (ep_h P c).

Definition epool_list (P : epool) : list eexpr :=
  (ehexpr P <$> enum CPU)
  ++ [EUart (ep_gen P); EDisk (ep_gen P) (ep_dp P) (ep_dws P);
      EPlic (ep_gen P)].

Definition ep_hset (P : epool) (c : CPU) (h : ehst) : epool :=
  EPool (ep_gen P) (fun c' => if decide (c' = c) then h else ep_h P c')
        (ep_dp P) (ep_dws P).

Definition ep_dset (P : epool) (dp : option (DM dres)) (dws : wstate)
    : epool := EPool (ep_gen P) (ep_h P) dp dws.

(** The initial pool of a fresh era IS [WeakEvLang.epower_fork]. *)
Definition ep_init (gen : nat) : epool :=
  EPool gen (fun _ => None) None ws_init.

Lemma epool_list_init gen : epool_list (ep_init gen) = epower_fork gen.
Proof. reflexivity. Qed.

(** A hart's PROGRAM state is exactly what its expression holds: THE CPU (the
    PLIC wire's hart index is program-visible data), the residual monad and
    the parked fence.  There is no [option (M unit)]: since G5c1 the BOUNDARY
    IS [Interface.Ret tt] ([WeakEvLang.ELoop]), so [ehst]'s [None] maps to
    [Interface.Ret tt] and the hart's program state is total.  There is no
    [sp_dev] and no [sp_irq] — that is the whole point. *)
Inductive pexv6 :=
| PHart (cpu : CPU) (m : M unit) (rs : regstate)
        (fn : option (bool * bool * bool * bool))
        (* D3: THE ANNOUNCED INSTRUCTION BITS.  Program state, not memory
           state: [pstep_ev] decodes it ([WeakDeps.deps_of_bits]) to compute
           the labels' operand lists.  It comes from σ's [wgib] exactly as
           the register file comes from σ's [wgregs]. *)
        (ib : oib32)
| PDisk (dp : option (DM dres)).

Definition ehart_m (h : ehst) : M unit :=
  match h with Some (m, _) => m | None => Interface.Ret tt end.
Definition ehart_fn (h : ehst) : option (bool * bool * bool * bool) :=
  match h with Some (_, fn) => fn | None => None end.

(** ... and the expression IS that program state, constructor for
    constructor: [ehexp] is [Sail] of the two projections. *)
Lemma ehexp_sail gen c h : ehexp gen c h = Sail gen c (ehart_m h) (ehart_fn h).
Proof. by destruct h as [[m fn]|]. Qed.

Definition ehart_ag (P : epool) (σ : wgstate) (c : CPU) : wpagent pexv6 :=
  WPAgent (PHart c (ehart_m (ep_h P c)) (wgregs σ c) (ehart_fn (ep_h P c))
             (wgib σ c))
          (wgws σ c) ∅.

Definition edisk_ag (P : epool) : wpagent pexv6 :=
  WPAgent (PDisk (ep_dp P)) (ep_dws P) ∅.

Definition eags (P : epool) (σ : wgstate) : list (wpagent pexv6) :=
  (ehart_ag P σ <$> enum CPU) ++ [edisk_ag P].

(** THE PROJECTION to a [WeakPromise] configuration — the fabric is dropped,
    which is exactly the information the pf machine cannot hold (§6). *)
(** THE PROJECTION to a [WeakPromise] configuration.  Since the G-series
    generalization the fabric is a configuration component, so it is no
    longer forgotten: [D := DevModel.dev_state] and [pc_dev] IS the
    language's own [wgdev]. *)
Definition ecfg_of (P : epool) (σ : wgstate) : wpcfg pexv6 dev_state :=
  WPCfg (img_z (wgimg σ)) (wglog σ) (wgdev σ) (eags P σ).

Lemma eags_hart P σ (c : CPU) : eags P σ !! (fin_to_nat c) = Some (ehart_ag P σ c).
Proof.
  rewrite /eags lookup_app_l.
  - rewrite list_lookup_fmap enum_CPU_lookup //.
  - rewrite length_fmap enum_CPU_length. apply fin_to_nat_lt.
Qed.

Lemma eags_disk P σ : eags P σ !! n_disk = Some (edisk_ag P).
Proof.
  rewrite /eags /n_disk lookup_app_r.
  2:{ rewrite length_fmap enum_CPU_length. done. }
  rewrite length_fmap enum_CPU_length Nat.sub_diag //.
Qed.

Lemma eags_length P σ : length (eags P σ) = S NCPU.
Proof.
  rewrite /eags length_app length_fmap enum_CPU_length. cbn [length]. lia.
Qed.

(* ====================================================================== *)
(** ** 2. The labels: reading a [wlabel] off a transition

    [elabel_ok σ c l σ'] says "the memory effect of hart [c]'s transition IS
    the label [l]", spelled with EXACTLY the side conditions and view updates
    of [WeakPromiseBridge.wp_pf_step]'s five arms.  The FRAME is not restated:
    it is a theorem about the language's own step
    ([WeakEvLang.ecycle_step_img] / [ecycle_step_ws_other] / …), which is what
    "the machine is the language decorated with a label" means. *)

Definition elabel_ok (σ : wgstate) (c : CPU) (l : wlabel) (σ' : wgstate)
    : Prop :=
  match l with
  | LSilent => wglog σ' = wglog σ /\ wgws σ' c = wgws σ c
  (* D2: the event language emits EMPTY operand lists (D3 supplies
     [deps_of_bits]), so every memory arm PINS them to [[]] and the σ-effect
     stays the dependency-free step function verbatim.  [WeakEvInst] then
     converts to the machine's [_d] form by [srcs_view_nil] +
     [load_post_run_d_0] / [store_post_run_d_0]. *)
  | LLoad aq lat base tvs asrc =>
      lat = false /\ asrc = [] /\
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq lat base tvs /\
      wglog σ' = wglog σ /\
      wgws σ' c = load_post_run (wgws σ c) aq base tvs.*1
  | LStore rl base data asrc vsrc =>
      (exists k, wglog σ' = wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]) /\
      data <> [] /\
      wgws σ' c = store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
                    (srcs_view (wgws σ c) vsrc) base (length data)
                    (S (length (wglog σ)))
  | LRmw aq rl base tvs data asrc vsrc =>
      data <> [] /\ length tvs = length data /\
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs /\
      excl_ok (wglog σ) (fin_to_nat c) base tvs (S (length (wglog σ))) /\
      (exists k, wglog σ' = wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]) /\
      wgws σ' c = store_post_run_d
                    (load_post_run_d (wgws σ c) aq (srcs_view (wgws σ c) asrc)
                       base tvs.*1)
                    rl (srcs_view (wgws σ c) asrc) (srcs_view (wgws σ c) vsrc)
                    base (length data) (S (length (wglog σ)))
  | LFence pr pw sr sw =>
      wglog σ' = wglog σ /\ wgws σ' c = fence_post (wgws σ c) pr pw sr sw
  (* THE FABRIC MARKER (M5): [LSilent]'s twin.  A hart's MMIO access and
     the PLIC wire are silent-effect steps that TOUCH THE FABRIC, and
     [pdev] can only see that in the label — so they will be relabelled
     [LDev].  The memory effect is the silent one, verbatim. *)
  | LDev => wglog σ' = wglog σ /\ wgws σ' c = wgws σ c
  (* D3-2: the three dependency-only labels are REAL now — [PARM]'s
     [step_assign], [step_if] and the instruction start.  Each moves the
     hart's view and nothing else, so each is [LSilent]'s clause with the
     view equation replaced. *)
  | LRegW rd srcs =>
      wglog σ' = wglog σ /\
      wgws σ' c = regw_post (wgws σ c) rd (srcs_view (wgws σ c) srcs)
  | LCtrl srcs =>
      wglog σ' = wglog σ /\
      wgws σ' c = ctrl_post (wgws σ c) (srcs_view (wgws σ c) srcs)
  | LInstr => wglog σ' = wglog σ /\ wgws σ' c = instr_post (wgws σ c)
  (* THE RMW SPLIT (S3): the two halves.  [LExLoad] is [LLoad]'s clause at
     [lat := false], with the read admissible at the PLAIN floor (D-2r —
     the address view no longer floors an exclusive read on either the
     fused or the split path) and the RESERVATION written into the
     post-state by [exload_post_run_d], which still CONSUMES the address
     view (in [w_vcap]).  [LExStore] is [LStore]'s clause plus §4's window:
     a matching reservation of the right width, still clean at the fresh
     top. *)
  | LExLoad aq base tvs asrc =>
      read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs /\
      wglog σ' = wglog σ /\
      wgws σ' c = exload_post_run_d (wgws σ c) aq
                    (srcs_view (wgws σ c) asrc) base tvs.*1
  | LExStore rl base data asrc vsrc =>
      (exists k, wglog σ' = wglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]) /\
      data <> [] /\
      exwin_ok (wglog σ) (fin_to_nat c) (wgws σ c) base (length data)
        (S (length (wglog σ))) /\
      wgws σ' c = store_post_run_d (wgws σ c) rl (srcs_view (wgws σ c) asrc)
                    (srcs_view (wgws σ c) vsrc) base (length data)
                    (S (length (wglog σ)))
  end.

(** The disk agent's version.  Since M5 the disk is an ORDINARY weak-memory
    agent, so it uses the SAME four memory labels a hart uses (spelled at the
    disk's own [dws], which lives in the expression rather than in σ) plus
    the fabric marker; only [LRmw] never arises — the device has no atomic
    read-modify-write. *)
Definition edlabel_ok (P : epool) (σ : wgstate) (l : wlabel)
    (dws' : wstate) (σ' : wgstate) : Prop :=
  match l with
  | LSilent => wglog σ' = wglog σ /\ dws' = ep_dws P
  | LLoad aq lat base tvs asrc =>
      lat = false /\ asrc = [] /\
      read_ok (img_z (wgimg σ)) (wglog σ) (ep_dws P) aq lat base tvs /\
      wglog σ' = wglog σ /\
      dws' = load_post_run (ep_dws P) aq base tvs.*1
  | LStore rl base data asrc vsrc =>
      asrc = [] /\ vsrc = [] /\
      (exists k, wglog σ' = wglog σ ++ [WMsg base data (Some n_disk) k]) /\
      data <> [] /\
      dws' = store_post_run (ep_dws P) rl base (length data)
               (S (length (wglog σ)))
  | LFence pr pw sr sw =>
      wglog σ' = wglog σ /\ dws' = fence_post (ep_dws P) pr pw sr sw
  (* the fabric marker, [LSilent]'s twin: the disk's own fabric reads and
     writes are silent-effect steps that touch the fabric *)
  | LDev => wglog σ' = wglog σ /\ dws' = ep_dws P
  | LRmw _ _ _ _ _ _ _ => False
  | LRegW _ _ | LCtrl _ | LInstr => False
  (* THE RMW SPLIT (S3): the disk has no exclusives — the [LRmw] precedent
     two lines up, and [WeakEvInst.pstep_disk_no_ex] is the proof. *)
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => False
  end.

Lemma wbytes_ne (n : N) {w : N} (v : bv w) : n <> 0%N -> wbytes n v <> [].
Proof.
  intros Hn Heq. have Hl := wbytes_length n v. rewrite Heq /= in Hl.
  destruct n as [|pn]; [by apply Hn|]. cbn in Hl.
  by pose proof (Pos2Nat.is_pos pn); lia.
Qed.

(* ====================================================================== *)
(** ** 3. THE FABRIC-SHARED PROMISE-FREE MACHINE

    [wp_pf_step]'s arms over the language's own configuration.  Each arm
    LITERALLY CONTAINS the language's step — so the machine is not a second
    definition of anything: it is the language, with the pf bookkeeping made
    visible. *)

Inductive epf_step :
    nat -> wlabel -> (epool * wgstate) -> (epool * wgstate) -> Prop :=
| EPFBoundary (c : CPU) (P : epool) (σ : wgstate) (tick : bool) :
    ethread_live σ (ep_gen P) -> ep_h P c = None ->
    (* D3: the RESTART clears the hart's announced bits, and (W2b condition
       1) IT IS THE RESET POINT: the boundary emits [LInstr] and applies
       [instr_post], so the fetch that follows sees an empty translation
       bank. *)
    epf_step (fin_to_nat c) LInstr (P, σ)
      (ep_hset P c (Some (riscv_step tick, None)),
       ewg_ibws σ c None (instr_post (wgws σ c)))
| EPFCycle (c : CPU) (l : wlabel) (P : epool) (σ : wgstate)
           (m : M unit) (fn : option (bool * bool * bool * bool))
           (h' : ehst) (σ' : wgstate) :
    ethread_live σ (ep_gen P) -> ep_h P c = Some (m, fn) ->
    ecycle_step (ep_gen P) σ c m fn (ehexp (ep_gen P) c h') σ' ->
    elabel_ok σ c l σ' ->
    epf_step (fin_to_nat c) l (P, σ) (ep_hset P c h', σ')
| EPFDisk (l : wlabel) (P : epool) (σ : wgstate)
          (dp' : option (DM dres)) (dws' : wstate) (σ' : wgstate) :
    ethread_live σ (ep_gen P) ->
    edisk_step (ep_gen P) (ep_dp P) (ep_dws P) σ
      (EDisk (ep_gen P) dp' dws') σ' ->
    edlabel_ok P σ l dws' σ' ->
    epf_step n_disk l (P, σ) (ep_dset P dp' dws', σ')
(* THE UART THREAD and THE PLIC WIRE are FABRIC-TOUCHING silent steps, so
   since M5 they carry the marker label [LDev] (whose memory effect is
   [LSilent]'s, verbatim). *)
| EPFUart (P : epool) (σ σ' : wgstate) :
    ethread_live σ (ep_gen P) -> euart_step σ σ' ->
    epf_step n_disk LDev (P, σ) (P, σ')
| EPFPlic (c : CPU) (P : epool) (σ : wgstate) :
    ethread_live σ (ep_gen P) ->
    epf_step (fin_to_nat c) LDev (P, σ)
      (P, ewg_reg σ c
            (register_set sig_seip
               (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c)))
               (wgregs σ c))).

Definition epf_run (ρ ρ' : epool * wgstate) : Prop := exists i l, epf_step i l ρ ρ'.

(** THE ERA IS FIXED across the pf machine — as it is across Layer 1, which
    is stated per-era.  (The power thread is deliberately NOT a pf arm.) *)
Lemma epf_step_era i l ρ ρ' :
  epf_step i l ρ ρ' ->
  wgpow ρ'.2 = wgpow ρ.2 /\ wggen ρ'.2 = wggen ρ.2 /\ ep_gen ρ'.1 = ep_gen ρ.1.
Proof.
  destruct 1 as [c P σ tick Hlive Hh
                |c l0 P σ m0 fn0 h' σ' Hlive Hh Hcy Hl
                |l0 P σ pd dw σ' Hlive Hstep Hl
                |P σ σ' Hlive Hu
                |c P σ Hlive]; simpl; try by split_and!.
  - destruct (ecycle_step_era _ _ _ _ _ _ _ Hcy). by split_and!.
  - destruct Hstep as [(_ & _ & ->)
                      |[(pa & n & aq & kk & tvs & _ & _ & _ & _ & ->)
                      |[(pa & bs & kk & _ & _ & _ & ->)
                      |[(kk & _ & _ & ->)
                      |[(dl & _ & _ & ->)
                      |[(pg & _ & _ & _ & ->)
                      |[(_ & _ & ->)
                      |(p' & _ & _ & _ & ->)]]]]]]]; by split_and!.
  - destruct Hu as (d' & _ & ->). by split_and!.
Qed.

Lemma epf_step_live gen i l ρ ρ' :
  ethread_live ρ.2 gen -> ep_gen ρ.1 = gen -> epf_step i l ρ ρ' ->
  ethread_live ρ'.2 gen /\ ep_gen ρ'.1 = gen.
Proof.
  intros [Hp Hg] HP Hs. destruct (epf_step_era _ _ _ _ Hs) as (He1 & He2 & He3).
  rewrite /ethread_live He1 He2 He3 HP. by split_and!.
Qed.

Lemma epf_run_live gen ρ ρ' :
  ethread_live ρ.2 gen -> ep_gen ρ.1 = gen -> rtc epf_run ρ ρ' ->
  ethread_live ρ'.2 gen /\ ep_gen ρ'.1 = gen.
Proof.
  intros Hl HP Hr. revert Hl HP.
  induction Hr as [ρ|ρ ρ2 ρ3 (i & l & Hs) _ IH]; intros Hl HP; [by split|].
  apply IH; by destruct (epf_step_live gen i l ρ ρ2 Hl HP Hs).
Qed.

(* ====================================================================== *)
(** ** 4. ⇐ : EVERY PF STEP IS AN ERASED STEP

    The direction the φ export consumes (S3).  It is a PROJECTION: an
    [epf_step] literally contains the language's own step, so the only work is
    naming the pool position it belongs to and re-assembling the pool. *)

(** A thread at a known position steps the whole pool, by [insert]. *)
Lemma erased_step_of_lookup (t : list eexpr) (i : nat) (e e' : eexpr)
    (σ σ' : wgstate) :
  t !! i = Some e -> eprim_step e σ [] e' σ' [] ->
  @erased_step weak_ev_lang (t, σ) (<[i := e']> t, σ').
Proof.
  intros Hi Hstep. exists [].
  rewrite insert_take_drop; [|by eapply lookup_lt_Some].
  eapply (@step_atomic weak_ev_lang _ _ _ e σ e' σ' [] (take i t) (drop (S i) t));
    [by rewrite (take_drop_middle t i e Hi)| |exact Hstep].
  by rewrite app_nil_r.
Qed.

Lemma fmap_enum_hset (gen : nat) (f : CPU -> ehst) (c : CPU) (h : ehst) :
  ((fun c' => ehexp gen c' (if decide (c' = c) then h else f c')) <$> enum CPU)
  = <[fin_to_nat c := ehexp gen c h]>
      ((fun c' => ehexp gen c' (f c')) <$> enum CPU).
Proof.
  apply list_eq. intros j.
  rewrite list_lookup_fmap.
  destruct (decide (j = fin_to_nat c)) as [->|Hne].
  - rewrite list_lookup_insert.
    2:{ rewrite length_fmap enum_CPU_length. apply fin_to_nat_lt. }
    rewrite enum_CPU_lookup /=. by destruct (decide (c = c)).
  - rewrite list_lookup_insert_ne; [|done].
    rewrite list_lookup_fmap.
    destruct (enum CPU !! j) as [c0|] eqn:Hc0; [|reflexivity].
    simpl. destruct (decide (c0 = c)) as [->|]; [|reflexivity].
    exfalso. apply Hne. symmetry. exact (fin_enum_lookup_nat NCPU j c Hc0).
Qed.

Lemma epool_list_hart_lookup P (c : CPU) :
  epool_list P !! (fin_to_nat c) = Some (ehexpr P c).
Proof.
  rewrite /epool_list lookup_app_l.
  - rewrite list_lookup_fmap enum_CPU_lookup //.
  - rewrite length_fmap enum_CPU_length. apply fin_to_nat_lt.
Qed.

Lemma epool_list_hset P (c : CPU) (h : ehst) :
  <[fin_to_nat c := ehexp (ep_gen P) c h]> (epool_list P)
  = epool_list (ep_hset P c h).
Proof.
  rewrite /epool_list /ehexpr.
  rewrite insert_app_l.
  2:{ rewrite length_fmap enum_CPU_length. apply fin_to_nat_lt. }
  rewrite /ep_hset. cbn [ep_gen ep_h ep_dp ep_dws].
  by rewrite (fmap_enum_hset (ep_gen P) (ep_h P) c h).
Qed.

Lemma epool_list_disk_lookup P :
  epool_list P !! (S NCPU) = Some (EDisk (ep_gen P) (ep_dp P) (ep_dws P)).
Proof.
  rewrite /epool_list lookup_app_r; rewrite length_fmap enum_CPU_length; [|lia].
  by replace (S NCPU - NCPU)%nat with 1%nat by lia.
Qed.

Lemma epool_list_dset P dp dws :
  <[S NCPU := EDisk (ep_gen P) dp dws]> (epool_list P)
  = epool_list (ep_dset P dp dws).
Proof.
  rewrite /epool_list /ehexpr.
  rewrite insert_app_r_alt; rewrite length_fmap enum_CPU_length; [|lia].
  rewrite /ep_dset. cbn [ep_gen ep_h ep_dp ep_dws].
  by replace (S NCPU - NCPU)%nat with 1%nat by lia.
Qed.

Lemma epool_list_uart_lookup P : epool_list P !! NCPU = Some (EUart (ep_gen P)).
Proof.
  rewrite /epool_list lookup_app_r; rewrite length_fmap enum_CPU_length; [|lia].
  by rewrite Nat.sub_diag.
Qed.

Lemma epool_list_id (t : list eexpr) (i : nat) (e : eexpr) :
  t !! i = Some e -> <[i := e]> t = t.
Proof. intros Hi. by apply list_insert_id. Qed.

Theorem epf_step_erased i l ρ ρ' :
  epf_step i l ρ ρ' ->
  @erased_step weak_ev_lang (epool_list ρ.1, ρ.2) (epool_list ρ'.1, ρ'.2).
Proof.
  destruct 1 as [c P σ tick Hlive Hh
                |c l0 P σ m0 fn0 h' σ' Hlive Hh Hcy Hl
                |l0 P σ pd dw σ' Hlive Hstep Hl
                |P σ σ' Hlive Hu
                |c P σ Hlive]; simpl.
  - (* the boundary: fetch a fresh instruction *)
    rewrite -(epool_list_hset P c (Some (riscv_step tick, None))).
    eapply erased_step_of_lookup; [apply epool_list_hart_lookup|].
    rewrite /ehexpr Hh /=. by apply eprim_step_loop_live.
  - (* one event of the cycle *)
    rewrite -(epool_list_hset P c h').
    eapply erased_step_of_lookup; [apply epool_list_hart_lookup|].
    rewrite /ehexpr Hh /=.
    left. exists (ep_gen P), c, m0, fn0.
    split_and!; try reflexivity. left. by split.
  - rewrite -(epool_list_dset P pd dw).
    eapply erased_step_of_lookup; [apply epool_list_disk_lookup|].
    right; right; left. exists (ep_gen P), (ep_dp P), (ep_dws P).
    split_and!; try reflexivity. left. by split.
  - rewrite -(epool_list_id (epool_list P) NCPU (EUart (ep_gen P)));
      [|apply epool_list_uart_lookup].
    eapply erased_step_of_lookup; [apply epool_list_uart_lookup|].
    right; left. exists (ep_gen P). split_and!; try reflexivity.
    left. by split.
  - rewrite -(epool_list_id (epool_list P) (S (S NCPU)) (EPlic (ep_gen P))).
    2:{ rewrite /epool_list lookup_app_r;
          rewrite length_fmap enum_CPU_length; [|lia].
        by replace (S (S NCPU) - NCPU)%nat with 2%nat by lia. }
    eapply erased_step_of_lookup.
    { rewrite /epool_list lookup_app_r;
        rewrite length_fmap enum_CPU_length; [|lia].
      by replace (S (S NCPU) - NCPU)%nat with 2%nat by lia. }
    by apply eprim_step_plic_wire.
Qed.

Theorem epf_rtc_erased ρ ρ' :
  rtc epf_run ρ ρ' ->
  rtc (@erased_step weak_ev_lang) (epool_list ρ.1, ρ.2) (epool_list ρ'.1, ρ'.2).
Proof.
  induction 1 as [ρ|ρ ρ2 ρ3 (i & l & Hs) _ IH]; [apply rtc_refl|].
  eapply rtc_l; [by apply (epf_step_erased i l ρ ρ2)|exact IH].
Qed.

(* ====================================================================== *)
(** ** 5. ⇒ : EVERY LANGUAGE EVENT CARRIES A LABEL

    The label exhibition, at the step level.  ONE case analysis over the
    outcome the residual monad sits at, and in each branch the label is READ
    OFF the σ-update. *)

Lemma ecycle_step_label gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> exists l, elabel_ok σ c l σ'.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). exists (LFence pr pw sr sw).
    split; [reflexivity|apply gws_insert_eq]. }
  destruct m as [y|T oc k].
  { (* THE BOUNDARY — [LInstr], the reset point (W2b condition 1) *)
    intros (? & _ & ->). exists LInstr.
    split; [reflexivity|apply gws_insert_eq]. }
  destruct oc; simpl;
    try (intros (_ & ->); exists LSilent; by split);
    try (by intros []).
  - (* D3-2: THE REGISTER WRITE.  Its label is its classification's
       ([LSilent] / [LRegW] / [LCtrl]) and its σ-effect is that label's,
       by construction — one [destruct] over the three kinds. *)
    intros (_ & ->). eexists (erw_label (erw_of (edeps σ c) reg)).
    destruct (erw_of (edeps σ c) reg); simpl;
      (split; [reflexivity|]);
      solve [reflexivity|apply gws_insert_eq].
  - (* MemRead *)
    destruct (dev_addr _).
    + intros (w & d' & _ & _ & ->). exists LDev. by split.
    + intros (_ & [(_ & w & tvs & _ & _ & Hrd & _ & ->)
                  |(_ & w & tvs & _ & _ & Hrd & _ & ->)]).
      * eexists (LLoad _ false _ tvs []).
        split_and!;
          [reflexivity|reflexivity|exact Hrd|reflexivity|apply gws_insert_eq].
      * (* THE EXCLUSIVE READ (RMW split S3) *)
        eexists (LExLoad _ _ tvs _).
        split_and!; [exact Hrd|reflexivity|apply gws_insert_eq].
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros (d' & _ & _ & ->). exists LDev. by split.
    + intros (Hn & [(_ & _ & ->)|(_ & [(Hex & _ & ->)|(_ & ->)])]).
      * eexists (LStore _ _ _ _ _). split_and!.
        { eexists. reflexivity. }
        { by apply wbytes_ne. }
        rewrite wbytes_length. apply gws_insert_eq.
      * (* THE CONDITIONAL WRITE (RMW split S3) *)
        eexists (LExStore _ _ _ _ _). split_and!.
        { eexists. reflexivity. }
        { by apply wbytes_ne. }
        { rewrite wbytes_length. exact Hex. }
        rewrite wbytes_length. apply gws_insert_eq.
      * (* THE RETRY SELF-LOOP (design §5): a silent, σ-preserving step *)
        exists LSilent. by split.
  - (* D3-2: THE ANNOUNCE — [LInstr], the instruction start *)
    intros (_ & ->). exists LInstr.
    split; [reflexivity|apply gws_insert_eq].
  - (* Barrier *)
    intros (_ & ->). destruct b;
      [ eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | exists LSilent ];
      (split; [reflexivity|apply gws_insert_eq]).
  - (* Choose *) intros (ch & _ & ->). exists LSilent. by split.
Qed.

(** THE DISK'S LABEL, one per arm of the M5 device program: the three
    fabric arms carry the marker [LDev], the three memory nodes carry
    exactly a hart's labels, and the two program-internal arms are
    [LSilent]. *)
Lemma edisk_step_label P σ e' σ' :
  edisk_step (ep_gen P) (ep_dp P) (ep_dws P) σ e' σ' ->
  exists l dp' dws', e' = EDisk (ep_gen P) dp' dws' /\
    edlabel_ok P σ l dws' σ'.
Proof.
  intros [(_ & -> & ->)
         |[(pa & n & aq & kk & tvs & _ & _ & Hrd & -> & ->)
         |[(pa & bs & kk & _ & Hne & -> & ->)
         |[(kk & _ & -> & ->)
         |[(dl & _ & -> & ->)
         |[(pg & _ & _ & -> & ->)
         |[(_ & -> & ->)
         |(p' & _ & _ & -> & ->)]]]]]]].
  - exists LDev. do 2 eexists. split; [reflexivity|by split].
  - eexists (LLoad _ false _ tvs []). do 2 eexists. split; [reflexivity|].
    by split_and!.
  - eexists (LStore false _ bs [] []). do 2 eexists. split; [reflexivity|].
    split_and!; [reflexivity|reflexivity|by eexists|exact Hne|reflexivity].
  - eexists (LFence _ _ _ _). do 2 eexists. split; [reflexivity|by split].
  - exists LDev. do 2 eexists. split; [reflexivity|by split].
  - exists LSilent. do 2 eexists. split; [reflexivity|by split].
  - exists LSilent. do 2 eexists. split; [reflexivity|by split].
  - exists LDev. do 2 eexists. split; [reflexivity|by split].
Qed.

(* ====================================================================== *)
(** ** 6. THE PROJECTION TO [wpcfg] — AND WHAT THE G-SERIES CHANGED

    THE OBSTRUCTION IN THE HEADER IS GONE AT LAYER 1.  [WeakPromise.wpcfg]
    now has THREE shared components: the image, the log, and the DEVICE
    FABRIC [pc_dev : D], with [D] an abstract type parameter and the program
    step generalized to [P → D → wlabel → P → D → Prop].  So [ecfg_of] no
    longer forgets anything: it instantiates [D := DevModel.dev_state] and
    carries [wgdev] itself.

    WHAT G5 STILL OWES (the instance, not the machine).  [epf_step]'s five
    arms are the five [WeakPromiseBridge.wp_pf_step] arms at
    [P := pexv6], [D := dev_state], with the marker
    [pdev p l p' := true] exactly on the DEVICE-ACCESS steps — the
    [dev_addr]-hit branches of [EPFCycle], and [EPFDisk]/[EPFUart]/[EPFPlic]
    — every one of which carries [LSilent].  Every other arm is
    fabric-blind and fabric-preserving, so [WeakPromiseFact.pdev_ok] holds
    and [WeakRobustTrace]'s witness of an [epf_run] IS its device-access
    order.  Exhibiting that instance (and reading the decomposition off
    [WeakRobustTrace.state_ptraces]) is G5's job; nothing in this file needs
    to change for it.

    The two facts a consumer of Layer 1's vocabulary needs are below: the
    observation floor of a hart agent IS that hart's coherence floor, and
    the disk sits at [n_disk]. *)

Lemma obs_flr_hart P σ (c : CPU) (a : Z) :
  obs_flr (ecfg_of P σ) (fin_to_nat c) a = coh (wgws σ c) a.
Proof. rewrite /obs_flr /ecfg_of /= eags_hart //. Qed.

Lemma ecfg_of_log P σ : pc_log (ecfg_of P σ) = wglog σ.
Proof. reflexivity. Qed.

(** THE φ TRANSPORT: [WeakGhost.no_violation] over σ REFUTES Layer 1's
    [WeakRobust.violation_hart] at the projected configuration, at the hart
    bound [n_disk = NCPU] — the two predicates are the same statement, term
    for term.  This is the whole of what S3's success criterion needs from the
    layout, and note what it does NOT need: the agents' PROGRAM state, which
    is why moving it into the pool costs the export nothing. *)
Theorem no_violation_violation_hart P σ :
  no_violation (wglog σ) (wgws σ) ->
  ~ violation_hart cls_of pub_of n_disk (ecfg_of P σ).
Proof.
  intros Hnv (p & m & i & j & a & Hp & Ht & Hth & Hcls & Hpub & Hne & Hjh &
              Hb & Hfl).
  rewrite ecfg_of_log in Hp.
  destruct Hth as (i' & Hti & Hilt).
  assert (i' = i) as -> by (rewrite Ht in Hti; by simplify_eq).
  destruct Hjh as (j' & Hj & Hjlt).
  assert (j' = j) as -> by (by simplify_eq).
  have Hcn : fin_to_nat (nat_to_fin Hilt) = i by apply fin_to_nat_to_fin.
  have Hcn' : fin_to_nat (nat_to_fin Hjlt) = j by apply fin_to_nat_to_fin.
  have Hak : wm_ak m = WCplain.
  { rewrite /cls_of in Hcls. by destruct (wm_ak m). }
  have Hnpub : ~ wpublished (wglog σ) (wm_tid m) p.
  { intros Hw. apply Hpub. rewrite /pub_of. exists p, m.
    rewrite ecfg_of_log. by split_and!. }
  have Hti2 : wm_tid m = Some (fin_to_nat (nat_to_fin Hilt)) by rewrite Hcn.
  have Hnec : nat_to_fin Hjlt <> nat_to_fin Hilt.
  { intros Heq. apply Hne. by rewrite -Hcn -Hcn' Heq. }
  have Hlt := Hnv p m (nat_to_fin Hilt) a Hp Hti2 Hak Hnpub Hb
                (nat_to_fin Hjlt) Hnec.
  rewrite -Hcn' obs_flr_hart in Hfl. lia.
Qed.
