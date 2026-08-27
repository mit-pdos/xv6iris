(* RiscvExec.v -- the run/exec interpreters, determinism bridge, wp_exec_step. *)
(* stdpp's [gmap]/[bv] BEFORE the model, exactly as RiscvPtsto.v does: the    *)
(* memory-model interp bundle below is stated over [gmap Arch.pa (bv 8)].     *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto HartBlock.
(* the TSO machine's pure layer and ghosts (tso-machine-flip.md): [pwmsg],
   [flat]/[latest], [view_auth].  Import is not transitive, so requiring
   RiscvPtsto does not put these in scope. *)
Require Import TsoMemPa TsoGhost.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Local Open Scope Z_scope.

(* ===== RiscvModelExec ===== *)
(* ====================================================================== *)
(* RiscvModelExec.v                                                        *)
(*                                                                         *)
(* A functional partial interpreter [exec] mirroring the relational [run] *)
(* of RiscvModelLang, plus the DETERMINISM bridge:                         *)
(*   exec m s = Some (x,s')  ->  run m s x s'  /\  run m s is unique.      *)
(* From that, a single reusable WP rule [wp_exec_step]: [prim_step] picks  *)
(* the tick flag nondeterministically, so the caller supplies exec         *)
(* witnesses for BOTH [riscv_step false] and [riscv_step true] (each       *)
(* branch deterministic; the unique-run discharges wp_lift_step's          *)
(* "forall next-state" obligation), and the continuation re-establishes   *)
(* [mstate_interp] for whichever successor the step took.                  *)
(*                                                                         *)
(* [run]/[prim_step]/RiscvModelLang are UNCHANGED; [exec] is auxiliary.    *)
(*                                                                         *)
(* The pure byte/bitvector arithmetic ([read_bytes], [read_bytes_spec],    *)
(* [bv_eq_of_bytes], ...) lives in RiscvModelBytes.v, which is iris-free    *)
(* so that vanilla Coq [rewrite ... by ...] / comma-chained rewrites work   *)
(* there.  RiscvModelBytes re-defines [pa_add]/[nth_byte] with the *same*   *)
(* bodies as RiscvModelLang's, so they are definitionally convertible and   *)
(* the lemmas below relate to [run] by conversion (no extra bridging).      *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. exec: the functional partial interpreter (mirrors run).              *)
(* ---------------------------------------------------------------------- *)

Fixpoint exec {X} (m : M X) (s : mstate) {struct m} : option (X * mstate) :=
  match m with
  | Interface.Ret y => Some (y, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (X * mstate) with
       | Interface.RegRead r _ => fun k => exec (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v => fun k => exec (k tt) (set_reg s r v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 exec (k (inl (w, None))) (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => exec (k (inl (w, None))) s
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => exec (k (inl None)) (MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             exec (k (inl None))
                  (MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev))
       | Interface.InstrAnnounce _   => fun k => exec (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => exec (k tt) s
       | Interface.Barrier _         => fun k => exec (k tt) s
       | Interface.CacheOp _         => fun k => exec (k tt) s
       | Interface.TlbOp _           => fun k => exec (k tt) s
       | Interface.TakeException _   => fun k => exec (k tt) s
       | Interface.ReturnException _ => fun k => exec (k tt) s
       | Interface.TranslationStart _=> fun k => exec (k tt) s
       | Interface.TranslationEnd _  => fun k => exec (k tt) s
       | Interface.CycleCount        => fun k => exec (k tt) s
       | Interface.Message _         => fun k => exec (k tt) s
       | Interface.GetCycleCount     => fun k => exec (k 0%Z) s
       | _ => fun _ => None   (* Choose / GenericFail / Discard / ExtraOutcome: stuck *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. Determinism bridge: exec success => the unique run.                  *)
(* ---------------------------------------------------------------------- *)

Lemma exec_run_det {X} (m : M X) :
  forall s x s', exec m s = Some (x, s') ->
    run m s x s' /\ (forall y s2, run m s y s2 -> y = x /\ s2 = s').
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hexec.
  - (* Ret *) simpl in Hexec. injection Hexec as <- <-. simpl. split.
    + done.
    + intros y2 s2 [<- <-]. done.
  - (* Next *) destruct oc; simpl in Hexec; try discriminate;
      (* handle the deterministic non-memory branches uniformly *)
      try (split;
           [ apply (proj1 (IH _ _ _ _ Hexec))
           | intros y2 s2 Hr; simpl in Hr; exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr) ]).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * (* device fabric *)
        destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        split.
        { simpl. rewrite Hd Hdr. exact (proj1 (IH _ _ _ _ Hexec)). }
        { intros y2 s2 Hr. simpl in Hr. rewrite Hd Hdr in Hr.
          exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr). }
      * (* RAM *)
        destruct (read_bytes s.(mem) _ _) as [w0|] eqn:Hrb;
          [|discriminate].
        destruct (IH (inl (w0, None)) s x s' Hexec) as [Hrun0 Huniq0].
        split.
        { simpl. rewrite Hd. exists w0. split; [|exact Hrun0].
          intros j Hj. apply (read_bytes_spec _ _ _ _ Hrb j Hj). }
        { intros y2 s2 Hr. simpl in Hr. rewrite Hd in Hr.
          destruct Hr as (w & Hbytes & Hrun).
          assert (Hweq : w = w0).
          { apply bv_eq_of_bytes. intros j Hj.
            pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
            pose proof (Hbytes j Hj) as Hw.
            rewrite Hw in H0. apply Some_inj in H0. exact H0. }
          subst w. exact (Huniq0 _ _ Hrun). }
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * (* device fabric *)
        destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        split.
        { simpl. rewrite Hd Hdw. exact (proj1 (IH _ _ _ _ Hexec)). }
        { intros y2 s2 Hr. simpl in Hr. rewrite Hd Hdw in Hr.
          exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr). }
      * (* RAM *)
        split.
        { simpl. rewrite Hd. exact (proj1 (IH _ _ _ _ Hexec)). }
        { intros y2 s2 Hr. simpl in Hr. rewrite Hd in Hr.
          exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr). }
Qed.

(* ---------------------------------------------------------------------- *)
(* 2b. THE SOLO-BLOCK BRACKET, closed against [exec].                       *)
(*                                                                          *)
(* [HartBlock.hart_block_run] says a contiguous, interference-free run of    *)
(* the node semantics from the start of a cycle to the next boundary is one  *)
(* old [run]; [exec_run_det] says [run] is functional wherever [exec]        *)
(* succeeds.  Together: a solo block's END STATE IS THE CERTIFIED ONE.  That *)
(* is what lets the whole-instruction certification data already in the tree *)
(* (the [exec_*] catalogue, the decode bridge, every leaf's interpreter-run  *)
(* fact) be CONSUMED by the node-granular adapter rather than re-derived.    *)
(*                                                                          *)
(* POST-FLIP (tso-machine-flip.md RULING 3) the bracket carries the SOLO     *)
(* ERA with it: [mblock h img] is a chain of node steps each of which sees   *)
(* the flat tie ([s.(mem) = flat img log]) and a log holding nothing but     *)
(* hart [h]'s own messages -- exactly the situation of the boot bracket and  *)
(* of the device-conformance tester, and exactly what collapses the plain    *)
(* load's [tso_read] back onto [exec]'s flat read.  [exec] itself is         *)
(* UNCHANGED: run/exec stay flat, which is the whole point of the ruling.    *)
(* ---------------------------------------------------------------------- *)

(* [h] and [img] are left to inference rather than annotated: this file does
   NOT Import [TsoMemPa] (Import is not transitive) nor stdpp's bitvector
   notations, so neither [agent] nor [bv] is spellable here -- and [mblock]
   pins both anyway. *)
Corollary hart_block_exec h img (tick : bool) (s s' s'' : mstate) :
  exec (riscv_step tick) s = Some (tt, s'') ->
  mblock h img (riscv_step tick, s) (Interface.Ret tt, s') ->
  s' = s''.
Proof.
  intros He Hb. destruct (exec_run_det _ _ _ _ He) as [_ Huniq].
  by destruct (Huniq _ _ (hart_block_run _ _ _ _ _ Hb)) as [_ ->].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The reusable WP rule for deterministic ops.                          *)
(* ---------------------------------------------------------------------- *)

(* the generation of a generation-indexed thread expression (the power
   thread has none) *)
Definition thread_gen (e : mexpr) : option nat :=
  match e with
  | HartE gen _ _ => Some gen
  | UartLoopE gen => Some gen
  | DiskLoopE gen => Some gen
  | PlicLoopE gen => Some gen
  | PowerLoopE => None
  end.

Section WPDead.
  Context `{!riscvFixedGS Σ}.

  (* THE CORPSE RULE (claude-notes/design/crash.md): a dead generation's
     thread self-loops forever, from the death certificate ALONE -- no era
     resources, any postcondition.  This is what the base rules tail into
     when they discover their generation has passed, and it is the whole
     reason abandoning a generation's resources is sound. *)
  Lemma wp_dead (e : mexpr) (gen : nat) :
    thread_gen e = Some gen ->
    gen_dead gen ⊢ WP (e : expr riscv_lang).
  Proof.
    intros Hg.
    iIntros "#Hdead". iLöb as "IH".
    iApply wp_lift_step; first by destruct e.
    iIntros (g ns κ κs nt) "(Hgauth & Hsi)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hdead") as %[_ Hge].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
    assert (Hnl : ~ thread_live g gen).
    { intros [_ Heq]. lia. }
    iSplitR.
    { iPureIntro. destruct e; simplify_eq/=.
      - exists [], (HartE gen cpu m), g, [].
        by apply prim_step_hart_dead.
      - exists [], (UartLoopE gen), g, [].
        right; left. exists gen. split_and!; auto.
      - exists [], (DiskLoopE gen), g, [].
        right; right; left. exists gen. split_and!; auto.
      - exists [], (PlicLoopE gen), g, [].
        right; right; right; left. exists gen. split_and!; auto. }
    iIntros (e2 g2 efs Hstep) "!>".
    (* only the corpse arm is enabled *)
    assert (e2 = e /\ g2 = g /\ efs = []) as (-> & -> & ->).
    { destruct e; simplify_eq/=.
      - destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
          as (-> & -> & [(Hlive & _) | (_ & -> & ->)]);
          [exfalso; by apply Hnl|done].
      - destruct (prim_step_uart_inv _ _ _ _ _ _ Hstep)
          as (-> & -> & -> & [(Hlive & _) | (_ & ->)]);
          [exfalso; by apply Hnl|done].
      - destruct (prim_step_disk_inv _ _ _ _ _ _ Hstep)
          as (-> & -> & -> & [(Hlive & _) | (_ & ->)]);
          [exfalso; by apply Hnl|done].
      - destruct (prim_step_plic_inv _ _ _ _ _ _ Hstep)
          as (-> & -> & -> & [(Hlive & _) | (_ & ->)]);
          [exfalso; by apply Hnl|done]. }
    iIntros "_". iMod "Hback" as "_". iModIntro.
    iFrame "Hgauth Hsi". iSplitL; [|done].
    iApply "IH".
  Qed.
End WPDead.

(* ====================================================================== *)
(* 2c. THE MEMORY-MODEL INTERP BUNDLE, HART-LOCAL                          *)
(*     (tso-machine-flip.md §6 amendment A6.1).                            *)
(*                                                                         *)
(* [RiscvPtsto.tso_interp_at] is stated at a [gstate]: its view authority   *)
(* is at [avf g], the WHOLE per-agent view function.  A leaf works at       *)
(* [mstate] and must never see [g], so the lifting rules hand it the        *)
(* GSTATE-FREE repackaging below -- the same body with [gimg]/[gmem]/       *)
(* [glog]/[avf g] abstracted, and [mm_ok]'s single pure conjunct restated   *)
(* as the ties that mention only the abstracted arguments.                  *)
(*                                                                         *)
(* THE THIRD PURE TIE ([∀ h, NCPU ≤ h → V h = length log]) is not in        *)
(* [mm_ok] and has to be here: it is RULING 2 / §4's "the bus-master        *)
(* agents are PINNED TO THE TOP", true of [avf] by construction, and        *)
(* without it a callback holding only an abstract [V] could not say what    *)
(* the non-hart entries of its returned view function are -- which is       *)
(* exactly what [vstep] below has to know.                                  *)
(*                                                                         *)
(* IT LIVES HERE, NOT IN RiscvPtsto.v, and so pays a [⊣⊢] rather than       *)
(* being definitional: every leaf already Requires this file, and iterating *)
(* on RiscvPtsto.v costs a ~20-minute rebuild per attempt.  IF THE [⊣⊢]     *)
(* UNFOLDING EVER MEASURES AS A PROOF-PERFORMANCE HAZARD, moving            *)
(* [tso_interp_of] into RiscvPtsto.v and defining [tso_interp_at] as its    *)
(* instance at [avf g] is a MECHANICAL follow-up: the bodies are already    *)
(* the same up to the pure conjunct.                                        *)
(* ====================================================================== *)

(* THE VIEW FUNCTION AFTER ONE AGENT'S STEP.  Agent [h] takes its new view;
   the other HARTS keep theirs; every non-hart (bus-master) agent stays
   pinned to the TOP OF THE NEW LOG -- which is why a store's append moves
   the disk's view for free and no rule has to update it.  This is the
   function the σ-callback owes its bundle back at, and the lifting rules
   discharge [avf g' =₁ vstep …] against it ([avf_hart_node]). *)
Definition vstep (h : agent) (tv' : nat) (log' : list pwmsg)
    (V : agent -> nat) : agent -> nat :=
  fun h' => if decide (h' = h) then tv'
            else if lt_dec h' NCPU then V h' else length log'.

(* the [gstate]-side computation the lifting rules must match: a hart node
   moves ONE hart's view and possibly appends, and [avf] of the written-back
   state is exactly [vstep] of [avf] of the old one.  Pointwise (no
   functional extensionality; [tso_interp_of_ext] closes the gap). *)
Lemma avf_hart_node (g : gstate) (cpu : CPU) (rs' : regstate)
    (mem' : gmap Arch.pa (bv 8)) (d' : dev_state) (r' : option resv)
    (log' : list pwmsg) (tv' : nat) (h' : agent) :
  avf (GState (<[cpu := rs']> g.(gregs)) mem' d' g.(ggen) g.(gpow)
         (<[cpu := r']> g.(gresv)) g.(gimg) log' (<[cpu := tv']> g.(gtv))) h'
  = vstep (hart_agent cpu) tv' log' (avf g) h'.
Proof.
  rewrite /avf /vstep /hart_agent /insert /gtv_insert.
  destruct (lt_dec h' NCPU) as [Hlt|Hge]; cbn [gtv glog].
  (* [case_decide] and NOT [destruct (decide …)]: the two [decide]s carry
     DIFFERENT [EqDecision] instances (the hart index's [fin], the agent's
     [nat]), so a spelled-out [decide] fails to match the goal's term. *)
  - assert (Hf : fin_to_nat (nat_to_fin Hlt) = h') by apply fin_to_nat_to_fin.
    case_decide as Hd1; case_decide as Hd2; try done.
    + exfalso. apply Hd2. rewrite -Hf. by rewrite Hd1.
    + exfalso. apply Hd1, (inj fin_to_nat). by rewrite Hf.
  - case_decide as Hd2; [|done].
    exfalso. apply Hge. rewrite Hd2. apply fin_to_nat_lt.
Qed.

(* … and the DISK's (A6.2): a DMA step moves no hart's view, and the disk's
   own is pinned to the top, so [vstep] at [disk_agent] and the new log's
   length is the whole update -- and it is a no-op on the arm that appends
   nothing. *)
Lemma avf_disk_node (g : gstate) (mem' : gmap Arch.pa (bv 8))
    (d' : dev_state) (log' : list pwmsg) (h' : agent) :
  avf (GState g.(gregs) mem' d' g.(ggen) g.(gpow) g.(gresv)
         g.(gimg) log' g.(gtv)) h'
  = vstep disk_agent (length log') log' (avf g) h'.
Proof.
  rewrite /avf /vstep /disk_agent.
  destruct (lt_dec h' NCPU) as [Hlt|Hge]; cbn [gtv glog].
  - case_decide as Hd; [exfalso; lia|done].
  - case_decide as Hd; done.
Qed.

(* the view function is UNCHANGED by a step that neither appends nor moves
   the stepping agent's view -- the non-hart entries by the bundle's pinning
   tie, which is exactly why that tie is in the bundle (A6.1). *)
Lemma vstep_idle (V : agent -> nat) (log : list pwmsg) (h h' : agent) :
  (∀ h0, (NCPU ≤ h0)%nat -> V h0 = length log) ->
  vstep h (V h) log V h' = V h'.
Proof.
  intros Hpin. rewrite /vstep. case_decide as Hd; [by subst|].
  destruct (lt_dec h' NCPU) as [|Hge]; [done|]. symmetry. apply Hpin. lia.
Qed.

(* the stepping agent's own entry of its own step's view function *)
Lemma vstep_self (h : agent) (t : nat) (log : list pwmsg) (V : agent -> nat) :
  vstep h t log V h = t.
Proof. rewrite /vstep. by case_decide. Qed.

(* ---------------------------------------------------------------------- *)
(* THE GATE BRIDGE (tso-machine-flip.md §6 amendment A6.1 vs the step-4     *)
(* kit).  [TsoCtx.ctx_load_ok] -- the load gate that discharges §6's        *)
(* [Mobl_ram_plain] -- is stated at a [gstate] and [tso_interp_at]; A6.1    *)
(* says a LEAF must never see a [gstate], so the leaf rules hand over       *)
(* [tso_interp_of], the gstate-free bundle.  The two were designed against  *)
(* different assumptions and meet here.                                     *)
(*                                                                          *)
(* They reconcile because [tso_interp_at] READS ONLY four fields of its     *)
(* [gstate] -- [gimg], [gmem], [glog], [gtv] -- so the bundle can           *)
(* RECONSTRUCT one, with the other five filled by anything.  The step that  *)
(* makes it work is [avf (gs_of …) =₁ V], and that needs exactly the        *)
(* bundle's THIRD pure tie (bus-master agents pinned to the top): [avf]     *)
(* answers [length log] off the hart range, so without the tie [V] would be *)
(* unconstrained there.  The tie was added for [vstep]'s idle case; it is   *)
(* what makes the gate reachable at all.                                    *)
(* ---------------------------------------------------------------------- *)
Definition gs_of (img mem : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (V : agent -> nat) (rs : regstate) (d : dev_state) : gstate :=
  GState (fun _ => rs) mem d 0%nat true (fun _ => None) img log
         (fun c => V (hart_agent c)).

Lemma avf_gs_of (img mem : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (V : agent -> nat) (rs : regstate) (d : dev_state) (h : agent) :
  (∀ h', (NCPU ≤ h')%nat -> V h' = length log) ->
  avf (gs_of img mem log V rs d) h = V h.
Proof.
  intros Hpin. rewrite /avf /gs_of /hart_agent. cbn [gtv glog].
  destruct (lt_dec h NCPU) as [Hlt|Hge].
  - f_equal. apply fin_to_nat_to_fin.
  - symmetry. apply Hpin. lia.
Qed.

Section TsoBundle.
  Context `{!riscvFixedGS Σ}.

  Definition tso_interp_of (E : riscvEraGS)
      (img mem : gmap Arch.pa (bv 8)) (log : list pwmsg) (V : agent -> nat)
      : iProp Σ :=
    (∃ (TM : gmap Arch.pa ts_elem) (LM : gmap nat pwmsg),
       ghost_map_auth (era_ts_name E) 1 TM ∗
       ⌜dom TM = dom mem⌝ ∗
       (* one conjunct; see [RiscvPtsto.tso_interp_at]'s note *)
       ⌜∀ a e, TM !! a = Some e → ts_ok img mem log a e⌝ ∗
       ghost_map_auth (era_logm_name E) 1 LM ∗
       ⌜∀ i, LM !! i = log !! i⌝ ∗
       mono_nat_auth_own (era_loglen_name E) 1 (length log) ∗
       view_auth (era_view_name E) V ∗
       ⌜mem = flat img log⌝ ∗
       ⌜∀ h, (V h ≤ length log)%nat⌝ ∗
       ⌜∀ h, (NCPU ≤ h)%nat -> V h = length log⌝ ∗
       (* THE ERA IMAGE COVERS RAM ([RiscvLang.mm_ok]'s third conjunct,
          A6.78) -- carried here for the same reason the flat tie is: the
          [⊣⊢] with [tso_interp_at] has to reconstruct it, and the "no
          evidence" read's obligation ([TsoCtx.ledger_read_any_ram_ok]) is
          discharged from it INSIDE a leaf, where no [gstate] is in
          scope. *)
       ⌜∀ a : Arch.pa,
          (ram_lo <= SailStdpp.Operators_mwords.uint a < ram_hi)%Z ->
          is_Some (img !! a)⌝)%I.

  (* [viewUR] is a [discrete_funUR], so its [≡] IS pointwise equality --
     which is why the bundle can be re-indexed by a pointwise-equal view
     function without functional extensionality. *)
  Lemma view_auth_ext (γ : gname) (V V' : agent -> nat) :
    (∀ h, V h = V' h) -> view_auth γ V ⊣⊢ view_auth γ V'.
  Proof.
    intros HV. rewrite /view_auth.
    assert (vf V ≡ vf V') as Heq by (intros h; by rewrite /vf HV).
    by rewrite Heq.
  Qed.

  Lemma tso_interp_of_ext E img mem log (V V' : agent -> nat) :
    (∀ h, V h = V' h) ->
    tso_interp_of E img mem log V ⊣⊢ tso_interp_of E img mem log V'.
  Proof.
    intros HV. rewrite /tso_interp_of. iSplit.
    - iIntros "H". iDestruct "H" as (TM LM)
        "(Hts & %H1 & %H2 & Hlm & %H3 & Hll & Hv & %H4 & %H5 & %H6 & %H7)".
      iExists TM, LM.
      rewrite -(view_auth_ext (era_view_name E) V V' HV).
      iFrame "Hts Hlm Hll Hv". iPureIntro. split_and!; try done.
      + intros h. rewrite -HV. apply H5.
      + intros h Hh. rewrite -HV. by apply H6.
    - iIntros "H". iDestruct "H" as (TM LM)
        "(Hts & %H1 & %H2 & Hlm & %H3 & Hll & Hv & %H4 & %H5 & %H6 & %H7)".
      iExists TM, LM.
      rewrite (view_auth_ext (era_view_name E) V V' HV).
      iFrame "Hts Hlm Hll Hv". iPureIntro. split_and!; try done.
      + intros h. rewrite HV. apply H5.
      + intros h Hh. rewrite HV. by apply H6.
  Qed.

  (* THE SEAM, in one line: the era's TSO conjunct IS the bundle at the
     machine's own image/cache/log and at [avf g]. *)
  Lemma tso_interp_at_of (E : riscvEraGS) (g : gstate) :
    tso_interp_at E g ⊣⊢
    tso_interp_of E g.(gimg) g.(gmem) g.(glog) (avf g).
  Proof.
    rewrite /tso_interp_at /tso_interp_of. iSplit.
    - iIntros "H". iDestruct "H" as (TM LM)
        "(Hts & %Hdom & %Hlat & Hlm & %Hlm2 & Hll & Hv & %Hmm)".
      destruct Hmm as (Hflat & Htv & Hcov).
      iExists TM, LM. iFrame "Hts Hlm Hll Hv". iPureIntro.
      split_and!; [exact Hdom|exact Hlat|exact Hlm2|exact Hflat| | |exact Hcov].
      + intros h. rewrite /avf. destruct (lt_dec h NCPU) as [Hlt|]; [|lia].
        apply Htv.
      + intros h Hh. rewrite /avf.
        destruct (lt_dec h NCPU) as [Hlt|]; [lia|done].
    - iIntros "H". iDestruct "H" as (TM LM)
        "(Hts & %Hdom & %Hlat & Hlm & %Hlm2 & Hll & Hv & %Hflat & %HV & _ & %Hcov)".
      iExists TM, LM. iFrame "Hts Hlm Hll Hv". iPureIntro.
      split_and!; [exact Hdom|exact Hlat|exact Hlm2|].
      split_and!; [exact Hflat| |exact Hcov].
      intros c. rewrite -(avf_hart g c). apply HV.
  Qed.

  (* THE IMAGE-COVERAGE ACCESSOR, so no leaf ever destructures the bundle:
     the "no evidence" read's whole obligation, at the leaf's own
     abstracted [img] ([TsoCtx.ledger_read_any_ram_ok] is the [gstate]-side
     twin, reached through [tso_interp_of_at_gs]). *)
  Lemma tso_interp_of_img_cover E img mem log (V : agent -> nat) :
    tso_interp_of E img mem log V -∗
    ⌜∀ a : Arch.pa,
       (ram_lo <= SailStdpp.Operators_mwords.uint a < ram_hi)%Z ->
       is_Some (img !! a)⌝.
  Proof.
    iIntros "H". iDestruct "H" as (TM LM) "(_&_&_&_&_&_&_&_&_&_&%Hc)".
    iPureIntro. exact Hc.
  Qed.

  Lemma tso_interp_of_mono E img mem log (V V' : agent -> nat) :
    (∀ h, V h = V' h) ->
    tso_interp_of E img mem log V -∗ tso_interp_of E img mem log V'.
  Proof.
    intros HV. rewrite (tso_interp_of_ext _ _ _ _ V V' HV). iIntros "$".
  Qed.

  (* THE IDLE RETURN: a node that neither appends nor moves this agent's view
     gives the bundle back exactly as it got it.  What every register /
     announce / MMIO leaf and the boundary rule use. *)
  Lemma tso_interp_of_idle E img mem log (V : agent -> nat) (h : agent) :
    tso_interp_of E img mem log V -∗
    tso_interp_of E img mem log (vstep h (V h) log V).
  Proof.
    iIntros "H". iDestruct "H" as (TM LM)
      "(Hts & %H1 & %H2 & Hlm & %H3 & Hll & Hv & %H4 & %H5 & %H6 & %H7)".
    iApply (tso_interp_of_mono E img mem log V (vstep h (V h) log V)
              (fun h' => eq_sym (vstep_idle V log h h' H6))).
    iExists TM, LM. iFrame "Hts Hlm Hll Hv". iPureIntro. by split_and!.
  Qed.

  (* the view bound, read off the bundle -- what makes an advance MONOTONE
     rather than an arbitrary jump, and what every leaf needs before it can
     move its own view *)
  Lemma tso_interp_of_bound E img mem log (V : agent -> nat) :
    tso_interp_of E img mem log V -∗ ⌜∀ h, (V h ≤ length log)%nat⌝.
  Proof.
    iIntros "H". iDestruct "H" as (TM LM) "(_&_&_&_&_&_&_&_&%Hb&_)".
    iPureIntro. exact Hb.
  Qed.

  (* THE RECEIPT (tso-machine-flip.md §6 amendment A6.6).  The view
     authority is open exactly once per leaf, and that is where [view_lb] is
     BORN: minting it is an INCLUSION, not an update, so it is free and the
     authority comes back untouched.  Persistent, so a consumer that does not
     want the receipt simply drops it.  [TsoCtx.hart_view_lb] is the
     Σ-surface wrapper over this; the leaf file states the machine-level
     fact and does not import the context algebra to do it. *)
  Lemma tso_interp_of_receipt E img mem log (V : agent -> nat) (h : agent) :
    tso_interp_of E img mem log V -∗
    tso_interp_of E img mem log V ∗
    view_lb (era_view_name E) (era_loglen_name E) h (V h).
  Proof.
    iIntros "H". iDestruct "H" as (TM LM)
      "(Hts & %H1 & %H2 & Hlm & %H3 & Hll & Hv & %H4 & %H5 & %H6 & %H7)".
    iDestruct (view_lb_get (era_view_name E) (era_loglen_name E) V
                 (length log) h (H5 h) with "Hv Hll") as "(Hv & Hll & #Hrec)".
    iFrame "Hrec". iExists TM, LM. iFrame "Hts Hlm Hll Hv". iPureIntro.
    by split_and!.
  Qed.

  (* the same at a NAMED index -- the form the leaves use, so no [vstep]
     ever has to be rewritten inside an Iris hypothesis *)
  Lemma tso_interp_of_receipt_at E img mem log (V : agent -> nat) (h : agent)
      (K : nat) :
    V h = K ->
    tso_interp_of E img mem log V -∗
    tso_interp_of E img mem log V ∗
    view_lb (era_view_name E) (era_loglen_name E) h K.
  Proof. intros <-. apply tso_interp_of_receipt. Qed.

  (* the bus-master pinning tie, read off the bundle -- the half of the
     [avf] reconstruction that [mm_ok] does not carry *)
  Lemma tso_interp_of_pin E img mem log (V : agent -> nat) :
    tso_interp_of E img mem log V -∗
    ⌜∀ h, (NCPU ≤ h)%nat -> V h = length log⌝.
  Proof.
    iIntros "H". iDestruct "H" as (TM LM) "(_&_&_&_&_&_&_&_&_&%Hp&_)".
    iPureIntro. exact Hp.
  Qed.

  (* THE DISK'S IDLE RETURN (§6 amendments A6.2 + A6.11).  Five of
     [disk_step]'s six arms write nothing, and after A6.11 they SAY so
     ([W = ∅], hence [log' = log]); what they owe back is the bundle at
     [vstep disk_agent (length log) log V], which is the bundle they were
     given -- because [avf] pins every bus-master agent to the top, so
     [V disk_agent] IS [length log] and [vstep] is the identity there.
     Spelled once so [WpUart]'s four framing arms are one line each. *)
  Lemma tso_interp_of_disk_idle E img mem log (V : agent -> nat) :
    tso_interp_of E img mem log V -∗
    tso_interp_of E img mem log (vstep disk_agent (length log) log V).
  Proof.
    iIntros "H". iDestruct (tso_interp_of_pin with "H") as %Hp.
    rewrite -(Hp disk_agent (Nat.le_refl NCPU)).
    iApply (tso_interp_of_idle with "H").
  Qed.

  (* THE BRIDGE ITSELF: the leaf's bundle IS the kit's [tso_interp_at], at a
     reconstructed [gstate].  Both directions, so a gate can be applied and
     the bundle handed back.  [rs]/[d] are arbitrary -- [tso_interp_at] never
     looks at [gregs]/[gdev]/[ggen]/[gpow]/[gresv]. *)
  Lemma tso_interp_of_at_gs E img mem log (V : agent -> nat)
      (rs : regstate) (d : dev_state) :
    (∀ h, (NCPU ≤ h)%nat -> V h = length log) ->
    tso_interp_of E img mem log V ⊣⊢
    tso_interp_at E (gs_of img mem log V rs d).
  Proof.
    intros Hpin. rewrite tso_interp_at_of. cbn [gimg gmem glog].
    apply tso_interp_of_ext. intros h. symmetry. by apply avf_gs_of.
  Qed.

  (* THE MONOTONE ADVANCE: this agent's view moves forward, nothing else
     changes.  What a PLAIN LOAD's drain and a DRAINING FENCE both do, and
     the only ghost UPDATE the view authority ever needs on the hart side
     ([TsoGhost.view_auth_update]; the receipt [hart_view_lb] is minted
     separately, §6).  [h < NCPU] because a bus-master agent's view is
     pinned to the top and may only move with the log. *)
  Lemma tso_interp_of_advance E img mem log (V : agent -> nat)
      (h : agent) (t : nat) :
    (h < NCPU)%nat -> (V h ≤ t)%nat -> (t ≤ length log)%nat ->
    tso_interp_of E img mem log V ==∗
    tso_interp_of E img mem log (vstep h t log V).
  Proof.
    iIntros (Hh Hle Htop) "H". iDestruct "H" as (TM LM)
      "(Hts & %H1 & %H2 & Hlm & %H3 & Hll & Hv & %H4 & %H5 & %H6 & %H7)".
    assert (Hmono : ∀ h', (V h' ≤ vstep h t log V h')%nat).
    { intros h'. rewrite /vstep. case_decide as Hd; [by subst|].
      destruct (lt_dec h' NCPU) as [|Hge]; [done|].
      rewrite H6; [done|lia]. }
    iMod (view_auth_update _ V (vstep h t log V) Hmono with "Hv") as "Hv".
    iModIntro. iExists TM, LM. iFrame "Hts Hlm Hll Hv". iPureIntro.
    split_and!; [done|done|done|done| | |done].
    - intros h'. rewrite /vstep. case_decide as Hd; [exact Htop|].
      destruct (lt_dec h' NCPU); [apply H5|lia].
    - intros h' Hh'. rewrite /vstep. case_decide as Hd; [lia|].
      destruct (lt_dec h' NCPU); [lia|done].
  Qed.

  (* "DRAIN, THEN READ MEMORY": the exclusive read's move -- the view goes to
     the TOP and the receipt says so.  The one place an ACQUIRE receipt at the
     top is honestly produced (the AMO/conditional write's success arm gets
     its own by [tso_interp_of_receipt] on the post-append bundle, whose top
     it already sits at). *)
  Lemma tso_interp_of_top E img mem log (V : agent -> nat) (h : agent) :
    (h < NCPU)%nat ->
    tso_interp_of E img mem log V ==∗
    tso_interp_of E img mem log (vstep h (length log) log V) ∗
    view_lb (era_view_name E) (era_loglen_name E) h (length log).
  Proof.
    iIntros (Hh) "H".
    iDestruct (tso_interp_of_bound with "H") as %Hb.
    iMod (tso_interp_of_advance _ _ _ _ _ h (length log) Hh (Hb h)
            (Nat.le_refl (length log)) with "H") as "H".
    (* the receipt's index IS the top: [vstep] at the stepping agent *)
    iDestruct (tso_interp_of_receipt_at _ _ _ _ _ h (length log)
                 (vstep_self h (length log) log V) with "H") as "[H Hrec]".
    iModIntro. iFrame "H Hrec".
  Qed.

  (* THE WRITE-BACK, in one step: the bundle a hart's σ-callback returns IS
     the era's TSO conjunct at the written-back machine state.  This is where
     [vstep] meets [avf] and the two are discharged against each other; both
     hart lifting rules below use nothing else. *)
  Lemma tso_interp_hart_wb (E : riscvEraGS) (g : gstate) (cpu : CPU)
      (rs' : regstate) (mem' : gmap Arch.pa (bv 8)) (d' : dev_state)
      (r' : option resv) (log' : list pwmsg) (tv' : nat) :
    tso_interp_of E g.(gimg) mem' log' (vstep (hart_agent cpu) tv' log' (avf g))
    -∗ tso_interp_at E (GState (<[cpu := rs']> g.(gregs)) mem' d' g.(ggen)
                          g.(gpow) (<[cpu := r']> g.(gresv)) g.(gimg) log'
                          (<[cpu := tv']> g.(gtv))).
  Proof.
    iIntros "H". rewrite tso_interp_at_of.
    rewrite (tso_interp_of_ext _ _ _ _ _ _
               (avf_hart_node g cpu rs' mem' d' r' log' tv')).
    iExact "H".
  Qed.

  (* … and the disk's (A6.2).  Same shape; the disk agent's own view rides
     the append, so [vstep disk_agent (length log') log'] is the whole move. *)
  Lemma tso_interp_disk_wb (E : riscvEraGS) (g : gstate)
      (mem' : gmap Arch.pa (bv 8)) (d' : dev_state) (log' : list pwmsg) :
    tso_interp_of E g.(gimg) mem' log'
      (vstep disk_agent (length log') log' (avf g))
    -∗ tso_interp_at E (GState g.(gregs) mem' d' g.(ggen) g.(gpow) g.(gresv)
                          g.(gimg) log' g.(gtv)).
  Proof.
    iIntros "H". rewrite tso_interp_at_of.
    rewrite (tso_interp_of_ext _ _ _ _ _ _ (avf_disk_node g mem' d' log')).
    iExact "H".
  Qed.
End TsoBundle.

Section WPExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE SINGLE PER-HART FRAMING POINT, now per NODE of the Sail monad
     instead of per whole instruction.  Everything else about it is
     unchanged from the whole-instruction rule it replaces: it takes the
     thread's [gen_cert] and cases four ways on the current [(ggen, gpow)].
     LIVE (power on, generation current): the registry element ties the
     ambient era to [state_interp]'s existential, and the caller's callback
     sees exactly [mstate_interp] -- ONE HART'S VIEW, the same currency the
     whole-instruction rule handed over, which is why the leaves' σ-callbacks
     keep their shape.  DEAD (generation passed): tail into [wp_dead].
     Current-but-off: refuted by the STARTED certificate.  Unborn: refuted
     by the birth certificate.

     THE CALLER OWES, at the node [m]:
       - a WITNESS successor, i.e. that the node is not stuck; and
       - the continuation at EVERY successor the node admits.
     The ∀ is what the semantic delta costs: a node with a nondeterministic
     arm (an MMIO read is deterministic, a RAM read is not -- the value is
     pinned only by what the caller owns) hands the continuation whatever the
     machine chose.  Callers that step a DETERMINISTIC node discharge the ∀
     from a determinism fact, exactly as the old rule discharged
     [wp_lift_step]'s "forall next-state" obligation from [exec_run_det].

     THE RESERVATION CONTEXT (design §3a) is ∀-quantified: [oth] is what the
     other harts have reserved, [r] this hart's own reservation.  Neither is
     tracked by [state_interp] yet, so the caller learns nothing about them
     and owes a witness and a continuation for EVERY value -- which is
     exactly enough: a register node ignores them; a RAM write or an
     exclusive read whose footprint meets [oth] SELF-LOOPS, and the memory
     rules absorb that arm by Löb.  Only the conditional-write rule needs to
     KNOW [r] (to learn the RMW's old value), and that is the rule that will
     hand [state_interp] the [resv_frag]/[resv_ok] pair. *)
  (* THE RESERVATION-AGNOSTIC FORM.  Usable exactly by the rules whose arms
     never touch the hart's reservation -- register nodes, announces, plain
     and MMIO READS -- because writing back the value already there is a
     no-op on the mirror's auth ([RiscvPtsto.resv_map_insert_id]).  Every arm
     that CHANGES it (any RAM/MMIO write, the exclusive read, the [Ret]
     boundary) needs [wp_hart_step_resv] below instead: a [ghost_map] auth
     cannot be updated without its fragment. *)
  (* THE MEMORY-MODEL CONTEXT (tso-machine-flip.md §6 amendment A6.1) rides
     beside the reservation context and is ∀-quantified the same way: [img]
     is the era image, [log] the write log, [V] the per-agent view function
     and [tv] THIS hart's entry of it (handed over separately so a leaf can
     name its own view without projecting [V]).  The callback gets the
     ghosts as [tso_interp_of] -- the gstate-free bundle -- and owes it back
     at the node's [log'] and at [vstep], the view function after this
     hart's move.  A leaf that touches no memory returns it unchanged modulo
     [vstep]'s no-op ([tso_interp_of_ext]); the load/store/barrier leaves are
     where the four ghost steps live. *)
  Lemma wp_hart_step (m : M unit) :
    (forall oth h img σ log tv r m' σ' log' tv' r',
       mnode_step oth h img σ log tv r m m' σ' log' tv' r' -> r' = r) ->
    gen_cert -∗
    (∀ σ oth r img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ∃ m0 σ0 log0 tv0 r0,
         ⌜mnode_step oth (hart_agent cpu_id) img σ log tv r
            m m0 σ0 log0 tv0 r0⌝ ∗
          ▷ (∀ m' σ' log' tv' r',
               ⌜mnode_step oth (hart_agent cpu_id) img σ log tv r
                  m m' σ' log' tv' r'⌝ ={∅,⊤}=∗
               mstate_interp σ' ∗
               tso_interp_of riscv_eraGS img σ'.(mem) log'
                 (vstep (hart_agent cpu_id) tv' log' V) ∗
               WP (HartE gen_id cpu_id m' : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    intros Hpres.
    iIntros "#(Hborn & Hstarted & Hrege) H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { (* DEAD -- the birth bound rules out the unborn side *)
      assert (Hlt : gen_id < g.(ggen)) by lia.
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      assert (Hnl : ~ thread_live g gen_id) by (intros [_ Hgg]; lia).
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (HartE gen_id cpu_id m), g, [].
        by apply prim_step_hart_dead. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
        as (-> & -> & [(Hlive & _) | (_ & -> & ->)]); [by exfalso|].
      iIntros "_". iMod "Hback" as "_". iModIntro.
      iFrame "Hgauth Hsauth Htie".
      iSplitL "HRauth Hera".
      { iExists R. iFrame "HRauth Hera". iPureIntro. exact Hdom. }
      iSplitL; [|done].
      iApply (wp_dead _ gen_id); [done|]. iExact "Hdead". }
    destruct (g.(gpow)) eqn:Hpw; last first.
    { (* CURRENT BUT POWERED OFF: impossible -- generation [gen_id]'s
         PowerOn has happened ([gen_started]), but the started count reads
         [ggen + 0 = gen_id]. *)
      exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia. }
    assert (Hlive : thread_live g gen_id) by (split; congruence).
    (* LIVE.  Tie the ambient era to the existential via the registry. *)
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Htso & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    (* the era's TSO conjunct, re-indexed as the gstate-free bundle (A6.1) *)
    iEval (rewrite tso_interp_at_of) in "Htso".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev))
            (others_resv g.(gresv) cpu_id) (g.(gresv) cpu_id)
            g.(gimg) g.(glog) (g.(gtv) cpu_id) (avf g)
            with "[] [Hri Hmem Hdev] Htso") as (m0 σ0 log0 tv0 r0) "(%Hwit & Hk)".
    { iPureIntro. apply avf_hart. }
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (HartE gen_id cpu_id m0),
             (GState (<[cpu_id := σ0.(sregs)]> g.(gregs)) σ0.(mem) σ0.(mdev)
                g.(ggen) g.(gpow) (<[cpu_id := r0]> g.(gresv))
                g.(gimg) log0 (<[cpu_id := tv0]> g.(gtv))), [].
      left. exists gen_id, cpu_id, m. split_and!; try reflexivity.
      left. split; [exact Hlive|]. by exists m0, σ0, log0, tv0, r0. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
      as (-> & -> & [(_ & (m2 & σ2 & log2 & tv2 & r2 & Hnode & -> & ->))
                    | (Hnl & _)]);
      last by exfalso.
    (* the hart moved no disk byte: the durable conjunct is FRAMED, at the
       post-state's own image ([RiscvLang.mnode_step_v_disk]) *)
    pose proof (mnode_step_v_disk _ _ _ _ _ _ _ _ _ _ _ _ _ Hnode) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio (mdev σ2))))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (mdev σ2)))
      by (symmetry; exact Hvd).
    iMod ("Hk" $! m2 σ2 log2 tv2 r2 with "[//]")
      as "[(Hri' & Hmem' & Hdev') [Htso' HWP]]".
    iDestruct ("Hclose" with "Hri'") as "Hgr'".
    iDestruct (tso_interp_hart_wb _ g cpu_id σ2.(sregs) σ2.(mem) σ2.(mdev)
                 r2 log2 tv2 with "Htso'") as "Htso2".
    iIntros "_ !>".
    iEval (rewrite /disk_fixed_interp Hvd2) in "Htie".
    rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev' Htso2".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview2. }
    (* the mirror: this rule's arms preserve the reservation, so the auth's
       map is unchanged; [resv_ok] comes from the language's own step
       invariant. *)
    iSplitL "Hresv".
    { iEval (rewrite /resv_auth_at) in "Hresv".
      rewrite /resv_auth_at
        (resv_map_insert_id g.(gresv) cpu_id r2
           (eq_sym (Hpres _ _ _ _ _ _ _ _ _ _ _ _ Hnode))).
      iFrame "Hresv". }
    iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
  Qed.

  (* THE FRAG FORM: for the arms that CHANGE the hart's reservation (every
     RAM/MMIO write, the exclusive read, the [Ret] boundary).  The caller
     brings the hart's [resv_frag] at [rr]; the callback runs at exactly
     [r := rr] (agreement with the auth), learns that a [Some] reservation's
     snapshot still IS memory ([resv_ok], the fact the conditional write
     lives on), and gets the frag back at whatever the arm set. *)
  Lemma wp_hart_step_resv (m : M unit) (rr : option resv) :
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ oth img log tv V, ⌜forall rv, rr = Some rv -> rv ⊆ σ.(mem)⌝ -∗
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ∃ m0 σ0 log0 tv0 r0,
         ⌜mnode_step oth (hart_agent cpu_id) img σ log tv rr
            m m0 σ0 log0 tv0 r0⌝ ∗
          ▷ (∀ m' σ' log' tv' r',
               ⌜mnode_step oth (hart_agent cpu_id) img σ log tv rr
                  m m' σ' log' tv' r'⌝ ={∅,⊤}=∗
               mstate_interp σ' ∗
               tso_interp_of riscv_eraGS img σ'.(mem) log'
                 (vstep (hart_agent cpu_id) tv' log' V) ∗
               (resv_frag cpu_id r' -∗
                WP (HartE gen_id cpu_id m' : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros "#(Hborn & Hstarted & Hrege) Hfrag H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { (* DEAD -- the birth bound rules out the unborn side *)
      assert (Hlt : gen_id < g.(ggen)) by lia.
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      assert (Hnl : ~ thread_live g gen_id) by (intros [_ Hgg]; lia).
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (HartE gen_id cpu_id m), g, [].
        by apply prim_step_hart_dead. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
        as (-> & -> & [(Hlive & _) | (_ & -> & ->)]); [by exfalso|].
      iIntros "_". iMod "Hback" as "_". iModIntro.
      iFrame "Hgauth Hsauth Htie".
      iSplitL "HRauth Hera".
      { iExists R. iFrame "HRauth Hera". iPureIntro. exact Hdom. }
      iSplitL; [|done].
      iApply (wp_dead _ gen_id); [done|]. iExact "Hdead". }
    destruct (g.(gpow)) eqn:Hpw; last first.
    { (* CURRENT BUT POWERED OFF: impossible -- generation [gen_id]'s
         PowerOn has happened ([gen_started]), but the started count reads
         [ggen + 0 = gen_id]. *)
      exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia. }
    assert (Hlive : thread_live g gen_id) by (split; congruence).
    (* LIVE.  Tie the ambient era to the existential via the registry. *)
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Htso & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iDestruct (resv_frag_agree _ cpu_id rr with "Hresv Hfrag") as %Hrr.
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iEval (rewrite tso_interp_at_of) in "Htso".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev))
            (others_resv g.(gresv) cpu_id)
            g.(gimg) g.(glog) (g.(gtv) cpu_id) (avf g)
            with "[] [] [Hri Hmem Hdev] Htso") as (m0 σ0 log0 tv0 r0) "(%Hwit & Hk)".
    { iPureIntro. intros rv Hrv. apply (Hrok cpu_id). by rewrite Hrr. }
    { iPureIntro. apply avf_hart. }
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    rewrite -Hrr in Hwit.
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (HartE gen_id cpu_id m0),
             (GState (<[cpu_id := σ0.(sregs)]> g.(gregs)) σ0.(mem) σ0.(mdev)
                g.(ggen) g.(gpow) (<[cpu_id := r0]> g.(gresv))
                g.(gimg) log0 (<[cpu_id := tv0]> g.(gtv))), [].
      left. exists gen_id, cpu_id, m. split_and!; try reflexivity.
      left. split; [exact Hlive|]. by exists m0, σ0, log0, tv0, r0. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
      as (-> & -> & [(_ & (m2 & σ2 & log2 & tv2 & r2 & Hnode & -> & ->))
                    | (Hnl & _)]);
      last by exfalso.
    (* the hart moved no disk byte: the durable conjunct is FRAMED, at the
       post-state's own image ([RiscvLang.mnode_step_v_disk]) *)
    pose proof (mnode_step_v_disk _ _ _ _ _ _ _ _ _ _ _ _ _ Hnode) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio (mdev σ2))))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (mdev σ2)))
      by (symmetry; exact Hvd).
    rewrite Hrr in Hnode.
    iMod ("Hk" $! m2 σ2 log2 tv2 r2 with "[//]")
      as "[(Hri' & Hmem' & Hdev') [Htso' HWP]]".
    iDestruct ("Hclose" with "Hri'") as "Hgr'".
    iDestruct (tso_interp_hart_wb _ g cpu_id σ2.(sregs) σ2.(mem) σ2.(mdev)
                 r2 log2 tv2 with "Htso'") as "Htso2".
    iMod (resv_frag_update g.(gresv) cpu_id rr r2 with "Hresv Hfrag")
      as "[Hresv Hfrag]".
    iDestruct ("HWP" with "Hfrag") as "HWP".
    iIntros "_ !>".
    iEval (rewrite /disk_fixed_interp Hvd2) in "Htie".
    rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev' Htso2".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview2. }
    (* the mirror was moved to the post-state's map by the frag update;
       [resv_ok] comes from the language's own step invariant *)
    iFrame "Hresv". iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
  Qed.



  (* THE BOUNDARY RULE, derived: at [Loop] the only node is the restart, so
     the caller owes nothing about σ at all and simply picks up the WP of a
     fresh cycle -- at BOTH ticks, since the tick is chosen by the machine.
     This is where the old rule's ∀-over-[tick] now lives; the [tick_clock]
     tail is then ordinary register nodes of the same cycle, not a second
     successor state the caller has to name. *)
  (* The boundary is where a DANGLING reservation is dropped (§3a), so this
     is a frag-form rule: the hart's [resv_frag] comes in at whatever the
     last instruction left and goes out at [None] for the next cycle. *)
  Lemma wp_hart_restart (rr : option resv) :
    gen_cert -∗
    resv_frag cpu_id rr -∗
    ▷ (∀ tick : bool,
         resv_frag cpu_id None -∗
         WP (HartE gen_id cpu_id (riscv_step tick) : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcert Hfrag H". rewrite /LoopE.
    iApply (wp_hart_step_resv _ rr with "Hcert Hfrag").
    iIntros (σ oth img log tv V) "_ %Htv Hsi Htso".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
    iExists (riscv_step false), σ, log, tv, None.
    iSplitR; [iPureIntro; by exists false|].
    iNext. iIntros (m' σ' log' tv' r') "%Hn".
    destruct Hn as (tick & -> & -> & -> & -> & ->).
    iMod "Hback" as "_". iModIntro. iFrame "Hsi".
    (* the boundary touches neither the log nor the view (an instruction
       boundary is not a fence, tso-machine-flip.md §2): the bundle goes
       back untouched. *)
    iSplitL "Htso".
    { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
    iIntros "Hfrag". iApply ("H" with "Hfrag").
  Qed.

End WPExec.

Section WPDev.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* The device-thread analogues, same four-way split.  Their callbacks
     still hand over the same full interp triple as before. *)

  Local Lemma dev_step_prelude (g : gstate)
      (Hbge : gen_id <= g.(ggen)) (Hsge : S gen_id <= start_count g) :
    g.(ggen) = gen_id -> g.(gpow) = true \/ gen_id < g.(ggen).
  Proof.
    intros Heq. destruct (g.(gpow)) eqn:Hpw; [by left|].
    exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia.
  Qed.

  Lemma wp_uart_step :
    gen_cert -∗
    (∀ gr m d, gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ={⊤,∅}=∗
       ▷ (∀ d', ⌜uart_step d d'⌝ ={∅,⊤}=∗
            gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d' ∗
            WP (UartLoop : expr riscv_lang))) -∗
    WP (UartLoop : expr riscv_lang).
  Proof.
    iIntros "#(Hborn & Hstarted & Hrege) H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { assert (Hlt : gen_id < g.(ggen)) by lia.
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (UartLoopE gen_id), g, [].
        right; left. exists gen_id. split_and!; auto.
        right. split; [|done]. intros [_ Hgg]. lia. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct (prim_step_uart_inv _ _ _ _ _ _ Hstep)
        as (-> & -> & -> & [ ([_ Hgg] & _) | (_ & ->) ]); [exfalso; lia|].
      iIntros "_". iMod "Hback" as "_". iModIntro.
      iFrame "Hgauth Hsauth Htie".
      iSplitL "HRauth Hera".
      { iExists R. iFrame "HRauth Hera". iPureIntro. exact Hdom. }
      iSplitL; [|done].
      iApply (wp_dead _ gen_id); [done|]. iExact "Hdead". }
    destruct (g.(gpow)) eqn:Hpw; last first.
    { exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia. }
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Htso & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (UartLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv)
           g.(gimg) g.(glog) g.(gtv)), [].
      right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      eexists. split; [apply UartStepIdle|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_uart_inv _ _ _ _ _ _ Hstep)
      as (-> & -> & -> & [ (Hlive & d' & Hdstep & ->) | (Hnl & ->) ]);
      last by (exfalso; apply Hnl; split; congruence).
    iMod ("Hk" $! d' with "[//]") as "(Hgr' & Hmem' & Hdev' & HWP)".
    (* a UART step moves no disk byte, so the durable conjunct is FRAMED *)
    pose proof (uart_step_v_disk _ _ Hdstep) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio d')))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio d'))
      by (symmetry; exact Hvd).
    iIntros "_ !>".
    iEval (rewrite /disk_fixed_interp Hvd2) in "Htie".
    rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    (* the TSO conjunct is FRAMED: a UART step moves neither the image, the
       flat cache, the log nor any view, so [avf] of the written-back state
       is [avf g] by conversion *)
    iFrame "Hgr' Hmem' Hdev' Htso".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview2. }
    (* the reservation mirror: a device step never touches [gresv], so the
       auth is framed; [resv_ok] is the language's step invariant *)
    iFrame "Hresv". iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
  Qed.

  (* THE ONE RULE THAT HANDS THE IMAGE CONJUNCT OVER (crash.md): a DMA
     completion is the only step in the whole machine that moves [v_disk], so
     the disk thread -- and nobody else -- receives the AMBIENT ERA's image
     auth together with its tie to the device's image, and owes the same shape
     back at the post-state's image.  Stated in the RAW ∃-form rather than as
     [disk_dur_interp], because the callback is per-[dev_state], not per
     [gstate] -- the two are the same resource
     ([disk_dur_interp riscv_eraGS g = disk_img_auth disk_img_name
     (v_disk (dvirtio (gdev g)))]). *)
  Lemma wp_disk_step :
    gen_cert -∗
    (* THE STARTED-GENERATIONS AUTH IS THREADED THROUGH TOO (phase C2b/D1),
       in the same accessor style as the image auth: a DMA completion is the
       one step whose client fupd has to know WHICH generation is current,
       and [state_interp] is the only thing that does.  The pure [n = gen + 1]
       is the live-era arithmetic ([start_count] at [gpow = true]); together
       they let the crash-side arm's [gen_started] be bounded from above. *)
    (* THE TSO BUNDLE IS THREADED THROUGH TOO (tso-machine-flip.md §6
       amendment A6.2).  The disk is an AGENT of the log: a DMA-writing step
       appends its whole write set [W] as ONE authored message, so the four
       ghost steps a hart's store owes ([Wobl_ram]) are owed here as well --
       and they cannot be done by this rule, because the per-byte timestamp
       FRAGMENTS for [W]'s addresses ride inside the CLIENT's own
       [ctx_pointsto]s.  So the authority is handed to the callback exactly
       as the image auth already is, and the callback owes it back at the
       appended log.  The disk's own VIEW half is free: [avf] pins every
       bus-master agent to the top, so [vstep disk_agent (length log') log']
       is the whole move.
       THE WRITE SET COMES OUT OF [disk_step] ITSELF (§6 amendment A6.11),
       so the callback KNOWS which [W] it owes timestamps for -- and an arm
       that writes nothing says [W = ∅], which is what lets four of the six
       arms hand the bundle straight back.  Before A6.11 [W] was a separate
       existential tied only by [W ∪ m = m'], and this rule was unprovable
       downstream: every arm, [DiskStepIdle] included, admitted a non-empty
       [W] of already-correct bytes and hence an unpayable append. *)
    (∀ gr m d n img log V, ⌜n = (gen_id + 1)%nat⌝ -∗
       gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ∗
       disk_img_auth disk_img_name (v_disk (dvirtio d)) ∗
       disk_fixed_auth (v_disk (dvirtio d)) ∗ start_auth n ∗
       tso_interp_of riscv_eraGS img m log V ={⊤,∅}=∗
       ▷ (∀ d' (W : gmap Arch.pa (bv 8)) (log' : list pwmsg),
            ⌜disk_step d m d' W⌝ -∗
            (* [%list]: this file sits in [Z_scope] and the model's imports
               leave [++] resolving to STRING append otherwise *)
            ⌜(W = ∅ /\ log' = log)
             \/ (W <> ∅ /\ log' = (log ++ [PWMsg W disk_agent])%list)⌝
            ={∅,⊤}=∗
            gregs_interp gr ∗ gen_heap_interp (W ∪ m) ∗ dev_interp d' ∗
            disk_img_auth disk_img_name (v_disk (dvirtio d')) ∗
            disk_fixed_auth (v_disk (dvirtio d')) ∗ start_auth n ∗
            tso_interp_of riscv_eraGS img (W ∪ m) log'
              (vstep disk_agent (length log') log' V) ∗
            WP (DiskLoop : expr riscv_lang))) -∗
    WP (DiskLoop : expr riscv_lang).
  Proof.
    iIntros "#(Hborn & Hstarted & Hrege) H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { assert (Hlt : gen_id < g.(ggen)) by lia.
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (DiskLoopE gen_id), g, [].
        right; right; left. exists gen_id. split_and!; auto.
        right. split; [|done]. intros [_ Hgg]. lia. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct (prim_step_disk_inv _ _ _ _ _ _ Hstep)
        as (-> & -> & -> & [ ([_ Hgg] & _) | (_ & ->) ]); [exfalso; lia|].
      iIntros "_". iMod "Hback" as "_". iModIntro.
      iFrame "Hgauth Hsauth Htie".
      iSplitL "HRauth Hera".
      { iExists R. iFrame "HRauth Hera". iPureIntro. exact Hdom. }
      iSplitL; [|done].
      iApply (wp_dead _ gen_id); [done|]. iExact "Hdead". }
    destruct (g.(gpow)) eqn:Hpw; last first.
    { exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia. }
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Htso & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iEval (rewrite /disk_fixed_interp) in "Htie".
    iEval (rewrite tso_interp_at_of) in "Htso".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) (start_count g)
            g.(gimg) g.(glog) (avf g)
            with "[] [$Hgr $Hmem $Hdev Hdauth Htie Hsauth Htso]") as "Hk".
    { iPureIntro. rewrite /start_count Hpw Heq. lia. }
    { iFrame "Htie Hsauth Htso". iExists dmap. iFrame "Hdauth". iPureIntro.
      exact Hdview. }
    iModIntro. iSplitR.
    { iPureIntro. exists [], (DiskLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv)
           g.(gimg) g.(glog) g.(gtv)), [].
      right; right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      (* the idle self-loop appends NOTHING: [W = ∅], log unchanged *)
      exists g.(gdev), ∅, g.(glog). split_and!.
      - apply DiskStepIdle.
      - by left.
      - intros a _. by rewrite left_id_L.
      - by rewrite left_id_L. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_disk_inv _ _ _ _ _ _ Hstep)
      as (-> & -> & -> & [ (Hlive & d' & W & log' & Hdstep & Hlog & _ & ->)
                         | (Hnl & ->) ]);
      last by (exfalso; apply Hnl; split; congruence).
    iMod ("Hk" $! d' W log' with "[//] [//]")
      as "(Hgr' & Hmem' & Hdev' & Hdur' & Htie' & Hsauth' & Htso' & HWP)".
    iDestruct (tso_interp_disk_wb _ g (W ∪ g.(gmem)) d' log' with "Htso'")
      as "Htso2".
    iIntros "_ !>". rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth' Htie' HWP".
    iDestruct "Hdur'" as (dmap') "[Hdauth' %Hdview']".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev' Htso2".
    iSplitL "Hdauth'".
    { iExists dmap'. iFrame "Hdauth'". iPureIntro. exact Hdview'. }
    (* the reservation mirror: a device step never touches [gresv], so the
       auth is framed; [resv_ok] is the language's step invariant *)
    iFrame "Hresv". iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
  Qed.

  Lemma wp_plic_step :
    gen_cert -∗
    (∀ gr m d, gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ={⊤,∅}=∗
       ▷ (∀ gr', ⌜plic_step d gr gr'⌝ ={∅,⊤}=∗
            gregs_interp gr' ∗ gen_heap_interp m ∗ dev_interp d ∗
            WP (PlicLoop : expr riscv_lang))) -∗
    WP (PlicLoop : expr riscv_lang).
  Proof.
    iIntros "#(Hborn & Hstarted & Hrege) H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct (mono_nat_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { assert (Hlt : gen_id < g.(ggen)) by lia.
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (PlicLoopE gen_id), g, [].
        right; right; right; left. exists gen_id. split_and!; auto.
        right. split; [|done]. intros [_ Hgg]. lia. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct (prim_step_plic_inv _ _ _ _ _ _ Hstep)
        as (-> & -> & -> & [ ([_ Hgg] & _) | (_ & ->) ]); [exfalso; lia|].
      iIntros "_". iMod "Hback" as "_". iModIntro.
      iFrame "Hgauth Hsauth Htie".
      iSplitL "HRauth Hera".
      { iExists R. iFrame "HRauth Hera". iPureIntro. exact Hdom. }
      iSplitL; [|done].
      iApply (wp_dead _ gen_id); [done|]. iExact "Hdead". }
    destruct (g.(gpow)) eqn:Hpw; last first.
    { exfalso. rewrite /start_count Hpw Heq Nat.add_0_r in Hsge. lia. }
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Htso & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (PlicLoopE gen_id),
        (GState (<[0%fin := register_set sig_seip
                    (bool_to_bit (dev_seip g.(gdev) (fin_to_nat (0%fin : CPU))))
                    (g.(gregs) 0%fin)]> g.(gregs)) g.(gmem) g.(gdev)
           g.(ggen) g.(gpow) g.(gresv) g.(gimg) g.(glog) g.(gtv)), [].
      right; right; right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      eexists. split; [apply (PlicStepWire _ _ 0%fin)|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_plic_inv _ _ _ _ _ _ Hstep)
      as (-> & -> & -> & [ (Hlive & gr' & Hdstep & ->) | (Hnl & ->) ]);
      last by (exfalso; apply Hnl; split; congruence).
    iMod ("Hk" $! gr' with "[//]") as "(Hgr' & Hmem' & Hdev' & HWP)".
    iIntros "_ !>". rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    (* a PLIC step moves only registers: the image conjunct, the FS tie and
       the TSO conjunct are all FRAMED (the device state is literally
       unchanged, and so are image/cache/log/views) *)
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev' Htso".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
    (* the reservation mirror: a device step never touches [gresv], so the
       auth is framed; [resv_ok] is the language's step invariant *)
    iFrame "Hresv". iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
  Qed.

End WPDev.

(* THE POWER ARMS HAVE NO LIFTING RULE HERE, and the ERA WIPE
   (tso-machine-flip.md §2's last bullet: [gimg := the reset memory],
   [glog := []], [gtv := λ_, 0], [gmem := gimg]) LANDS WITH ADEQUACY
   (§6 amendment A6.3, §7 step 6): a PowerOn allocates a FRESH era, so its
   [tso_interp_at] is minted rather than updated, beside the other
   initial-state ghosts.  Nothing in this file is missing on its account. *)

(* Now that the Lang/Iris/Exec sections (which must share stdpp's bv_countable   *)
(* with RiscvModelBytes for [mstate.mem]) are defined, bring in the model's      *)
(* Base/Values/TypeCasts for the remaining proof sections.                        *)
Require Import SailStdpp.Base.
(* Re-import the model AFTER Base so the model's names (read_kind/Read_plain/…)  *)
(* win over SailStdpp's homonyms for the sections below — matching the original  *)
(* per-file import order (model imported last).  mstate.mem's type is already    *)
(* fixed (bv_countable) from the Lang section above, so this does not retype it.  *)
Require Import Riscv.rv64d_types.
Require Import TsoCtx.

(* ===== RiscvModelExecClose ===== *)
(* ====================================================================== *)
(* RiscvModelExecClose.v                                                   *)
(*                                                                         *)
(* Close the ADD weakest-precondition via the deterministic-step route:    *)
(* prove [exec (riscv_step false) s = Some (tt, s_final)] and apply         *)
(* [wp_exec_step]                                                            *)
(* (no Hcycle, no per-instruction determinism).                            *)
(* ====================================================================== *)




Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. run_to_exec: a proven [run]-fact becomes an [exec]-fact, given that  *)
(*    exec makes progress (does not hit Choose/fail).  Free corollary of   *)
(*    exec_run_det.                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma run_to_exec {X} (m : M X) (s : mstate) (x : X) (s' : mstate) :
  run m s x s' -> exec m s <> None -> exec m s = Some (x, s').
Proof.
  intros Hrun Hne.
  destruct (exec m s) as [[x'' s'']|] eqn:He; [|exfalso; by apply Hne].
  destruct (exec_run_det _ _ _ _ He) as [_ Huniq].
  destruct (Huniq _ _ Hrun) as [-> ->]. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. exec_bind: the option-monad functional equation for exec over bind.  *)
(* ---------------------------------------------------------------------- *)

Lemma bind_Ret {X Y} (y : X) (f : X -> M Y) :
  Defs.bind (Interface.Ret y) f = f y.
Proof. reflexivity. Qed.

Lemma bind_Next {X Y T} (oc : Interface.outcome (fun _ => exception) T)
      (k : T -> M X) (f : X -> M Y) :
  Defs.bind (Interface.Next oc k) f = Interface.Next oc (fun z => Defs.bind (k z) f).
Proof. reflexivity. Qed.

Lemma exec_bind {X Y} (m : M X) (f : X -> M Y) :
  forall s, exec (Defs.bind m f) s
          = match exec m s with
            | Some (x, s1) => exec (f x) s1
            | None => None
            end.
Proof.
  induction m as [y | T oc k IH]; intros s.
  - rewrite bind_Ret. reflexivity.
  - rewrite bind_Next. destruct oc; cbn [exec];
      try (apply IH); try reflexivity.
    + (* MemRead *) destruct (dev_addr _).
      * destruct (dev_read _ _ _) as [[w d']|]; [apply IH | reflexivity].
      * destruct (read_bytes _ _ _) as [w|]; [apply IH | reflexivity].
    + (* MemWrite *) destruct (dev_addr _).
      * destruct (dev_write _ _ _ _) as [d'|]; [apply IH | reflexivity].
      * apply IH.
Qed.

Lemma exec_bind0 {Y} (m : M unit) (n : M Y) :
  forall s, exec (Defs.bind0 m n) s
          = match exec m s with Some (_, s1) => exec n s1 | None => None end.
Proof. intros s. unfold Defs.bind0. rewrite exec_bind. by destruct (exec m s) as [[??]|]. Qed.

Lemma exec_returnm {X} (x : X) s : exec (Defs.returnm x) s = Some (x, s).
Proof. reflexivity. Qed.

(* ===== RiscvModelWPclose ===== *)
(* ====================================================================== *)
(* RiscvModelWPclose.v                                                     *)
(*                                                                         *)
(* Close exec_riscv_step_ADD (the try_step wrapper around the proven       *)
(* exec_hart_active reduction, done FUNCTIONALLY via exec_bind) and        *)
(* wp_add_real_closed (via wp_exec_step) -- no Hcycle, no per-instruction  *)
(* determinism.                                                            *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Rewrite-friendly exec-bind: collapse the [match exec m s with ...] when *)
(* the head's exec result is known.                                        *)
(* ---------------------------------------------------------------------- *)

Lemma exec_bind_Some {X Y} (m : M X) (f : X -> M Y) s v st :
  exec m s = Some (v, st) -> exec (Defs.bind m f) s = exec (f v) st.
Proof. intros H. rewrite exec_bind H. reflexivity. Qed.

Lemma exec_bind0_Some {Y} (m : M unit) (n : M Y) s u st :
  exec m s = Some (u, st) -> exec (Defs.bind0 m n) s = exec n st.
Proof. intros H. rewrite exec_bind0 H. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The tick-branch witness for [wp_exec_step]: [riscv_step true] runs the  *)
(* same [try_step] and then [tick_clock] from the no-tick successor, so a  *)
(* caller composes its no-tick witness with a [tick_clock] exec fact.      *)
(* ---------------------------------------------------------------------- *)

Lemma exec_riscv_step_tick (s s' s'' : mstate) :
  exec (riscv_step false) s = Some (tt, s') ->
  exec (tick_clock tt) s' = Some (tt, s'') ->
  exec (riscv_step true) s = Some (tt, s'').
Proof.
  intros H1 H2.
  unfold riscv_step in H1 |- *.
  rewrite exec_bind in H1. rewrite exec_bind.
  destruct (exec (try_step 0 false) s) as [[b s1]|]; [|discriminate].
  cbn beta iota in H1 |- *.
  rewrite exec_returnm in H1.
  inversion H1; subst. exact H2.
Qed.

(* exec-leaves (functional twins of run_read_reg / run_write_reg). *)
Lemma exec_read_reg (r : register) s :
  exec (Defs.read_reg r : M _) s = Some (register_lookup r s.(sregs), s).
Proof. reflexivity. Qed.

Lemma exec_write_reg (r : register) (v : type_of_register r) s :
  exec (Defs.write_reg r v : M _) s = Some (tt, set_reg s r v).
Proof. reflexivity. Qed.

(* tick_pc copies nextPC -> PC; value is pc_write_callback _ = tt. *)
Lemma exec_tick_pc s :
  exec (tick_pc tt) s = Some (tt, set_reg s PC (register_lookup nextPC s.(sregs))).
Proof.
  unfold tick_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg PC _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC _)).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* exec_riscv_step_ADD: thread the try_step wrapper around the hart-active *)
(* reduction (Hha), FUNCTIONALLY via exec_bind.  s_final is explicit.      *)
(* ---------------------------------------------------------------------- *)

Section StepHartActive.
  Context (s s_exec : mstate) (retval : mword 32) (b : bool).

  (* [should_inc] at whatever privilege [s] happens to be in -- the wrapper
     reads [cur_privilege] only to feed [should_inc], so we never need to pin
     it to [Machine]. *)
  Hypothesis Hsi   :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.

  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_hart_active : exec (riscv_step false) s = Some (tt, s_final).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_final))).
    { reflexivity. }
    (* now prove exec (try_step 0 false) s = Some (false, s_final) *)
    unfold try_step.
    cbn [ext_pre_step_hook].
    (* read cur_privilege -- kept SYMBOLIC (whatever privilege [s] is in) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta.
    (* should_inc_minstret <that privilege> -> b *)
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    (* write minstret_increment b >> read hart_state *)
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    (* run_hart_active 0 -> Step_Execute (RETIRE_SUCCESS, _), s_exec *)
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    (* try_step TAIL: BODY = bind (bind0 ARM (read hart_state)) (fun w10 => MATCH10). *)
    (* Step A: exec (bind0 ARM (read hart_state)) s_exec = Some (HART_ACTIVE tt, s_exec). *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ (* exec ARM s_exec = Some(tt, s_exec) *)
            erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        (* exec (read hart_state) s_exec = Some(HART_ACTIVE tt, s_exec) *)
        apply exec_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    (* REST10 = bind0 (tick_pc) (bind (and_boolM (returnM true)(read mi)) (fun w12 => TAIL2)) *)
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    change (get_config_rvfi tt) with false.
    replace (register_lookup minstret_increment
               (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs))
      with b.
    2:{ rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - (* b = true: minstret += 1 *)
      erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some.
              2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - (* b = false *)
      erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity.
  Qed.

End StepHartActive.

Section StepADD.
  Context (s s_exec : mstate) (w : mword 32) (b : bool) (pc : mword 64).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hsi   : exec (should_inc_minstret Machine) s = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.
  Hypothesis Hrvfi : get_config_rvfi tt = false.

  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.


End StepADD.

(* [should_inc_minstret] is TOTAL: it only reads mcountinhibit + minstretcfg
   and combines them with [and_boolM], so at any state / privilege its [exec]
   yields [Some (_, s)] for SOME boolean -- we never need to know which. *)
Lemma exec_should_inc_minstret_Some (priv : Privilege) s :
  ∃ b : bool, exec (should_inc_minstret priv) s = Some (b, s).
Proof.
  unfold should_inc_minstret, Defs.and_boolM.
  (* outer bind on [read mcountinhibit >>= returnM _] *)
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind_Some.
      2:{ apply (exec_read_reg mcountinhibit s). }
      apply exec_returnm. }
  cbn beta.
  (* [if <mcountinhibit bit> then (read minstretcfg >>= returnM _) else returnM false] *)
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_bind_Some.
    2:{ apply (exec_read_reg minstretcfg s). }
    eexists. apply exec_returnm.
  - eexists. apply exec_returnm.
Qed.

