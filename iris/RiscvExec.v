(* RiscvExec.v -- the run/exec interpreters, determinism bridge, wp_exec_step. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
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
(* 3. The reusable WP rule for deterministic ops.                          *)
(* ---------------------------------------------------------------------- *)

Section WPExec.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* The single per-hart framing point: [wp_lift_step] hands us the GLOBAL
     [state_interp] (all harts' register bridges + shared memory); we focus the
     ambient hart [cpu_id]'s bridge via [gregs_interp_acc], run one step against
     that hart's [mstate] view, and restore the global bridge afterwards.  Every
     leaf WP is written in terms of the single-hart [mstate_interp] and never
     sees [gregs]. *)
  Lemma wp_exec_step Φ :
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ σ' σ'', ⌜exec (riscv_step false) σ = Some (tt, σ')⌝ ∗
                 ⌜exec (riscv_step true)  σ = Some (tt, σ'')⌝ ∗
          ▷ (∀ tick : bool, |={∅,⊤}=> mstate_interp (if tick then σ'' else σ') ∗
                            WP (Loop : expr riscv_lang) {{ Φ }}))
    ⊢ WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "[Hgr [Hmem Hdev]]".
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev)) with "[Hri Hmem Hdev]")
      as (σ' σ'') "(%Hexecf & %Hexect & Hk)".
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    pose proof (exec_run_det _ _ _ _ Hexecf) as [Hrunf Huniqf].
    pose proof (exec_run_det _ _ _ _ Hexect) as [Hrunt Huniqt].
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (LoopE cpu_id),
             (GState (<[cpu_id := σ'.(sregs)]> g.(gregs)) σ'.(mem) σ'.(mdev)), [].
      left.
      exists cpu_id. split; [done|]. split; [done|]. split; [done|]. split; [done|].
      exists false, tt, σ'. split; [exact Hrunf|done]. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as [(cpu2 & Hcpu2 & -> & _ & -> & tick2 & u2 & σ2' & Hrun2 & ->)
                      |(Hcontra & _)]; last discriminate Hcontra.
    injection Hcpu2 as <-.
    iSpecialize ("Hk" $! tick2).
    destruct tick2;
      [ destruct (Huniqt _ _ Hrun2) as [_ ->]
      | destruct (Huniqf _ _ Hrun2) as [_ ->] ];
      iMod "Hk" as "[(Hri' & Hmem' & Hdev') HWP]";
      iDestruct ("Hclose" with "Hri'") as "Hgr'";
      iIntros "_ !>"; rewrite /state_interp /=; iFrame "Hgr' Hmem' Hdev' HWP".
  Qed.

End WPExec.

Section WPDev.
  Context `{!riscvGS Σ}.

  (* The device-thread analogue of [wp_exec_step]: one step of the [DevLoop]
     execution context.  The device is ALWAYS reducible (the wire step exists
     for any hart), so the user only proves PRESERVATION: for EVERY possible
     device transition -- a byte leaving the tx FIFO, a byte arriving from
     the outside world, the virtio disk completing a queued request, the PLIC
     gateway latching a device's interrupt level, or the PLIC driving a
     hart's [sig_seip] wire -- re-establish the register bridges (the wire
     step writes a hart's [sig_seip] register, which needs its ghost-map
     fragment unless the written value is unchanged), the byte memory and the
     device interpretation.

     The BYTE MEMORY is handed over rather than framed, because the disk is a
     bus master: [DevStepDisk] returns a memory that differs from the one it
     was given (RiscvLang §3c).  A client therefore has to own every byte the
     DMA writes -- which is exactly what the device invariant's DMA lease
     (WpVirtio.v) is for.  Every other device transition returns the memory
     unchanged, so those cases still frame it. *)
  Lemma wp_dev_step Φ :
    (∀ gr m d, gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ={⊤,∅}=∗
       ▷ (∀ d' m' gr', ⌜dev_step d m gr d' m' gr'⌝ ={∅,⊤}=∗
            gregs_interp gr' ∗ gen_heap_interp m' ∗ dev_interp d' ∗
            WP (DevLoop : expr riscv_lang) {{ Φ }}))
    ⊢ WP (DevLoop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "[Hgr [Hmem Hdev]]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. do 4 eexists. right.
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      do 3 eexists. split; [apply (DevStepWire _ _ _ 0%fin) | reflexivity]. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as [(cpu2 & Hcontra & _)
                      |(_ & -> & _ & -> & d' & m' & gr' & Hdstep & ->)];
      first discriminate Hcontra.
    iMod ("Hk" $! d' m' gr' with "[//]") as "(Hgr' & Hmem' & Hdev' & HWP)".
    iIntros "_ !>". rewrite /state_interp /=. iFrame "Hgr' Hmem' Hdev' HWP".
  Qed.

End WPDev.

(* Now that the Lang/Iris/Exec sections (which must share stdpp's bv_countable   *)
(* with RiscvModelBytes for [mstate.mem]) are defined, bring in the model's      *)
(* Base/Values/TypeCasts for the remaining proof sections.                        *)
Require Import SailStdpp.Base.
(* Re-import the model AFTER Base so the model's names (read_kind/Read_plain/…)  *)
(* win over SailStdpp's homonyms for the sections below — matching the original  *)
(* per-file import order (model imported last).  mstate.mem's type is already    *)
(* fixed (bv_countable) from the Lang section above, so this does not retype it.  *)
Require Import Riscv.rv64d_types Riscv.rv64d.

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
    2:{ unfold set_reg; cbn [sregs].
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

