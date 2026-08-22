(* RiscvExec.v -- the run/exec interpreters, determinism bridge, wp_exec_step. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto HartBlock.
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
(* ---------------------------------------------------------------------- *)

Corollary hart_block_exec (tick : bool) (s s' s'' : mstate) :
  exec (riscv_step tick) s = Some (tt, s'') ->
  mblock (riscv_step tick, s) (Interface.Ret tt, s') ->
  s' = s''.
Proof.
  intros He Hb. destruct (exec_run_det _ _ _ _ He) as [_ Huniq].
  by destruct (Huniq _ _ (hart_block_run _ _ _ Hb)) as [_ ->].
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

Section WPExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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
  Lemma wp_hart_step (m : M unit) :
    (forall oth σ r m' σ' r', mnode_step oth σ r m m' σ' r' -> r' = r) ->
    gen_cert -∗
    (∀ σ oth r, mstate_interp σ ={⊤,∅}=∗
       ∃ m0 σ0 r0, ⌜mnode_step oth σ r m m0 σ0 r0⌝ ∗
          ▷ (∀ m' σ' r', ⌜mnode_step oth σ r m m' σ' r'⌝ ={∅,⊤}=∗
               mstate_interp σ' ∗
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev))
            (others_resv g.(gresv) cpu_id) (g.(gresv) cpu_id)
            with "[Hri Hmem Hdev]") as (m0 σ0 r0) "(%Hwit & Hk)".
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (HartE gen_id cpu_id m0),
             (GState (<[cpu_id := σ0.(sregs)]> g.(gregs)) σ0.(mem) σ0.(mdev)
                g.(ggen) g.(gpow) (<[cpu_id := r0]> g.(gresv))), [].
      left. exists gen_id, cpu_id, m. split_and!; try reflexivity.
      left. split; [exact Hlive|]. by exists m0, σ0, r0. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
      as (-> & -> & [(_ & (m2 & σ2 & r2 & Hnode & -> & ->)) | (Hnl & _)]);
      last by exfalso.
    (* the hart moved no disk byte: the durable conjunct is FRAMED, at the
       post-state's own image ([RiscvLang.mnode_step_v_disk]) *)
    pose proof (mnode_step_v_disk _ _ _ _ _ _ _ Hnode) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio (mdev σ2))))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (mdev σ2)))
      by (symmetry; exact Hvd).
    iMod ("Hk" $! m2 σ2 r2 with "[//]") as "[(Hri' & Hmem' & Hdev') HWP]".
    iDestruct ("Hclose" with "Hri'") as "Hgr'".
    iIntros "_ !>".
    iEval (rewrite /disk_fixed_interp Hvd2) in "Htie".
    rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview2. }
    (* the mirror: this rule's arms preserve the reservation, so the auth's
       map is unchanged; [resv_ok] comes from the language's own step
       invariant. *)
    iSplitL "Hresv".
    { iEval (rewrite /resv_auth_at) in "Hresv".
      rewrite /resv_auth_at
        (resv_map_insert_id g.(gresv) cpu_id r2
           (eq_sym (Hpres _ _ _ _ _ _ Hnode))).
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
    (∀ σ oth, ⌜forall rv, rr = Some rv -> rv ⊆ σ.(mem)⌝ -∗
       mstate_interp σ ={⊤,∅}=∗
       ∃ m0 σ0 r0, ⌜mnode_step oth σ rr m m0 σ0 r0⌝ ∗
          ▷ (∀ m' σ' r', ⌜mnode_step oth σ rr m m' σ' r'⌝ ={∅,⊤}=∗
               mstate_interp σ' ∗
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iDestruct (resv_frag_agree _ cpu_id rr with "Hresv Hfrag") as %Hrr.
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev))
            (others_resv g.(gresv) cpu_id)
            with "[] [Hri Hmem Hdev]") as (m0 σ0 r0) "(%Hwit & Hk)".
    { iPureIntro. intros rv Hrv. apply (Hrok cpu_id). by rewrite Hrr. }
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    rewrite -Hrr in Hwit.
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (HartE gen_id cpu_id m0),
             (GState (<[cpu_id := σ0.(sregs)]> g.(gregs)) σ0.(mem) σ0.(mdev)
                g.(ggen) g.(gpow) (<[cpu_id := r0]> g.(gresv))), [].
      left. exists gen_id, cpu_id, m. split_and!; try reflexivity.
      left. split; [exact Hlive|]. by exists m0, σ0, r0. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_hart_inv _ _ _ _ _ _ _ _ Hstep)
      as (-> & -> & [(_ & (m2 & σ2 & r2 & Hnode & -> & ->)) | (Hnl & _)]);
      last by exfalso.
    (* the hart moved no disk byte: the durable conjunct is FRAMED, at the
       post-state's own image ([RiscvLang.mnode_step_v_disk]) *)
    pose proof (mnode_step_v_disk _ _ _ _ _ _ _ Hnode) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio (mdev σ2))))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (mdev σ2)))
      by (symmetry; exact Hvd).
    rewrite Hrr in Hnode.
    iMod ("Hk" $! m2 σ2 r2 with "[//]") as "[(Hri' & Hmem' & Hdev') HWP]".
    iDestruct ("Hclose" with "Hri'") as "Hgr'".
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
    iFrame "Hgr' Hmem' Hdev'".
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
    iIntros (σ oth) "_ Hsi".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
    iExists (riscv_step false), σ, None.
    iSplitR; [iPureIntro; by exists false|].
    iNext. iIntros (m' σ' r') "%Hn".
    destruct Hn as (tick & -> & -> & ->).
    iMod "Hback" as "_". iModIntro. iFrame "Hsi". iIntros "Hfrag".
    iApply ("H" with "Hfrag").
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (UartLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv)), [].
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
    iFrame "Hgr' Hmem' Hdev'".
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
    (∀ gr m d n, ⌜n = (gen_id + 1)%nat⌝ -∗
       gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ∗
       disk_img_auth disk_img_name (v_disk (dvirtio d)) ∗
       disk_fixed_auth (v_disk (dvirtio d)) ∗ start_auth n ={⊤,∅}=∗
       ▷ (∀ d' m', ⌜disk_step d m d' m'⌝ ={∅,⊤}=∗
            gregs_interp gr ∗ gen_heap_interp m' ∗ dev_interp d' ∗
            disk_img_auth disk_img_name (v_disk (dvirtio d')) ∗
            disk_fixed_auth (v_disk (dvirtio d')) ∗ start_auth n ∗
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iEval (rewrite /disk_fixed_interp) in "Htie".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) (start_count g)
            with "[] [$Hgr $Hmem $Hdev Hdauth Htie Hsauth]") as "Hk".
    { iPureIntro. rewrite /start_count Hpw Heq. lia. }
    { iFrame "Htie Hsauth". iExists dmap. iFrame "Hdauth". iPureIntro.
      exact Hdview. }
    iModIntro. iSplitR.
    { iPureIntro. exists [], (DiskLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv)), [].
      right; right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      do 2 eexists. split; [apply DiskStepIdle|]. split; [done|].
      rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct (prim_step_disk_inv _ _ _ _ _ _ Hstep)
      as (-> & -> & -> & [ (Hlive & d' & m' & Hdstep & _ & ->) | (Hnl & ->) ]);
      last by (exfalso; apply Hnl; split; congruence).
    iMod ("Hk" $! d' m' with "[//]")
      as "(Hgr' & Hmem' & Hdev' & Hdur' & Htie' & Hsauth' & HWP)".
    iIntros "_ !>". rewrite /state_interp /power_interp /disk_fixed_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth' Htie' HWP".
    iDestruct "Hdur'" as (dmap') "[Hdauth' %Hdview']".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur & Hresv & %Hrok)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (PlicLoopE gen_id),
        (GState (<[0%fin := register_set sig_seip
                    (bool_to_bit (dev_seip g.(gdev) (fin_to_nat (0%fin : CPU))))
                    (g.(gregs) 0%fin)]> g.(gregs)) g.(gmem) g.(gdev)
           g.(ggen) g.(gpow) g.(gresv)), [].
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
    (* a PLIC step moves only registers: the image conjunct and the FS tie
       are both FRAMED (the device state is literally unchanged) *)
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
    iSplitL "Hdauth".
    { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
    (* the reservation mirror: a device step never touches [gresv], so the
       auth is framed; [resv_ok] is the language's step invariant *)
    iFrame "Hresv". iPureIntro.
    exact (prim_step_resv_ok _ _ _ _ _ _ Hstep Hrok).
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

