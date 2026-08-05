(* RiscvExec.v -- the run/exec interpreters, determinism bridge, wp_exec_step. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
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

(* the generation of a generation-indexed thread expression (the power
   thread has none) *)
Definition thread_gen (e : mexpr) : option nat :=
  match e with
  | LoopE gen _ => Some gen
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
  Lemma wp_dead (e : mexpr) (gen : nat) (Φ : mval -> iProp Σ) :
    thread_gen e = Some gen ->
    gen_dead gen ⊢ WP (e : expr riscv_lang) {{ Φ }}.
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
      - exists [], (LoopE gen cpu), g, [].
        left. exists gen, cpu. split_and!; auto.
      - exists [], (UartLoopE gen), g, [].
        right; left. exists gen. split_and!; auto.
      - exists [], (DiskLoopE gen), g, [].
        right; right; left. exists gen. split_and!; auto.
      - exists [], (PlicLoopE gen), g, [].
        right; right; right; left. exists gen. split_and!; auto. }
    iIntros (e2 g2 efs Hstep) "!>".
    (* only the corpse arm is enabled *)
    assert (e2 = e /\ g2 = g /\ efs = []) as (-> & -> & ->).
    { destruct e; simplify_eq/=;
        destruct Hstep as
          [ (gen2 & cpu2 & Heq & -> & _ & -> & [ (Hlive & _) | (_ & ->) ])
          | [ (gen2 & Heq & -> & _ & -> & [ (Hlive & _) | (_ & ->) ])
          | [ (gen2 & Heq & -> & _ & -> & [ (Hlive & _) | (_ & ->) ])
          | [ (gen2 & Heq & -> & _ & -> & [ (Hlive & _) | (_ & ->) ])
          | (Heq & _) ] ] ] ];
        simplify_eq/=; try done;
        exfalso; apply Hnl; exact Hlive. }
    iIntros "_". iMod "Hback" as "_". iModIntro.
    iFrame "Hgauth Hsi". iSplitL; [|done].
    iApply "IH".
  Qed.
End WPDead.

Section WPExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The single per-hart framing point, now FOUR-WAY (crash.md): the rule
     takes the thread's [gen_cert] and cases on the current [(ggen, gpow)].
     LIVE (power on, generation current): the registry element ties the
     ambient era to [state_interp]'s existential and the pre-crash proof
     runs unchanged -- the caller's callback still sees exactly
     [mstate_interp].  DEAD (generation passed): tail into [wp_dead].
     Current-but-off: refuted by the STARTED certificate (the started
     count would have to be both [gen_id] and [> gen_id]).  Unborn:
     refuted by the birth certificate. *)
  Lemma wp_exec_step Φ :
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ σ' σ'', ⌜exec (riscv_step false) σ = Some (tt, σ')⌝ ∗
                 ⌜exec (riscv_step true)  σ = Some (tt, σ'')⌝ ∗
          ▷ (∀ tick : bool, |={∅,⊤}=> mstate_interp (if tick then σ'' else σ') ∗
                            WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
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
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro. exists [], (LoopE gen_id cpu_id), g, [].
        left. exists gen_id, cpu_id. split_and!; auto.
        right. split; [|done]. intros [_ Hgg]. lia. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct Hstep as
        [ (gen2 & cpu2 & Hcpu2 & -> & _ & -> &
            [ ([_ Hgg] & _) | (_ & ->) ])
        | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
        [ injection Hcpu2 as <- <-; exfalso; lia
        | injection Hcpu2 as <- <-
        | discriminate Hc | discriminate Hc | discriminate Hc | discriminate Hc ].
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
    (* LIVE.  Tie the ambient era to the existential via the registry. *)
    iDestruct "Hera" as (E) "(%HRE & Hera)".
    iDestruct (ghost_map_lookup with "HRauth Hrege") as %HRgen.
    assert (E = riscv_eraGS) as ->.
    { rewrite Heq in HRE. congruence. }
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iMod ("H" $! (MState (g.(gregs) cpu_id) g.(gmem) g.(gdev)) with "[Hri Hmem Hdev]")
      as (σ' σ'') "(%Hexecf & %Hexect & Hk)".
    { rewrite /mstate_interp /=. iFrame "Hri Hmem Hdev". }
    pose proof (exec_run_det _ _ _ _ Hexecf) as [Hrunf Huniqf].
    pose proof (exec_run_det _ _ _ _ Hexect) as [Hrunt Huniqt].
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (LoopE gen_id cpu_id),
             (GState (<[cpu_id := σ'.(sregs)]> g.(gregs)) σ'.(mem) σ'.(mdev)
                g.(ggen) g.(gpow)), [].
      left.
      exists gen_id, cpu_id. split_and!; auto.
      left. split; [split; congruence|].
      exists false, tt, σ'. split; [exact Hrunf|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen2 & cpu2 & Hcpu2 & -> & _ & -> &
          [ (Hlive & tick2 & u2 & σ2' & Hrun2 & ->) | (Hnl & ->) ])
      | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
      [ injection Hcpu2 as <- <-
      | injection Hcpu2 as <- <-; exfalso; apply Hnl; split; congruence
      | discriminate Hc | discriminate Hc | discriminate Hc | discriminate Hc ].
    (* the hart moved no disk byte: the durable conjunct is FRAMED, at the
       post-state's own image ([RiscvLang.run_v_disk]) *)
    pose proof (run_v_disk _ _ _ _ Hrun2) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio (mdev σ2'))))
      by (rewrite Hvd; exact Hdview).
    (* the FS tie, restated at the POST state's image.  Stated here, while
       [σ2'] still has a name: the [destruct tick2] below substitutes it away,
       so a tactic after that point cannot spell the post state. *)
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (mdev σ2')))
      by (symmetry; exact Hvd).
    iSpecialize ("Hk" $! tick2).
    destruct tick2;
      [ destruct (Huniqt _ _ Hrun2) as [_ ->]
      | destruct (Huniqf _ _ Hrun2) as [_ ->] ];
      iMod "Hk" as "[(Hri' & Hmem' & Hdev') HWP]";
      iDestruct ("Hclose" with "Hri'") as "Hgr'";
      iIntros "_ !>";
      iEval (rewrite /fs_tie_interp Hvd2) in "Htie";
      rewrite /state_interp /power_interp /fs_tie_interp
        /era_interp /disk_dur_interp /disk_img_auth /=;
      iFrame "Hgauth Hsauth Htie HWP";
      iExists R; iFrame "HRauth";
      (iSplitR; [iPureIntro; exact Hdom|]);
      rewrite Hpw; iExists riscv_eraGS;
      (iSplitR; [iPureIntro; exact HRE|]);
      iFrame "Hgr' Hmem' Hdev'";
      iExists dmap; iFrame "Hdauth"; iPureIntro; exact Hdview2.
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

  Lemma wp_uart_step Φ :
    gen_cert -∗
    (∀ gr m d, gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ={⊤,∅}=∗
       ▷ (∀ d', ⌜uart_step d d'⌝ ={∅,⊤}=∗
            gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d' ∗
            WP (UartLoop : expr riscv_lang) {{ Φ }})) -∗
    WP (UartLoop : expr riscv_lang) {{ Φ }}.
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
      destruct Hstep as
        [ (gen2 & cpu2 & Hc & _)
        | [ (gen2 & Hu & -> & _ & -> & [ ([_ Hgg] & _) | (_ & ->) ])
        | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
        [ discriminate Hc
        | injection Hu as <-; exfalso; lia
        | injection Hu as <-
        | discriminate Hc | discriminate Hc | discriminate Hc ].
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (UartLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow)), [].
      right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      eexists. split; [apply UartStepIdle|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen2 & cpu2 & Hc & _)
      | [ (gen2 & Hu & -> & _ & -> & [ (Hlive & d' & Hdstep & ->) | (Hnl & ->) ])
      | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
      [ discriminate Hc
      | injection Hu as <-
      | injection Hu as <-; exfalso; apply Hnl; split; congruence
      | discriminate Hc | discriminate Hc | discriminate Hc ].
    iMod ("Hk" $! d' with "[//]") as "(Hgr' & Hmem' & Hdev' & HWP)".
    (* a UART step moves no disk byte, so the durable conjunct is FRAMED *)
    pose proof (uart_step_v_disk _ _ Hdstep) as Hvd.
    assert (Hdview2 : disk_view dmap (v_disk (dvirtio d')))
      by (rewrite Hvd; exact Hdview).
    assert (Hvd2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio d'))
      by (symmetry; exact Hvd).
    iIntros "_ !>".
    iEval (rewrite /fs_tie_interp Hvd2) in "Htie".
    rewrite /state_interp /power_interp /fs_tie_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
    iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview2.
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
  Lemma wp_disk_step Φ :
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
       disk_tie (v_disk (dvirtio d)) ∗ start_auth n ={⊤,∅}=∗
       ▷ (∀ d' m', ⌜disk_step d m d' m'⌝ ={∅,⊤}=∗
            gregs_interp gr ∗ gen_heap_interp m' ∗ dev_interp d' ∗
            disk_img_auth disk_img_name (v_disk (dvirtio d')) ∗
            disk_tie (v_disk (dvirtio d')) ∗ start_auth n ∗
            WP (DiskLoop : expr riscv_lang) {{ Φ }})) -∗
    WP (DiskLoop : expr riscv_lang) {{ Φ }}.
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
      destruct Hstep as
        [ (gen2 & cpu2 & Hc & _)
        | [ (gen2 & Hc & _)
        | [ (gen2 & Hu & -> & _ & -> & [ ([_ Hgg] & _) | (_ & ->) ])
        | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
        [ discriminate Hc | discriminate Hc
        | injection Hu as <-; exfalso; lia
        | injection Hu as <-
        | discriminate Hc | discriminate Hc ].
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) (start_count g)
            with "[] [$Hgr $Hmem $Hdev Hdauth Htie Hsauth]") as "Hk".
    { iPureIntro. rewrite /start_count Hpw Heq. lia. }
    { iFrame "Htie Hsauth". iExists dmap. iFrame "Hdauth". iPureIntro.
      exact Hdview. }
    iModIntro. iSplitR.
    { iPureIntro. exists [], (DiskLoopE gen_id),
        (GState g.(gregs) g.(gmem) g.(gdev) g.(ggen) g.(gpow)), [].
      right; right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      do 2 eexists. split; [apply DiskStepIdle|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen2 & cpu2 & Hc & _)
      | [ (gen2 & Hc & _)
      | [ (gen2 & Hu & -> & _ & -> & [ (Hlive & d' & m' & Hdstep & ->) | (Hnl & ->) ])
      | [ (gen2 & Hc & _) | (Hc & _) ] ] ] ];
      [ discriminate Hc | discriminate Hc
      | injection Hu as <-
      | injection Hu as <-; exfalso; apply Hnl; split; congruence
      | discriminate Hc | discriminate Hc ].
    iMod ("Hk" $! d' m' with "[//]")
      as "(Hgr' & Hmem' & Hdev' & Hdur' & Htie' & Hsauth' & HWP)".
    iIntros "_ !>". rewrite /state_interp /power_interp /fs_tie_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth' Htie' HWP".
    iDestruct "Hdur'" as (dmap') "[Hdauth' %Hdview']".
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
    iExists dmap'. iFrame "Hdauth'". iPureIntro. exact Hdview'.
  Qed.

  Lemma wp_plic_step Φ :
    gen_cert -∗
    (∀ gr m d, gregs_interp gr ∗ gen_heap_interp m ∗ dev_interp d ={⊤,∅}=∗
       ▷ (∀ gr', ⌜plic_step d gr gr'⌝ ={∅,⊤}=∗
            gregs_interp gr' ∗ gen_heap_interp m ∗ dev_interp d ∗
            WP (PlicLoop : expr riscv_lang) {{ Φ }})) -∗
    WP (PlicLoop : expr riscv_lang) {{ Φ }}.
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
      destruct Hstep as
        [ (gen2 & cpu2 & Hc & _)
        | [ (gen2 & Hc & _)
        | [ (gen2 & Hc & _)
        | [ (gen2 & Hu & -> & _ & -> & [ ([_ Hgg] & _) | (_ & ->) ])
        | (Hc & _) ] ] ] ];
        [ discriminate Hc | discriminate Hc | discriminate Hc
        | injection Hu as <-; exfalso; lia
        | injection Hu as <-
        | discriminate Hc ].
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
    iDestruct "Hera" as "(Hgr & Hmem & Hdev & Hdur)".
    iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
    iMod ("H" $! g.(gregs) g.(gmem) g.(gdev) with "[$Hgr $Hmem $Hdev]") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. exists [], (PlicLoopE gen_id),
        (GState (<[0%fin := register_set sig_seip
                    (bool_to_bit (dev_seip g.(gdev) (fin_to_nat (0%fin : CPU))))
                    (g.(gregs) 0%fin)]> g.(gregs)) g.(gmem) g.(gdev)
           g.(ggen) g.(gpow)), [].
      right; right; right; left. exists gen_id. split_and!; auto.
      left. split; [split; congruence|].
      eexists. split; [apply (PlicStepWire _ _ 0%fin)|]. rewrite Hpw. done. }
    iIntros (e2 g2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen2 & cpu2 & Hc & _)
      | [ (gen2 & Hc & _)
      | [ (gen2 & Hc & _)
      | [ (gen2 & Hu & -> & _ & -> & [ (Hlive & gr' & Hdstep & ->) | (Hnl & ->) ])
      | (Hc & _) ] ] ] ];
      [ discriminate Hc | discriminate Hc | discriminate Hc
      | injection Hu as <-
      | injection Hu as <-; exfalso; apply Hnl; split; congruence
      | discriminate Hc ].
    iMod ("Hk" $! gr' with "[//]") as "(Hgr' & Hmem' & Hdev' & HWP)".
    iIntros "_ !>". rewrite /state_interp /power_interp /fs_tie_interp
      /era_interp /disk_dur_interp /disk_img_auth /=.
    iFrame "Hgauth Hsauth Htie HWP".
    (* a PLIC step moves only registers: the image conjunct and the FS tie
       are both FRAMED (the device state is literally unchanged) *)
    iExists R. iFrame "HRauth".
    iSplitR; [iPureIntro; exact Hdom|].
    rewrite Hpw. iExists riscv_eraGS.
    iSplitR; [iPureIntro; exact HRE|].
    iFrame "Hgr' Hmem' Hdev'".
    iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview.
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

