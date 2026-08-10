(* WpNext.v -- the continuation of every S-mode step.

   An instruction executed with interrupts ENABLED can be trapped, the thread
   yielded, and execution resumed on a DIFFERENT hart.  So a step's
   continuation quantifies the hart -- and, because the binder is named [CID],
   every resource written inside [K] is automatically about the hart we RESUME
   on, with no annotation and no change to any resource's spelling.  That
   includes the SIE ghost: it is the hart's CANONICAL name ([sie_name], hence
   [IntrDefs.sie_gname]), so rebinding [CID] rebinds the ghost too and no
   separate ghost binder is needed.

   With interrupts DISABLED no trap is taken, so the hart is pinned.  That is
   the [b = false] implication, and it is what lets push_off'd code read [tp]
   once and keep using the answer ([push_off(); c = mycpu(); c->noff++]).
   [wp_next_off] collapses the whole thing away, so an interrupts-off (or
   M-mode) contract is stated exactly as it is today, with no binder at all.

   THERE IS A SECOND WAY THE HART IS PINNED, AND IT IS NOT ABOUT SIE: a thread
   with NO CURRENT PROC cannot be yielded.  [kerneltrap] yields only when
   [myproc() != 0], so the scheduler thread -- whose [cpus[cid].proc] is 0 --
   provably stays where it is even with interrupts on.  That datum is already
   threaded through the whole S-mode tier as [sie_arm] / [sie_cap_gpr]'s [p]
   (the value of [cpus[cid].proc]), so [wp_next] takes it and offers the second
   escape hatch [wp_next_idle].  [scheduler()] needs exactly this and no
   crossing payload could serve instead: what it holds across its
   interrupts-enabled window is REGISTER state naming the ENTRY hart's [cpus[]]
   fields, so on another hart the [sd s1,48(s4)] at +0x68 would write the wrong
   hart's [cpu->proc] -- the code would simply be wrong, which is why this is a
   refutation of migration rather than a transport of resources across one.

   This WEAKENS nothing.  The condition under which the continuation is pinned
   got LARGER, so a consumer of [wp_next] receives a stronger hypothesis, and a
   leaf that PRODUCES one still produces it at its own hart, where the
   implication holds vacuously.

   The soundness obligation this creates lands on Stage 2's
   [intr_handler_spec]: NO CURRENT PROC IMPLIES THE TRAP RETURNS ON THE SAME
   HART.  That is a true statement about [kerneltrap]; writing it down here
   makes it a premise someone must discharge rather than an accident.

   THIS FILE IS THE ONLY PLACE THAT NAMES THE HART WE CAME FROM -- and it must
   therefore live outside any section that fixes [CpuId], because Rocq refuses
   to rebind a SECTION variable's name ("CID is already used"), which is
   exactly the shadowing every consumer relies on. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.   (* [zero_reg]: the idle hatch *)
Require Import RiscvLang.

Section WpNext.
  Context {Σ : gFunctors}.

  Definition wp_next `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64)
      (K : forall (CID : CpuId), iProp Σ) : iProp Σ :=
    (∀ CID : CpuId,
       ⌜ b = false \/ p = zero_reg -> (CID : CPU) = (CID0 : CPU) ⌝ -∗ K CID)%I.

  (* Always available, at ANY [b] and any [p]: proving the hart-generic form
     discharges the step's obligation.  (The converse needs one of the two
     pinning conditions.) *)
  Lemma wp_next_intro `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64) K :
    (∀ CID : CpuId, K CID) -∗ wp_next b p K.
  Proof. iIntros "H" (CID _). iApply "H". Qed.

  (* Interrupts off: the hart is the one we started with (and hence so is its
     canonical SIE ghost), so the continuation is stated with no binder --
     today's spelling exactly. *)
  Lemma wp_next_off `{GEN : GenId} `{CID0 : CpuId} (p : mword 64) K :
    wp_next false p K ⊣⊢ K CID0.
  Proof.
    iSplit.
    - iIntros "H". iApply ("H" $! CID0). iPureIntro. intros _. reflexivity.
    - iIntros "H" (CID Hs). pose proof (Hs (or_introl eq_refl)) as Hc.
      rewrite (_ : CID = CID0); [ iExact "H" | exact Hc ].
  Qed.

  (* THE INTRODUCTION HALF OF [wp_next_off], AS A WAND -- and the spelling a
     whole-function proof should use.  [rewrite wp_next_off] is a SETOID
     rewrite of an [⊣⊢] over the whole proofmode goal, so it re-traverses the
     entire Iris context once per instruction; at ~130 instructions over a
     syscall-sized context that is tens of seconds a file (measured 45 s of
     ProofVirtioDiskInit's 576 s, and 12 s once switched).  [iApply
     wp_next_off_intro] only has to match the goal's head, and leaves exactly
     the same continuation. *)
  Lemma wp_next_off_intro `{GEN : GenId} `{CID0 : CpuId} (p : mword 64) K :
    K CID0 -∗ wp_next false p K.
  Proof. iIntros "H". by iApply wp_next_off. Qed.

  (* NO CURRENT PROC: the thread cannot be yielded, so the hart is pinned even
     at [b = true].  Same collapse as [wp_next_off], from the other hatch. *)
  Lemma wp_next_idle `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64) K :
    p = zero_reg -> wp_next b p K ⊣⊢ K CID0.
  Proof.
    intros Hp.
    iSplit.
    - iIntros "H". iApply ("H" $! CID0). iPureIntro. intros _. reflexivity.
    - iIntros "H" (CID Hs). pose proof (Hs (or_intror Hp)) as Hc.
      rewrite (_ : CID = CID0); [ iExact "H" | exact Hc ].
  Qed.

  (* THE ELIMINATION FORM AN ENGINE USES, at an EXPLICIT hart.  A layer whose
     own step neither pins nor moves the hart (it sits between two [wp_next]s)
     transports its caller's hart-generic continuation straight to whatever
     hart its OWN callback was instantiated at, carrying the guard along.
     Stating it once keeps the guard bookkeeping out of every Iris proof.

     [CID0] IS PINNED EXPLICITLY IN THE [wp_next] BELOW, and it has to be: with
     two [CpuId] hypotheses in scope, instance resolution would fill the
     definition's own [CID0] slot from the LAST one -- [CIDn] -- and the guard
     would silently degrade to the tautology [CIDn = CIDn].  Every statement in
     this file that mentions two harts is spelled out for that reason. *)
  Lemma wp_next_at `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64) K
      (CIDn : CpuId) :
    (b = false \/ p = zero_reg -> (CIDn : CPU) = (CID0 : CPU)) ->
    wp_next (CID0 := CID0) b p K -∗ K CIDn.
  Proof. iIntros (Hs) "H". iApply ("H" $! CIDn). iPureIntro. exact Hs. Qed.

  (* ... and the SAME-HART instance of it: an engine that provably returns to
     the hart it started on (STAGE 1 -- the absorbing Löb is at a fixed hart,
     a trap returns where it came from) consumes the hart-generic obligation
     its STATEMENT demands of callers here, with the guard closed by
     [reflexivity].  Unlike [wp_next_off] this needs no condition on [b] or
     [p]: it is the direction that is always available.

     THIS IS THE LEMMA THAT MAKES THE FUNNEL'S OWN CONVERSION FREE, AND THE
     ONE THAT MARKS WHERE THE STAGING HAS TO STOP.  Wrapping
     [WpSmodeIntr.wp_instr_s_sconf]'s σ-callback in [wp_next b p] is provable
     by exactly this: the funnel consumes the leaf's hart-generic obligation at
     its own hart and its body is unchanged.  Wrapping the callbacks of the two
     engines BELOW it ([WpIntrInv.wp_exec_step_intr],
     [WpSmodeIntr.wp_instr_s_intr]) is NOT, and [wp_next_here] is precisely the
     step that is then unavailable: the funnel would have to PRODUCE a
     hart-generic callback for the absorbing engine, and its '1' arm frames
     PER-HART residue at the entry hart across that engine -- the [sret_bits]
     halves, the SIE eighth, [cpu_hart]'s per-cpu cells, [strans_bit], and
     [intr_inv] itself.  Only the trap handler can hand those back at the
     resuming hart, so that half of the move belongs with [intr_handler_spec] /
     [intr_frame], not here. *)
  Lemma wp_next_here `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64) K :
    wp_next b p K -∗ K CID0.
  Proof. iApply (wp_next_at b p K CID0). intros _. reflexivity. Qed.

  (* RE-ANCHORING A CALLER'S OBLIGATION AT ANOTHER HART.  A layer whose own
     step MOVED the hart -- a parking function whose [swtch] resumed
     elsewhere, and, at Stage 2, the absorbing engine re-entering its Löb on
     the hart the last trap returned to -- holds its caller's [wp_next] at the
     hart it STARTED on and has to discharge one at the hart it ENDED on.
     Those are different propositions (the guard's right-hand side names the
     anchor), so this is a TRANSPORT, not a frame: the third instance of the
     shape [IntrDefs.cpu_own_transport] / [IntrDefs.trap_csrs_ext_transport]
     already established -- A HART-INDEXED RESOURCE THAT SURVIVES A POSSIBLE
     MIGRATION NEEDS A TRANSPORT LEMMA, NOT A FRAME.

     Sound rather than a fudge, and both halves are worth seeing.  At
     [p <> zero_reg] and [b = true] the guard is vacuous, so [wp_next true p K]
     is just [forall CID, K CID] and re-supplying it anywhere is free -- which
     is exactly the case a parking function is in ([proc_addr_nonzero] refutes
     the idle hatch).  At [p = zero_reg] the mover's OWN [wp_next] guarantees
     it came back on the same hart ([wp_next_idle]), and that is precisely the
     hypothesis [Heq].

     THIS IS WHERE [wp_next]'s SECOND ESCAPE HATCH IS CALLED IN.  The hatch was
     introduced for [scheduler()] (claude-notes/completed/explicit-cpuid.md),
     which recorded "no current proc => the trap returns on the same hart" as a
     debt against Stage 2; [Heq] is the place that debt is paid, and Stage 2's
     [IntrDefs.intr_handler_spec] is what will discharge it for the trap
     arm. *)
  Lemma wp_next_retarget `{GEN : GenId} (CID0 CID1 : CpuId) (b : bool)
      (p : mword 64) K :
    (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
    wp_next (CID0 := CID0) b p K -∗ wp_next (CID0 := CID1) b p K.
  Proof.
    intros Heq. iIntros "H" (CID Hs). iApply "H".
    iPureIntro. intros Hb. rewrite (Hs Hb). exact (Heq Hb).
  Qed.

  (* Chaining: the conditional equalities compose, which is what lets a
     [b]-GENERIC whole-function proof thread one implication per instruction
     and still discharge its own continuation at the end -- with no case split
     on [b] anywhere. *)
  Lemma wp_next_trans `{GEN : GenId} `{CID0 : CpuId} (b : bool) (p : mword 64)
      (CID1 : CpuId) (CID2 : CpuId) :
    (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
    (b = false \/ p = zero_reg -> (CID2 : CPU) = (CID1 : CPU)) ->
    (b = false \/ p = zero_reg -> (CID2 : CPU) = (CID0 : CPU)).
  Proof.
    intros H1 H2 Hb. pose proof (H1 Hb) as Ha. pose proof (H2 Hb) as Hc.
    by rewrite Hc.
  Qed.
End WpNext.

(* THE CONSUMER-SIDE DISCHARGE.  A straight-line stretch accumulates one
   conditional equality per instruction; this closes the function's own
   [wp_next] obligation from however many are in context, at any [b], with no
   case split.  Plain [eapply wp_next_trans; eassumption] does NOT do it -- the
   hypotheses arrive spelled [@cpu_id CIDk] while the lemma is stated at the
   bare binder -- so chain them by congruence instead.  (Note there is NO
   [split] here: since the SIE ghost went canonical the per-step fact is a
   bare equation, not a conjunction, and a [split] on an equation is
   [constructor 1] = [eq_refl] and would fail on the first chained step.) *)
(* THE GOAL'S INDEX AND THE CHAIN'S NEED NOT BE THE SAME TERM.  A PARKING
   function's own [wp_next] index is the literal [true] (a swtch moves the
   hart whatever SIE was doing), while the leaves it ran carry its caller's
   [eb] -- so the hypothesis to discharge and the chain facts are
   disjunctions with DIFFERENT left components, and a plain [specialize]
   does not typecheck.  The fallback keeps only the RIGHT disjunct (the
   left one is [true = false], absurd) and re-injects it at whatever index
   the chain fact carries.  At a matching index the first branch fires and
   nothing changes. *)
Ltac wp_next_chain :=
  let Hd := fresh "Hd" in
  intros Hd;
  repeat match goal with
         | H : _ = false \/ _ = _ -> _ = _ |- _ =>
             first
               [ specialize (H Hd)
               | specialize (H (or_intror
                   ltac:(destruct Hd as [Hbad | Hgood];
                         [ discriminate Hbad | exact Hgood ]))) ]
         end;
  solve [ congruence
        | repeat match goal with
                 | H : ?a = ?b |- ?a = ?c => rewrite H; clear H
                 end; reflexivity ].
