(* HartRunFull.v -- [run_hart_active] WITH THE OUTCOME LEFT TO THE MACHINE,
   and the User-mode interrupt dispatch that feeds it.

   [HartRunGen]'s two rules already drop the privilege and make the dispatch
   and the fetch obligations.  They still bake in THREE things that the user
   tier cannot accept, and each one is forced by a user outcome the M/S rules
   cannot express:

     - THE FETCH SHAPE.  [swp_run_hart_active_gen] hardcodes [r = F_Base w]
       (its twin [F_RVC h]), so a caller whose fetch may FAULT has no rule at
       all: the model early-returns an [F_Error] as [Step_Fetch_Failure], and
       a user fetch walks a page table that may refuse it.  Here the fetch
       obligation is MATCH-SHAPED over [FetchResult]: the caller says, per
       constructor, what it is prepared to have happen -- and gives [False]
       for the shapes it has ruled out.  The base and RVC arms carry their
       own tail (the decode certificate, the landing-pad refusal, the
       compressed gate, and the execute obligation) INSIDE the fetch's
       postcondition, because the file the fetch lands on is existential:
       a TLB-filling or A/D-updating walk does not land where it started.

     - THE EXECUTE RESULT.  [⌜e = RETIRE_SUCCESS⌝] becomes an arbitrary
       [r : ExecutionResult] with the postcondition MATCHING on it, since a
       user instruction may Trap, be Illegal, or Enter_Wait
       ([UserClassify.u_result_ok]).  Nothing downstream of [execute] looks
       at the result other than to hand it to [Step_Execute], so the rule
       does not have to know which one it is.

     - THE [ExecuteAs] REDIRECT.  The model re-executes exactly once and
       feeds the SECOND result to [Step_Execute] unfiltered.  So the redirect
       is not a side condition but a second obligation, and it lives in the
       first execute's own postcondition ([run_exec_post]) -- which is what
       lets ONE rule serve both the direct and the redirecting composers
       ([SmodeCore.exec_hart_active_progress_base_gen] / [_RVC_gen],
       [UserStep.exec_hart_active_progress_base_redirect_gen] /
       [_RVC_direct_gen]) with no case split at the call site.

   Contents:
   §1  [dispatch_of_pending] and [swp_dispatchInterrupt_U] -- the dispatch at
       User.  It is STRICTLY SIMPLER than [WpIntrCore.swp_dispatchInterrupt_S]:
       at User both effective enables short-circuit on the privilege
       comparison alone ([and_boolM (returnM false) _]), so mstatus is never
       read and the rule takes no mstatus premise.  The PLIC wires are
       ∀-peeled exactly as in the S rule -- [swp_read_mip_S] and
       [swp_external_interrupts_pending_S] are privilege-free and are reused
       verbatim -- so the answer is EXISTENTIAL in [sig_meip] / [sig_seip].
   §2  [swp_run_hart_active_full] -- the core rule.
   §3  the five instances: the four that mirror the tier's exec composers,
       and the fetch-failure one.
   §4  [swp_run_hart_active_U] -- §2 with §1's dispatch discharged.

   The whole file is PRIVILEGE-GENERIC except §1 and §4.                    *)
From Stdlib Require Import ZArith Bool Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import ExecCommon.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb
        WpDecodeBridge WpMmodeCsrSwp HartRunGen.
Require Import RiscvExtras.
Require Import SmodeCore WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE DISPATCH AT USER.                                               *)
(* ===================================================================== *)

(* The dispatch decision once the S-destined pending set is known.  Both
   [WpIntrCore.s_dispatch] (Supervisor, gated on mstatus.SIE) and
   [UserStep.u_dispatch] (User, ungated) are readings of this one function;
   [u_dispatch mip meip seip mie mdv] IS
   [dispatch_of_pending (s_pending mip meip seip mie mdv)], by [reflexivity]. *)
Definition dispatch_of_pending (ip : mword 64)
    : option (InterruptType * Privilege) :=
  if neq_vec ip (zeros' 64)
  then match findPendingInterrupt ip with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Section rundisp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [getPendingSet User].  Mirrors [WpIntrCore.swp_getPendingSet_S] node for
     node; the two boolean blocks are bridged as their exec facts, and at
     User each is data-free (the privilege comparison decides it), so this
     rule -- unlike the S one -- needs neither [Db mstatus = true] nor a
     value for mstatus. *)
  Lemma swp_getPendingSet_U (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (mip_v mie_v mdv_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (getPendingSet User)
      (fun v => ∃ meip seip : mword 1,
                ⌜v = (if neq_vec (s_pending mip_v meip seip mie_v mdv_v)
                                 (zeros' 64)
                      then Some (s_pending mip_v meip seip mie_v mdv_v,
                                 Supervisor)
                      else None)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmip HDmie HDmdl Hmip Hmie Hmdl Hmm HDb Hag HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold getPendingSet.
    iApply (swp_bind_use (currentlyEnabled Ext_S) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag HESg HES)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_bind_use (Defs.read_reg mideleg) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmdl
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (read_mip IncludePlatformInterrupts) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_mip_S Drw Dro Df rs dst Db mip_v Hdisj HDmip Hmip
                HDb Hag HES HESg with "Hcert Hrw Hro"). }
    iIntros (v). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg mie) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmie
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg mie) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmie
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* ---- the mIE block.  At User the and_boolM short-circuits on
       [generic_eq User Machine = false], so mstatus is never read, and the
       or_boolM's second disjunct is [returnM true]. ---- *)
    match goal with |- context[Defs.or_boolM ?A ?B] =>
      set (Amie := Defs.or_boolM A B) end.
    assert (HmieAE : forall K : bool -> M bool,
              exec (Defs.bind (Defs.returnm (generic_eq User Machine)) K)
                dst = exec (K false) dst).
    { intro K.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_returnM (generic_eq User Machine) dst)).
      reflexivity. }
    assert (HmieE : exec Amie dst = Some (true, dst)).
    { subst Amie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- exec (Defs.bind ?A ?B) _ = _ =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HmieAE _); reflexivity
        | rewrite (exec_bind_Some _ _ _ _ _ HinE) ] end.
      cbn match.
      change (orb (generic_eq User Supervisor) (generic_eq User User))
        with true.
      apply exec_returnm. }
    assert (HmieG : goodb Db Amie dst = true).
    { subst Amie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- goodb _ (Defs.bind ?A ?B) _ = true =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HmieAE _); reflexivity | ];
        assert (HinG : goodb Db A dst = true);
        [ rewrite (goodb_bind Db _ _ dst (generic_eq User Machine)
                     (goodb_returnm Db _ dst) ltac:(apply exec_returnm));
          apply (goodb_returnm Db _ dst)
        | rewrite (goodb_bind Db A B dst false HinG HinE) ] end.
      apply (goodb_returnm Db _ dst). }
    iApply (swp_bind_use Amie _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs Amie true Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw Amie dst rs true
                   HDb Hag HmieG HmieE)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* ---- the sIE block.  Same short circuit, on
       [generic_eq User Supervisor = false]: this is the block the S rule
       has to read mstatus for, and at User it does not. ---- *)
    match goal with |- context[Defs.or_boolM ?A ?B] =>
      set (Asie := Defs.or_boolM A B) end.
    assert (HsieAE : forall K : bool -> M bool,
              exec (Defs.bind (Defs.returnm (generic_eq User Supervisor)) K)
                dst = exec (K false) dst).
    { intro K.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_returnM (generic_eq User Supervisor) dst)).
      reflexivity. }
    assert (HsieE : exec Asie dst = Some (true, dst)).
    { subst Asie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- exec (Defs.bind ?A ?B) _ = _ =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HsieAE _); reflexivity
        | rewrite (exec_bind_Some _ _ _ _ _ HinE) ] end.
      cbn match.
      change (generic_eq User User) with true.
      apply exec_returnm. }
    assert (HsieG : goodb Db Asie dst = true).
    { subst Asie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- goodb _ (Defs.bind ?A ?B) _ = true =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HsieAE _); reflexivity | ];
        assert (HinG : goodb Db A dst = true);
        [ rewrite (goodb_bind Db _ _ dst (generic_eq User Supervisor)
                     (goodb_returnm Db _ dst) ltac:(apply exec_returnm));
          apply (goodb_returnm Db _ dst)
        | rewrite (goodb_bind Db A B dst false HinG HinE) ] end.
      apply (goodb_returnm Db _ dst). }
    iApply (swp_bind_use Asie _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs Asie true Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw Asie dst rs true
                   HDb Hag HsieG HsieE)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hmie Hmdl Hmm.
    rewrite and_vec_zeros64_r.
    replace (neq_vec (zeros' 64 : mword 64) (zeros' 64)) with false
      by (vm_compute; reflexivity).
    rewrite andb_false_r. cbn match. rewrite andb_true_l.
    iApply swp_ret. iExists meip, seip.
    unfold s_pending, s_mip_bits. by iFrame.
  Qed.

  Lemma swp_dispatchInterrupt_U (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) (mip_v mie_v mdv_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (dispatchInterrupt User)
      (fun r => ∃ meip seip : mword 1,
                ⌜r = dispatch_of_pending
                       (s_pending mip_v meip seip mie_v mdv_v)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmip HDmie HDmdl Hmip Hmie Hmdl Hmm HDb Hag HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold dispatchInterrupt.
    iApply (swp_bind_use (getPendingSet User) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_getPendingSet_U Drw Dro Df rs dst Db mip_v mie_v mdv_v
                Hdisj HDmip HDmie HDmdl Hmip Hmie Hmdl Hmm HDb Hag HES HESg
                with "Hcert Hrw Hro"). }
    iIntros (v). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
    iApply swp_ret. iExists meip, seip. unfold dispatch_of_pending.
    destruct (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)).
    - cbn match.
      destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
        by iFrame.
    - cbn match. by iFrame.
  Qed.

End rundisp.

(* ===================================================================== *)
(* §2 [run_hart_active], RESULT-GENERIC.                                  *)
(* ===================================================================== *)

Section runfull.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac r_glue :=
    cbn beta iota zeta delta
      [Defs.returnm returnM returnR Defs.returnR andb orb negb not
       Instances.generic_eq Instances.generic_neq get_config_rvfi
       get_config_print_instr].

  (* THE EXECUTE OBLIGATION'S POSTCONDITION.  The model re-executes an
     [ExecuteAs] ONCE and feeds the second result to [Step_Execute]
     unfiltered, so the redirect is a second [swp] sitting in the first
     execute's post -- not a side condition, and not a separate rule. *)
  Definition run_exec_post (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (ib : mword 32) (e : ExecutionResult) : iProp Σ :=
    match e with
    | ExecuteAs other => swp (execute other) (fun e' => Pe e' ib)
    | _ => Pe e ib
    end.

  Lemma run_exec_post_direct (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (ib : mword 32) (e : ExecutionResult) :
    (match e with ExecuteAs _ => False | _ => True end) ->
    Pe e ib -∗ run_exec_post Pe ib e.
  Proof.
    intros He. destruct e; try (iIntros "H"; iApply "H"). destruct He.
  Qed.

  Lemma run_exec_post_redirect (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (ib : mword 32) (other : instruction) :
    swp (execute other) (fun e' => Pe e' ib) -∗
    run_exec_post Pe ib (ExecuteAs other).
  Proof. iIntros "H". iApply "H". Qed.

  (* THE BASE FETCH'S TAIL.  [rsf] is existential because a fetch that fills
     the TLB or updates A/D does not land on the file it started from; the
     decode certificate, the landing-pad refusal and the PC value are
     therefore stated ABOUT [rsf] here rather than as premises of the rule. *)
  Definition run_fetch_base (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) (w : mword 32) : iProp Σ :=
    (∃ (rsf : regstate) (i : instruction) (pc : mword 64) (nl : nat),
       ⌜register_lookup (R_bitvector_64 PC) rsf = pc⌝ ∗
       ⌜hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf⌝ ∗
       ⌜hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
          = Some (false, rsf)⌝ ∗
       hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
       (hreg_frame (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 4) rsf) Drw -∗
        hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 4) rsf) Dro -∗
        swp (execute i) (run_exec_post Pe (zero_extend' 32 w))))%I.

  (* THE COMPRESSED FETCH'S TAIL.  Same, plus the [Ext_Zca] gate: the model
     answers a compressed word with [Illegal_Instruction] when the extension
     is off, and this rule covers only the enabled path. *)
  Definition run_fetch_rvc (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) (h : mword 16) : iProp Σ :=
    (∃ (rsf : regstate) (i : instruction) (pc : mword 64) (nl nz : nat),
       ⌜register_lookup (R_bitvector_64 PC) rsf = pc⌝ ∗
       ⌜hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf⌝ ∗
       ⌜hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
          = Some (false, rsf)⌝ ∗
       ⌜hfrun nz (Drw ∪ Dro) Drw rsf (currentlyEnabled Ext_Zca)
          = Some (true, rsf)⌝ ∗
       hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
       (hreg_frame (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 2) rsf) Drw -∗
        hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 2) rsf) Dro -∗
        swp (execute i) (run_exec_post Pe (zero_extend' 32 h))))%I.

  (* THE FETCH OBLIGATION'S POSTCONDITION: one arm per [FetchResult]
     constructor.  A caller that has ruled a shape out gives [False] for it. *)
  Definition run_fetch_post (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) (fr : FetchResult) : iProp Σ :=
    match fr with
    | F_Base w        => run_fetch_base Drw Dro Df Pe w
    | F_RVC h         => run_fetch_rvc Drw Dro Df Pe h
    | F_Error (e, xv) => Pf xv e
    | F_Ext_Error x   => Px x
    end.

  (* ==================================================================== *)
  (* THE CORE RULE.                                                        *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_full (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (p : Privilege)
      (Qi : InterruptType -> Privilege -> iProp Σ)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE DISPATCH: the machine picks the arm *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (* THE FETCH: the machine picks the SHAPE, and each shape carries its
       own tail *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (run_fetch_post Drw Dro Df Pe Pf Px)) -∗
    swp (run_hart_active 0)
      (fun st => match st with
                 | Step_Pending_Interrupt (ii, pr) => Qi ii pr
                 | Step_Execute (r, ib)            => Pe r ib
                 | Step_Fetch_Failure (Virtaddr xv, e) => Pf xv e
                 | Step_Ext_Fetch_Failure x        => Px x
                 | Step_Waiting _                  => False
                 end).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv.
    iIntros "#Hcert Hrw Hro Hdisp Hfet".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp] [-]").
    { iApply ("Hdisp" with "Hrw Hro"). }
    iIntros (o) "Ho".
    destruct o as [[ii pr] |].
    - (* ---- THE TRAP ARM: early return, nothing else runs ---- *)
      cbn beta iota. rewrite mcer_early_return.
      iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))). iApply "Ho".
    - (* ---- THE RETIRE ARM: on into the fetch ---- *)
      iDestruct "Ho" as "[Hrw Hro]".
      cbn beta iota. rewrite mbind0_ret.
      iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hfet] [-]").
      { iApply ("Hfet" with "Hrw Hro"). }
      iIntros (fr) "Hfr".
      destruct fr as [ x | w | h | [e xv] ]; rewrite /run_fetch_post.
      + (* ---- F_Ext_Error: the model early-returns it as a Step ---- *)
        cbn beta iota zeta delta [ext_fetch_hook]. r_glue.
        rewrite mcer_ret.
        iApply ("Hcont" $! (Step_Ext_Fetch_Failure x)). iApply "Hfr".
      + (* ---- F_Base: decode, landing pad, nextPC+4, execute ---- *)
        rewrite /run_fetch_base.
        iDestruct "Hfr" as (rsf i pc nl)
          "(%Hpcf & %Hdec & %Hlpad & Hrw & Hro & Hex)".
        cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
          fetch_callback get_config_print_instr].
        iApply (swp_use_cer (ext_decode w) _ _ C HC with "[Hrw Hro] [-]").
        { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj Hdec
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". r_glue.
        rewrite mbind0_ret.
        iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj Hlpad
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". r_glue.
        rewrite mbind_ret. r_glue.
        iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". rewrite Hpcf.
        iApply (swp_use_cer2
                  (Defs.write_reg (R_bitvector_64 nextPC)
                     (add_vec_int pc 4)) _ _ _ C HC with "[Hrw Hro] [-]").
        { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                    with "Hcert Hrw Hro"). }
        iIntros (u) "[Hrw Hro]".
        iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hex] [-]").
        { iApply ("Hex" with "Hrw Hro"). }
        iIntros (er) "He". rewrite /run_exec_post.
        (* the nine direct results land straight in [Step_Execute]; the
           tenth is the redirect, and the model does NOT filter what the
           second [execute] returns *)
        destruct er; try (r_glue; rewrite mcer_ret; iApply "Hcont";
                          iApply "He").
        r_glue.
        iApply (swp_use_cer (execute i0) _ _ C HC with "[He] [-]").
        { iApply "He". }
        iIntros (er2) "He2". r_glue. rewrite mcer_ret.
        iApply "Hcont". iApply "He2".
      + (* ---- F_RVC: compressed decode, the Zca gate, nextPC+2 ---- *)
        rewrite /run_fetch_rvc.
        iDestruct "Hfr" as (rsf i pc nl nz)
          "(%Hpcf & %Hdec & %Hlpad & %Hzca & Hrw & Hro & Hex)".
        cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
          fetch_callback get_config_print_instr].
        iApply (swp_use_cer (ext_decode_compressed h) _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj Hdec
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". r_glue.
        rewrite mbind0_ret.
        iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj Hlpad
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". r_glue.
        rewrite mbind_ret. r_glue.
        iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_hfrun nz Drw Dro Df rsf rsf _ _ Hdisj Hzca
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". r_glue.
        iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                  with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". rewrite Hpcf.
        iApply (swp_use_cer2
                  (Defs.write_reg (R_bitvector_64 nextPC)
                     (add_vec_int pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
        { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                    with "Hcert Hrw Hro"). }
        iIntros (u) "[Hrw Hro]".
        iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hex] [-]").
        { iApply ("Hex" with "Hrw Hro"). }
        iIntros (er) "He". rewrite /run_exec_post.
        destruct er; try (r_glue; rewrite mcer_ret; iApply "Hcont";
                          iApply "He").
        r_glue.
        iApply (swp_use_cer (execute i0) _ _ C HC with "[He] [-]").
        { iApply "He". }
        iIntros (er2) "He2". r_glue. rewrite mcer_ret.
        iApply "Hcont". iApply "He2".
      + (* ---- F_Error: the fetch faulted, and nothing after it runs ---- *)
        cbn beta iota zeta delta [ext_fetch_hook]. r_glue.
        rewrite mcer_ret.
        iApply ("Hcont" $! (Step_Fetch_Failure (Virtaddr xv, e))).
        iApply "Hfr".
  Qed.

  (* ==================================================================== *)
  (* §3 THE INSTANCES.  Each pins the fetch's shape and reads off exactly   *)
  (* one of the tier's exec composers; the conclusion is [HartRunGen]'s     *)
  (* disjunctive one, generalised from [RETIRE_SUCCESS] to any [resf].      *)
  (* ==================================================================== *)

  (* the swp twin of [SmodeCore.exec_hart_active_progress_base_gen] *)
  Lemma swp_run_hart_active_base (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (w : mword 32) (i : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    (match resf with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i) (fun e => ⌜e = resf⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗ R)).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv Hpcf Hdec Hlpad Hnr.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_full Drw Dro Df rs p Qi
                   (fun r ib => (⌜r = resf⌝ ∗ ⌜ib = zero_extend' 32 w⌝ ∗ R)%I)
                   (fun _ _ => False%I) (fun _ => False%I)
                   Hdisj HDpriv HDpc HDnpc Hpriv
                   with "Hcert Hrw Hro Hdisp [Hfet Hex]") ].
    - iIntros (st) "H".
      destruct st as [[ii pr] | x | [[xv] ex] | [er ib] | wr ];
        [ | iDestruct "H" as %[] | iDestruct "H" as %[] |
          | iDestruct "H" as %[] ].
      + iLeft. iExists ii, pr. by iFrame.
      + iDestruct "H" as "(-> & -> & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[Hex] [Hrw Hro Hfet]");
        [| iApply ("Hfet" with "Hrw Hro") ].
      iIntros (r) "(-> & Hrw & Hro)".
      rewrite /run_fetch_post /run_fetch_base.
      iExists rsf, i, pc, nl.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|]. iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & HR)".
      iApply (run_exec_post_direct _ _ _ Hnr).
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* the swp twin of [UserStep.exec_hart_active_progress_base_redirect_gen] *)
  Lemma swp_run_hart_active_base_redirect (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (w : mword 32) (i other : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 swp (execute other) (fun e' => ⌜e' = resf⌝ ∗ R))) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗ R)).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv Hpcf Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_full Drw Dro Df rs p Qi
                   (fun r ib => (⌜r = resf⌝ ∗ ⌜ib = zero_extend' 32 w⌝ ∗ R)%I)
                   (fun _ _ => False%I) (fun _ => False%I)
                   Hdisj HDpriv HDpc HDnpc Hpriv
                   with "Hcert Hrw Hro Hdisp [Hfet Hex]") ].
    - iIntros (st) "H".
      destruct st as [[ii pr] | x | [[xv] ex] | [er ib] | wr ];
        [ | iDestruct "H" as %[] | iDestruct "H" as %[] |
          | iDestruct "H" as %[] ].
      + iLeft. iExists ii, pr. by iFrame.
      + iDestruct "H" as "(-> & -> & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[Hex] [Hrw Hro Hfet]");
        [| iApply ("Hfet" with "Hrw Hro") ].
      iIntros (r) "(-> & Hrw & Hro)".
      rewrite /run_fetch_post /run_fetch_base.
      iExists rsf, i, pc, nl.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|]. iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & Hred)".
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[] Hred"). iIntros (e') "(-> & HR)".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* the swp twin of [SmodeCore.exec_hart_active_progress_RVC_gen] *)
  Lemma swp_run_hart_active_rvc (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (h : mword 16) (i other : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 swp (execute other) (fun e' => ⌜e' = resf⌝ ∗ R))) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 h)⌝ ∗ R)).
  Proof.
    intros Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpcf HmisaC Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_full Drw Dro Df rs p Qi
                   (fun r ib => (⌜r = resf⌝ ∗ ⌜ib = zero_extend' 32 h⌝ ∗ R)%I)
                   (fun _ _ => False%I) (fun _ => False%I)
                   Hdisj HDpriv HDpc HDnpc Hpriv
                   with "Hcert Hrw Hro Hdisp [Hfet Hex]") ].
    - iIntros (st) "H".
      destruct st as [[ii pr] | x | [[xv] ex] | [er ib] | wr ];
        [ | iDestruct "H" as %[] | iDestruct "H" as %[] |
          | iDestruct "H" as %[] ].
      + iLeft. iExists ii, pr. by iFrame.
      + iDestruct "H" as "(-> & -> & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[Hex] [Hrw Hro Hfet]");
        [| iApply ("Hfet" with "Hrw Hro") ].
      iIntros (r) "(-> & Hrw & Hro)".
      rewrite /run_fetch_post /run_fetch_rvc.
      iExists rsf, i, pc, nl, 4%nat.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iSplitR; [iPureIntro;
                exact (hfrun_cE_Zca (Drw ∪ Dro) Drw rsf HDmisa HmisaC)|].
      iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & Hred)".
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[] Hred"). iIntros (e') "(-> & HR)".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* the swp twin of [UserStep.exec_hart_active_progress_RVC_direct_gen] *)
  Lemma swp_run_hart_active_rvc_direct (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (h : mword 16) (i : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    (match resf with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i) (fun e => ⌜e = resf⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 h)⌝ ∗ R)).
  Proof.
    intros Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpcf HmisaC Hdec Hlpad Hnr.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_full Drw Dro Df rs p Qi
                   (fun r ib => (⌜r = resf⌝ ∗ ⌜ib = zero_extend' 32 h⌝ ∗ R)%I)
                   (fun _ _ => False%I) (fun _ => False%I)
                   Hdisj HDpriv HDpc HDnpc Hpriv
                   with "Hcert Hrw Hro Hdisp [Hfet Hex]") ].
    - iIntros (st) "H".
      destruct st as [[ii pr] | x | [[xv] ex] | [er ib] | wr ];
        [ | iDestruct "H" as %[] | iDestruct "H" as %[] |
          | iDestruct "H" as %[] ].
      + iLeft. iExists ii, pr. by iFrame.
      + iDestruct "H" as "(-> & -> & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[Hex] [Hrw Hro Hfet]");
        [| iApply ("Hfet" with "Hrw Hro") ].
      iIntros (r) "(-> & Hrw & Hro)".
      rewrite /run_fetch_post /run_fetch_rvc.
      iExists rsf, i, pc, nl, 4%nat.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iSplitR; [iPureIntro;
                exact (hfrun_cE_Zca (Drw ∪ Dro) Drw rsf HDmisa HmisaC)|].
      iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & HR)".
      iApply (run_exec_post_direct _ _ _ Hnr).
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* THE FETCH-FAILURE INSTANCE.  Nothing after the fetch runs: the model
     early-returns, so the caller owes no decode, no landing-pad fact and no
     execute -- only the fetch itself, landing on [F_Error]. *)
  Lemma swp_run_hart_active_fetch_fail (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (p : Privilege)
      (xv : mword 64) (e : ExceptionType) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (fun r => ⌜r = F_Error (e, xv)⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Fetch_Failure (Virtaddr xv, e)⌝ ∗ R)).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv.
    iIntros "#Hcert Hrw Hro Hdisp Hfet".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_full Drw Dro Df rs p Qi
                   (fun _ _ => False%I)
                   (fun xv' e' => (⌜xv' = xv⌝ ∗ ⌜e' = e⌝ ∗ R)%I)
                   (fun _ => False%I)
                   Hdisj HDpriv HDpc HDnpc Hpriv
                   with "Hcert Hrw Hro Hdisp [Hfet]") ].
    - iIntros (st) "H".
      destruct st as [[ii pr] | x | [[xv'] ex] | [er ib] | wr ];
        [ | iDestruct "H" as %[] | | iDestruct "H" as %[]
          | iDestruct "H" as %[] ].
      + iLeft. iExists ii, pr. by iFrame.
      + iDestruct "H" as "(-> & -> & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[] [Hrw Hro Hfet]");
        [| iApply ("Hfet" with "Hrw Hro") ].
      iIntros (r) "(-> & HR)". rewrite /run_fetch_post.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* ==================================================================== *)
  (* §4 THE CORE RULE AT USER, dispatch discharged.  [Qi] is BAKED (as in    *)
  (* [WpIntrCore.swp_run_hart_active_S]): the wire values are not known      *)
  (* until the dispatch has run, so the existential lives in the payload.    *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_U (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) (mip_v mie_v mdv_v : mword 64)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = User ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (run_fetch_post Drw Dro Df Pe Pf Px)) -∗
    swp (run_hart_active 0)
      (fun st => match st with
                 | Step_Pending_Interrupt (ii, pr) =>
                     ∃ meip seip : mword 1,
                       ⌜dispatch_of_pending
                          (s_pending mip_v meip seip mie_v mdv_v)
                        = Some (ii, pr)⌝ ∗
                       hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                 | Step_Execute (r, ib)            => Pe r ib
                 | Step_Fetch_Failure (Virtaddr xv, e) => Pf xv e
                 | Step_Ext_Fetch_Failure x        => Px x
                 | Step_Waiting _                  => False
                 end).
  Proof.
    intros Hdisj HDpriv HDmip HDmie HDmdl HDpc HDnpc Hpriv Hmip Hmie Hmdl Hmm
      HDb Hag HES HESg.
    iIntros "#Hcert Hrw Hro Hfet".
    iApply (swp_run_hart_active_full Drw Dro Df rs User
              (fun ii pr => (∃ meip seip : mword 1,
                   ⌜dispatch_of_pending (s_pending mip_v meip seip mie_v mdv_v)
                    = Some (ii, pr)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)
              Pe Pf Px Hdisj HDpriv HDpc HDnpc Hpriv
              with "Hcert Hrw Hro [] Hfet").
    (* the dispatch, from §1, re-shaped into the match the core rule expects *)
    iIntros "Hrw Hro".
    iApply (swp_mono with "[] [Hrw Hro]");
      [| iApply (swp_dispatchInterrupt_U Drw Dro Df rs dst Db mip_v mie_v mdv_v
                   Hdisj HDmip HDmie HDmdl Hmip Hmie Hmdl Hmm HDb Hag HES HESg
                   with "Hcert Hrw Hro") ].
    iIntros (o). iDestruct 1 as (meip seip) "(%Hd & Hrw & Hro)".
    destruct o as [[ii pr] |].
    - iExists meip, seip. iFrame. iPureIntro. by rewrite Hd.
    - iFrame.
  Qed.

End runfull.
