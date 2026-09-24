(* AppPipe.v -- THE PIPELINE APPLICATION'S RECORD.

   Design of record: claude-notes/design/app-pipe.md section 5.5, lane
   PIPE-STAGE, deliverable 4.  [AppEcho.v]'s sections 5 and 6 (and
   upstream's [AppFileRec.v]) at the pipeline claim: the conclusion, the
   record [app_pipe], and [App.xv6_app_laws] with every field but
   [al_programs] discharged.

   THE CLAIM IS ECHO'S SHAPE WITH /cat PINNED (design section 5.6, RULED
   after this lane's part-1 finding): [app_pred] is
   [AppPipeClaim.pipe_pred], which is [AppEcho.echo_pred] with
   [FileFsPure.file_fs_pure] where [echo_fs_pure] was -- a pipeline round
   modifies no file, but sh EXECS /cat, and echo's claim pins /init, /sh and
   /echo only.  [app_fixed], [app_cl] and [app_names] are still [AppEcho]'s
   own names, and [app_boot] is [echo_boot] under the name [pipe_boot] (the
   console key or flag reads no file-system pin).  What is new besides the
   claim is the CONSOLE half: [app_R] is [PipesOut.pipesE_led], [app_ifc] is
   the pipeline tag / taint / claim / licence, and [app_phi] is
   the N-stage model's conclusion (cut C8: the claim is born at
   [PipesDisc.pipes_lmE], the typed lines [echo ws] and
   [echo ws | cat | ... | cat]).

   ONE THING IS A SECTION HYPOTHESIS AND IS NOT DISCHARGED HERE:
   [al_programs], lane SH-PIPE-ROUND's (the first process's exec bundle).
   It is not an axiom -- every result below is a theorem with it in its
   binder list -- and the instance simply does not exist until that lane
   lands, exactly as [AppFileRec] does for SH-ROUND.  [Decision
   (PipeDisc.disc_p h)] is NOT a hypothesis: it is
   [PipeDiscDec.disc_p_dec] (lane PIPE-DEC). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import FsCrash.
Require Import FsImgDisk.
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsState.
Require Import FsAbsDefs.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import AppInv.
Require Import DevModel.
Require Import UartNames.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
Require Import FileInvDefs.
Require Import AppCfg.
Require Import FsCfg.
Require Import App.
Require Import UserFd.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import Xv6Cameras.
Require Import InitBoot.
Require Import InodeInv.
Require Import RiscvAdequacy.
Require Import EchoDisc.
Require Import ConsLog.
Require Import PipeDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppPipeClaim.
Require Import PipeOut.
Require Import LineModel.
Require Import PipesDisc.
Require Import PipeOutN PipeOutNEv.
Require Import PipesOut.
Require Import PipesLinks.
Require Import PipesDecE.
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE CONCLUSION                                                     *)
(*                                                                        *)
(*  [LineModel]'s conclusion at [PipesDisc.pipes_lmE]: a disciplined     *)
(*  history's every cycle is a good output.  Like [AppEcho.echo_phi] it   *)
(*  reads the trace alone, so the state argument is dropped.              *)
(* ====================================================================== *)
Definition pipe_phi : gstate -> list mobs -> Prop :=
  fun _ h => lm_disc pipes_lmE h -> Forall (lm_good_out pipes_lmE tt) (cycles_of h).

Section PipeApp.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !pipeOutG Σ}.

  (* ---- the four fields that are resources ---- *)

  Definition pipe_R (c : pipe_gn) (h : list mobs) : iProp Σ :=
    pipesE_led c h.

  Global Instance pipe_R_timeless c h : Timeless (pipe_R c h).
  Proof using . rewrite /pipe_R. apply _. Qed.

  Definition pipe_tag (c : pipe_gn) (h : list mobs) : iProp Σ := ptagE c h.

  Global Instance pipe_tag_persistent c h : Persistent (pipe_tag c h).
  Proof using . rewrite /pipe_tag. apply _. Qed.
  Global Instance pipe_tag_timeless c h : Timeless (pipe_tag c h).
  Proof using . rewrite /pipe_tag. apply _. Qed.

  (* THE KILL CREDENTIAL IS THE ECHO APPLICATION'S TAINT, unchanged: a kill
     under this discipline is impossible, so what a party a kill touched may
     keep is the fact the taint already states. *)
  Definition pipe_kill (c : pipe_gn) : iProp Σ := echo_taint (pgn_cl c).

  Global Instance pipe_kill_persistent c : Persistent (pipe_kill c).
  Proof using . rewrite /pipe_kill. apply _. Qed.
  Global Instance pipe_kill_timeless c : Timeless (pipe_kill c).
  Proof using . rewrite /pipe_kill. apply _. Qed.

  Definition pipe_cons (c : pipe_gn)
    : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ := peclE c.

  Global Instance pipe_cons_timeless c k h H : Timeless (pipe_cons c k h H).
  Proof using . rewrite /pipe_cons. apply _. Qed.

  (* ...AND THE INTERFACE'S LICENCE LAW ([RiscvPtsto.ai_lic], upstream's
     lane SUP-ONE): [pipe_al_sup]'s conclusion read one step earlier, at
     the CREDENTIAL rather than at the supply.  The pipeline application's
     kill price is the echo application's taint, and a tainted claim
     answers any boundary event out of its taint arm. *)
  Lemma pipe_cons_lic (c : pipe_gn) :
    pipe_kill c ⊢
      □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
           (ev : ConsLog.cons_ev),
           pipe_cons c k h H ==∗ pipe_cons c k h (ConsLog.cons_step H ev)).
  Proof using . 
    rewrite /pipe_cons /pipe_kill. iIntros "#Ht !>" (k h H ev) "Ho".
    iApply (pecl'_sup c (fun _ => None) adm_echo pipes_lm_echo_laws k h H ev with "Ht Ho").
  Qed.

  Definition pipe_ifc (c : pipe_gn) : app_iface Σ :=
    MkAppIface (pipe_tag c) (pipe_tag_persistent c) (pipe_tag_timeless c)
               (pipe_kill c) (pipe_kill_persistent c) (pipe_kill_timeless c)
               (pipe_cons c) (pipe_cons_timeless c) (pipe_cons_lic c).

  Definition pipe_turn (c : pipe_gn) : nat -> iProp Σ := pturn c.

  (* ====================================================================== *)
  (*  2.  THE RECORD                                                        *)
  (* ====================================================================== *)
  Definition app_pipe : xv6_app Σ :=
    MkApp pipe_gn pipe_cl_all echo_names
          (fun c => pipe_pred (pgn_cl c)) (fun c => pipe_boot (pgn_cl c))
          pipe_R pipe_ifc pipe_turn pipe_phi.

  (* ---- the birth step ---- *)
  Lemma pipe_al_birth : ⊢ |==> ∃ c : app_fixed app_pipe, app_cl app_pipe c.
  Proof using . cbn [app_pipe app_fixed app_cl]. exact pipe_birth_all. Qed.

  Lemma pipe_al_Rt (c : app_fixed app_pipe) (h : list mobs) :
    Timeless (app_R app_pipe c h).
  Proof using . cbn [app_pipe app_fixed app_R] in c |- *. apply _. Qed.

  (* the supply buys the kill credential, and at the pipeline application
     the two are the ECHO application's same reading of its counter
     ([AppEcho.echo_taint_of_sup]) -- because the claim is echo's. *)
  Lemma pipe_al_kill (c : app_fixed app_pipe) (r : app_names app_pipe) :
    AppInv.app_sup_raw (app_pred app_pipe c) r ⊢ □ app_kill app_pipe c.
  Proof using .
    rewrite /app_kill.
    cbn [app_pipe app_fixed app_names app_pred app_ifc pipe_ifc ai_kill]
      in c, r |- *.
    iIntros "#Hs". iModIntro. rewrite /pipe_kill.
    iApply (pipe_taint_of_sup (pgn_cl c) r with "Hs").
  Qed.

  Lemma pipe_al_sup (c : app_fixed app_pipe) (r : app_names app_pipe) :
    AppInv.app_sup_raw (app_pred app_pipe c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_pipe c k h H ==∗
             app_cons app_pipe c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons.
    cbn [app_pipe app_fixed app_names app_ifc pipe_ifc ai_cons pipe_cons]
      in c, r |- *.
    iIntros "#Hs".
    iDestruct (pipe_taint_of_sup (pgn_cl c) r with "Hs") as "#Ht".
    iIntros "!>" (k h H ev) "Ho".
    iApply (pecl'_sup c (fun _ => None) adm_echo pipes_lm_echo_laws k h H ev with "Ht Ho").
  Qed.

  Lemma pipe_al_R0 (c : app_fixed app_pipe) :
    app_cl app_pipe c ⊢ |==> app_R app_pipe c [].
  Proof using .
    cbn [app_pipe app_fixed app_cl app_R] in c |- *.
    iIntros "Hc". iModIntro. rewrite /pipe_R.
    iApply (pipesE_led_init c with "Hc").
  Qed.

  Lemma pipe_al_pow (c : app_fixed app_pipe) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_pipe c h ==∗
      app_R app_pipe c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_pipe c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            app_turn app_pipe c (S (obs_boots h))).
  Proof using .
    intros _.
    rewrite /app_cons.
    cbn [app_pipe app_fixed app_R pipe_R app_ifc pipe_ifc ai_cons pipe_cons
         app_turn pipe_turn] in c |- *.
    iApply (pipesE_led_pow c h on).
  Qed.

  (* the two UART arms, at the theorem's literal shape *)
  Lemma pipe_al_tx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_pipe) (r : app_names app_pipe)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_pipe) (app_pred app_pipe c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
           (ho : list mobs) (H : LogEntryDefs.cons_hist),
           ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
           ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
           ⌜u_wire u = u_out u⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
           ⌜ho `prefix_of` h⌝ -∗
           ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
           (if i is Uart0 then app_cons app_pipe c (S gen_id) ho H else emp) -∗
           uart_ghosts γ u' -∗ app_R app_pipe c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           (if i is Uart0 then app_cons app_pipe c (S gen_id) ho H else emp) ∗
           uart_ghosts γ u' ∗ app_R app_pipe c (h ++ [ObsUartOut i b])%list).
  Proof using .
    intros _ _.
    rewrite /app_cons.
    cbn [app_pipe app_fixed app_R pipe_R app_ifc pipe_ifc ai_cons pipe_cons]
      in c |- *.
    iIntros "!>" (h b u u' ho H)
      "%Htxp %Hlp %Hsh %Hwi %Hwo %Hbt %Hpo %Hacc Ho Hg Hled".
    iAssert (|==> (if i is Uart0 then peclE c (S gen_id) ho H else emp)
                  ∗ (echo_taint (pgn_cl c)
                     ∨ ⌜i = Uart0 ->
                        lm_good_out pipes_lmE tt (open_seg h ++ [ObsUartOut i b])⌝))%I
      with "[Ho]" as ">[Ho Hgo]".
    { destruct i; last first.
      { iModIntro. iFrame "Ho". iRight. iPureIntro. discriminate. }
      assert (Hins : ins (open_seg h ++ [ObsUartOut Uart0 b])
                     = ins (open_seg h))
        by (by rewrite ins_app ins_out app_nil_r).
      assert (Hpre : obs_wire Uart0 (open_seg h ++ [ObsUartOut Uart0 b])
                     `prefix_of` uart_acc u).
      { rewrite obs_wire_app Hwi Hwo.
        replace (obs_wire Uart0 [ObsUartOut Uart0 b]) with [b] by reflexivity.
        rewrite -(DevModel.uart_tx_pop_acc u b u' Htxp) /DevModel.uart_acc
                (DevModel.uart_tx_pop_out u b u' Htxp).
        exists (u_tx u'). by rewrite -app_assoc. }
      assert (Hne : obs_wire Uart0 (open_seg h ++ [ObsUartOut Uart0 b]) <> []).
      { rewrite obs_wire_app.
        replace (obs_wire Uart0 [ObsUartOut Uart0 b]) with [b] by reflexivity.
        intros Hz. apply (f_equal length) in Hz.
        rewrite length_app in Hz. cbn [length] in Hz. lia. }
      iDestruct (pecl'_drain c (fun _ => None) adm_echo pipes_lm_echo_laws (S gen_id) h ho H
                   (open_seg h ++ [ObsUartOut Uart0 b])
                   Hsh Hbt Hpo Hins ltac:(rewrite Hacc; exact Hpre) Hne
                   with "Ho") as "[Ho Hgo]".
      iModIntro. iFrame "Ho".
      iDestruct "Hgo" as "[HT | %Hg]"; [by iLeft |].
      iRight. iPureIntro. by intros _. }
    iMod (pipesE_led_tx c h i b Hsh with "Hgo Hled") as "Hled".
    iModIntro. iFrame "Ho Hg Hled".
  Qed.

  Lemma pipe_al_rx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_pipe) (r : app_names app_pipe)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_pipe) (app_pred app_pipe c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
           ⌜obs_boots h = S gen_id⌝ -∗
           uart_ghosts γ u' -∗ app_R app_pipe c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_pipe c (h ++ [ObsUartIn i b])%list ∗
           app_tag app_pipe c (h ++ [ObsUartIn i b])%list).
  Proof using .
    intros _ _. rewrite /app_tag.
    cbn [app_pipe app_fixed app_R pipe_R app_ifc pipe_ifc ai_tag] in c |- *.
    iIntros "!>" (h b u u') "_ %Hsh _ Hg Hled".
    iMod (pipesE_led_rx c h i b Hsh with "Hled") as "[Hled Htag]".
    iModIntro. iFrame "Hg Hled". rewrite /pipe_tag /ptagE.
    iSplitR; [| iExact "Htag"].
    iPureIntro. eapply trace_shape_snoc; [exact Hsh | reflexivity].
  Qed.

  (* ---- the transport, with the first process's boot resource.  It is the
         ECHO application's: the claim and the boot resource are echo's
         names. ---- *)
  Lemma pipe_al_xfer (c : app_fixed app_pipe) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred app_pipe c) (app_boot app_pipe c k).
  Proof using .
    cbn [app_pipe app_fixed app_names app_pred app_boot] in c |- *.
    rewrite /app_xfer_boot_raw. iApply pipe_xfer_boot.
  Qed.

  (* ---- the echo shift ---- *)
  Lemma pipe_al_echo (HR : riscvGS Σ) (c : app_fixed app_pipe) :
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_pipe c ->
    ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HR GEN XI.
  Proof using .
    cbn [app_pipe app_fixed app_ifc] in c |- *.
    intros Hiface.
    iApply (PipesLinks.pipes_happ_echo c (HRg := HR)).
    - rewrite /riscv_cons_res Hiface. by cbn [pipe_ifc ai_cons pipe_cons].
    - rewrite /riscv_rx_tag Hiface. by cbn [pipe_ifc ai_tag pipe_tag].
  Qed.

  (* ---- era 0's claim at the literal image: the ECHO application's, since
         the claim is echo's. ---- *)
  Lemma pipe_Happ_init (gst : gstate) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov ->
    fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_pipe,
      ⊢ |==> ∃ r : app_names app_pipe,
          app_pred app_pipe c r (abs_view (fss_inodes (FsDurImg.img_state
             (fs_blocks (v_disk (gst.(gdev).(dvirtio)))) sb nib))).
  Proof using .
    intros Himg Hdk Hsb Hcov c.
    cbn [app_pipe app_fixed app_names app_pred] in c |- *.
    exact (pipe_init_img (pgn_cl c) _ XV6_DISK_BYTES sb nib cov
             Himg Hdk Hsb Hcov).
  Qed.

  (* ---- ANTI-VACUITY: the CLAIM EQUATION the program tier takes as a
         parameter ([UInitConsPipe]'s [file_app = MkAppcfg echo_names
         (pipe_pred γ) r]) IS the one [al_programs] hands over at this
         record, by conversion and not by a bridge.  Three [reflexivity]s,
         and if one of them ever needs a tactic a field has moved. ---- *)
  Lemma pipe_app_pred_eq (c : app_fixed app_pipe) :
    app_pred app_pipe c = pipe_pred (pgn_cl c).
  Proof using . reflexivity. Qed.

  Lemma pipe_app_names_eq : app_names app_pipe = echo_names.
  Proof using . reflexivity. Qed.

  Lemma pipe_app_boot_eq (c : app_fixed app_pipe) (k : nat) :
    app_boot app_pipe c k = pipe_boot (pgn_cl c) k.
  Proof using . reflexivity. Qed.

  (* ---- the conclusion's one ingredient ---- *)
  Lemma pipe_Hphi_R (c : app_fixed app_pipe) (gst : gstate) (h : list mobs) :
    app_R app_pipe c h ⊢ ⌜app_phi app_pipe gst h⌝.
  Proof using .
    cbn [app_pipe app_fixed app_R app_phi] in c |- *.
    rewrite /pipe_R /pipe_phi. iIntros "H".
    iApply (pipesE_led_phi c h with "H").
  Qed.

End PipeApp.

(* ====================================================================== *)
(*  3.  THE LAWS, AS THE CLASS INSTANCE                                    *)
(*                                                                        *)
(*  Every field but [al_programs] is one of the lemmas above.              *)
(*  [al_programs] -- the first process's exec bundle -- is lane            *)
(*  SH-PIPE-ROUND's and is a SECTION HYPOTHESIS here rather than an        *)
(*  [Admitted] lemma, so that nothing in this file is admitted and the     *)
(*  instance simply does not exist until that lane lands.                  *)
(* ====================================================================== *)
Section PipeLaws.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !pipeOutG Σ}.

  (* lane SH-PIPE-ROUND's field, verbatim from [App.xv6_app_laws] *)
  Context (Hprog :
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_pipe (Σ := Σ)))
           (r : app_names (app_pipe (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_pipe) (app_pred app_pipe c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_pipe c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_pipe c (S gen_id) r -∗
        app_turn app_pipe c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0).

  Global Instance pipe_laws : App.xv6_app_laws (app_pipe (Σ := Σ)).
  Proof using Hprog ufdG0.
    split.
    - exact pipe_al_birth.
    - exact pipe_al_Rt.
    - exact pipe_al_kill.
    - exact pipe_al_sup.
    - exact pipe_al_R0.
    - exact pipe_al_pow.
    - intros HR GEN HF c r i γ Heq Huart.
      exact (pipe_al_tx (HF := HF) HR GEN c r i γ Heq Huart).
    - intros HR GEN HF c r i γ Heq Huart.
      exact (pipe_al_rx (HF := HF) HR GEN c r i γ Heq Huart).
    - exact pipe_al_xfer.
    - exact Hprog.
    - exact pipe_al_echo.
  Qed.
End PipeLaws.
