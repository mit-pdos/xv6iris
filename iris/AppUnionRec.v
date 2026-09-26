(* ===================================================================== *)
(*  AppUnionRec.v -- THE UNION APPLICATION'S RECORD (cut C9g; design:     *)
(*  claude-notes/design/union.md section 4).                              *)
(*                                                                        *)
(*  [AppFileRec.v] at the union: the conclusion, the record [app_union]   *)
(*  and [App.xv6_app_laws] with every field but [al_programs] discharged. *)
(*  The claim on the file-system view, the boot resource and the          *)
(*  transport are the FILE application's ([AppFile.file_pred] /           *)
(*  [file_boot] / [file_xfer_boot]); what is the union's own is the       *)
(*  console half: the ledger [UnionOut.union_led], the tag [utag], the    *)
(*  claim [ucl] (the file lines' generic claim beside the N-writer open   *)
(*  round) and the conclusion [UnionOutPure.union_phi].                   *)
(*                                                                        *)
(*  [al_programs] is a SECTION HYPOTHESIS here, as at [AppFileRec]; it is *)
(*  discharged by [UInitUnion.union_Hinit_boot].                          *)
(* ===================================================================== *)
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
Require Import LineModel.
Require Import FileState.
Require Import FileDisc.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import UnionDisc.
Require Import UnionOutPure.
Require Import UnionOut.
Require Import UnionLinks.
Local Open Scope Z_scope.

Local Notation U := ulmG.

(* ====================================================================== *)
(*  1.  THE CONCLUSION                                                     *)
(*                                                                        *)
(*  [UnionOutPure.union_phi] VERBATIM; it reads the trace alone.           *)
(* ====================================================================== *)
Definition union_phi : gstate -> list mobs -> Prop :=
  fun _ h => UnionOutPure.union_phi h.

Section UnionApp.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  (* ---- the four fields that are resources ---- *)

  Definition union_R (c : union_gn) (h : list mobs) : iProp Σ := union_led c h.

  Global Instance union_R_timeless c h : Timeless (union_R c h).
  Proof using . rewrite /union_R. apply _. Qed.

  Definition union_tag (c : union_gn) (h : list mobs) : iProp Σ := utag c h.

  Global Instance union_tag_persistent c h : Persistent (union_tag c h).
  Proof using . rewrite /union_tag. apply _. Qed.
  Global Instance union_tag_timeless c h : Timeless (union_tag c h).
  Proof using . rewrite /union_tag. apply _. Qed.

  Definition union_kill (c : union_gn) : iProp Σ := file_taint (fgn_cl (ugn_file c)).

  Global Instance union_kill_persistent c : Persistent (union_kill c).
  Proof using . rewrite /union_kill. apply _. Qed.
  Global Instance union_kill_timeless c : Timeless (union_kill c).
  Proof using . rewrite /union_kill. apply _. Qed.

  Definition union_cons (c : union_gn)
    : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ := ucl c.

  Global Instance union_cons_timeless c k h H : Timeless (union_cons c k h H).
  Proof using . rewrite /union_cons. apply _. Qed.

  (* THE INTERFACE'S LICENCE LAW: a tainted claim answers any boundary
     event out of its taint *)
  Lemma union_cons_lic (c : union_gn) :
    union_kill c ⊢
      □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
           (ev : ConsLog.cons_ev),
           union_cons c k h H ==∗ union_cons c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /union_cons /union_kill. iIntros "#Ht !>" (k h H ev) "Ho".
    iApply (peclV_sup (ugn_pipe c) U (ucparams c) ∅ (uwa c) k h H ev with "Ht Ho").
  Qed.

  Definition union_ifc (c : union_gn) : app_iface Σ :=
    MkAppIface (union_tag c) (union_tag_persistent c) (union_tag_timeless c)
               (union_kill c) (union_kill_persistent c) (union_kill_timeless c)
               (union_cons c) (union_cons_timeless c) (union_cons_lic c)
               (* the seccomp universe's era credential (S2); none yet *)
               wild_none (@wild_none_persistent Σ) (@wild_none_timeless Σ)
               (wild_none_lic (union_cons c)).

  Definition union_turn (c : union_gn) : nat -> iProp Σ := fturn (ugn_file c).

  (* ====================================================================== *)
  (*  2.  THE RECORD                                                        *)
  (* ====================================================================== *)
  Definition app_union : xv6_app Σ :=
    MkApp union_gn union_cl_all file_names
          (fun c => file_pred (fgn_cl (ugn_file c)))
          (fun c k r => file_boot (fgn_cl (ugn_file c)) k r)
          union_R union_ifc union_turn union_phi.

  (* ---- the birth step ---- *)
  Lemma union_al_birth : ⊢ |==> ∃ c : app_fixed app_union, app_cl app_union c.
  Proof using . cbn [app_union app_fixed app_cl]. exact union_birth_all. Qed.

  Lemma union_al_Rt (c : app_fixed app_union) (h : list mobs) :
    Timeless (app_R app_union c h).
  Proof using . cbn [app_union app_fixed app_R] in c |- *. apply _. Qed.

  (* the supply buys the kill credential: the file claim's reading *)
  Lemma union_al_kill (c : app_fixed app_union) (r : app_names app_union) :
    AppInv.app_sup_raw (app_pred app_union c) r ⊢ □ app_kill app_union c.
  Proof using .
    rewrite /app_kill.
    cbn [app_union app_fixed app_names app_pred app_ifc union_ifc ai_kill]
      in c, r |- *.
    iIntros "#Hs". iModIntro. rewrite /union_kill.
    iApply (file_taint_of_sup (fgn_cl (ugn_file c)) r with "Hs").
  Qed.

  Lemma union_al_sup (c : app_fixed app_union) (r : app_names app_union) :
    AppInv.app_sup_raw (app_pred app_union c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_union c k h H ==∗
             app_cons app_union c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons.
    cbn [app_union app_fixed app_names app_ifc union_ifc ai_cons union_cons]
      in c, r |- *.
    iIntros "#Hs".
    iDestruct (file_taint_of_sup (fgn_cl (ugn_file c)) r with "Hs") as "#Ht".
    iIntros "!>" (k h H ev) "Ho".
    iApply (peclV_sup (ugn_pipe c) U (ucparams c) ∅ (uwa c) k h H ev with "Ht Ho").
  Qed.

  Lemma union_al_R0 (c : app_fixed app_union) :
    app_cl app_union c ⊢ |==> app_R app_union c [].
  Proof using .
    cbn [app_union app_fixed app_cl app_R] in c |- *.
    iIntros "Hc". iModIntro. rewrite /union_R.
    iApply (union_led_init c with "Hc").
  Qed.

  Lemma union_al_pow (c : app_fixed app_union) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_union c h ==∗
      app_R app_union c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_union c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            app_turn app_union c (S (obs_boots h))).
  Proof using .
    intros _.
    rewrite /app_cons.
    cbn [app_union app_fixed app_R union_R app_ifc union_ifc ai_cons union_cons
         app_turn union_turn] in c |- *.
    iIntros "H". iApply (union_led_pow c h on with "H").
  Qed.

  (* the two UART arms, at the theorem's literal shape *)
  Lemma union_al_tx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_union) (r : app_names app_union)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_union) (app_pred app_union c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
           (ho : list mobs) (H : LogEntryDefs.cons_hist),
           ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
           ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
           ⌜u_wire u = u_out u⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
           ⌜ho `prefix_of` h⌝ -∗
           ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
           (if i is Uart0 then app_cons app_union c (S gen_id) ho H else emp) -∗
           uart_ghosts γ u' -∗ app_R app_union c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           (if i is Uart0 then app_cons app_union c (S gen_id) ho H else emp) ∗
           uart_ghosts γ u' ∗ app_R app_union c (h ++ [ObsUartOut i b])%list).
  Proof using .
    intros _ _.
    rewrite /app_cons.
    cbn [app_union app_fixed app_R union_R app_ifc union_ifc ai_cons union_cons]
      in c |- *.
    iIntros "!>" (h b u u' ho H)
      "%Htxp %Hlp %Hsh %Hwi %Hwo %Hbt %Hpo %Hacc Ho Hg Hled".
    iAssert (|==> (if i is Uart0 then ucl c (S gen_id) ho H else emp)
                  ∗ (file_taint (fgn_cl (ugn_file c))
                     ∨ (match i with
                        | Uart0 => ∃ (s0 : fstate) (vf : file_era),
                                     ⌜lm_good_out U s0
                                        (open_seg h ++ [ObsUartOut Uart0 b])⌝
                                     ∗ f0_typed (ugn_file c) s0
                                     ∗ file_era_pin (ugn_file c) (obs_boots h) vf
                                     ∗ f0_lb vf s0
                        | _ => True
                        end)))%I with "[Ho]" as ">[Ho Hgo]".
    { destruct i; last first.
      { iModIntro. iFrame "Ho". by iRight. }
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
      iDestruct (ucl_drain c (S gen_id) h ho H
                   (open_seg h ++ [ObsUartOut Uart0 b])
                   Hsh Hbt Hpo Hins ltac:(rewrite Hacc; exact Hpre) Hne
                   with "Ho") as "[Ho Hgo]".
      iModIntro. iFrame "Ho".
      rewrite /udrain_ret.
      iDestruct "Hgo" as "[HT | Hgo]"; [by iLeft |].
      iDestruct "Hgo" as (s0 vf) "(%Hg & %Hfok & #Hty & #Hfp & #Hlb)".
      iRight. iExists s0, vf. rewrite Hbt. iFrame "Hty Hfp Hlb".
      by iPureIntro. }
    iMod (union_led_tx c h i b Hsh with "Hgo Hled") as "Hled".
    iModIntro. iFrame "Ho Hg Hled".
  Qed.

  Lemma union_al_rx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_union) (r : app_names app_union)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_union) (app_pred app_union c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
           ⌜obs_boots h = S gen_id⌝ -∗
           uart_ghosts γ u' -∗ app_R app_union c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_union c (h ++ [ObsUartIn i b])%list ∗
           app_tag app_union c (h ++ [ObsUartIn i b])%list).
  Proof using .
    intros _ _. rewrite /app_tag.
    cbn [app_union app_fixed app_R union_R app_ifc union_ifc ai_tag] in c |- *.
    iIntros "!>" (h b u u') "_ %Hsh _ Hg Hled".
    iMod (union_led_rx c h i b Hsh with "Hled") as "[Hled Htag]".
    iModIntro. iFrame "Hg Hled". rewrite /union_tag. iExact "Htag".
  Qed.

  (* ---- the transport, with the first process's boot resource: the
         file application's ---- *)
  Lemma union_al_xfer (c : app_fixed app_union) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred app_union c) (app_boot app_union c k).
  Proof using .
    cbn [app_union app_fixed app_names app_pred app_boot] in c |- *.
    rewrite /app_xfer_boot_raw. iApply file_xfer_boot.
  Qed.

  (* ---- the echo shift ---- *)
  Lemma union_al_echo (HR : riscvGS Σ) (c : app_fixed app_union) :
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_union c ->
    ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HR GEN XI.
  Proof using .
    cbn [app_union app_fixed app_ifc] in c |- *.
    intros Hiface.
    assert (Hc : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = ucl c)
      by (rewrite /riscv_cons_res Hiface; by cbn [union_ifc ai_cons union_cons]).
    assert (Ht : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = utag c)
      by (rewrite /riscv_rx_tag Hiface; by cbn [union_ifc ai_tag union_tag]).
    iApply (UnionLinks.union_happ_echo c (HRg := HR) Hc Ht).
  Qed.

  (* ---- era 0's claim at the literal image: the file application's ---- *)
  Lemma union_Happ_init (gst : gstate) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov ->
    fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_union,
      ⊢ |==> ∃ r : app_names app_union,
          app_pred app_union c r (abs_view (fss_inodes (FsDurImg.img_state
             (fs_blocks (v_disk (gst.(gdev).(dvirtio)))) sb nib))).
  Proof using .
    intros Himg Hdk Hsb Hcov c.
    cbn [app_union app_fixed app_names app_pred] in c |- *.
    exact (file_init_img (fgn_cl (ugn_file c)) _ XV6_DISK_BYTES sb nib cov
             Himg Hdk Hsb Hcov).
  Qed.

  (* ---- the conclusion's one ingredient ---- *)
  Lemma union_Hphi_R (c : app_fixed app_union) (gst : gstate) (h : list mobs) :
    app_R app_union c h ⊢ ⌜app_phi app_union gst h⌝.
  Proof using .
    cbn [app_union app_fixed app_R app_phi] in c |- *.
    rewrite /union_R /union_phi. iIntros "H".
    iApply (union_led_phi c h with "H").
  Qed.

End UnionApp.

(* ====================================================================== *)
(*  3.  THE LAWS, AS THE CLASS INSTANCE                                    *)
(* ====================================================================== *)
Section UnionLaws.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  (* [App.al_programs] at this record, verbatim from the class *)
  Context (Hprog :
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_union (Σ := Σ)))
           (r : app_names (app_union (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_union) (app_pred app_union c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_union c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_union c (S gen_id) r -∗
        app_turn app_union c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0).

  Global Instance union_laws : App.xv6_app_laws (app_union (Σ := Σ)).
  Proof using Hprog ufdG0.
    split.
    - exact union_al_birth.
    - exact union_al_Rt.
    - exact union_al_kill.
    - exact union_al_sup.
    - exact union_al_R0.
    - exact union_al_pow.
    - intros HR GEN HF c r i γ Heq Huart.
      exact (union_al_tx (HF := HF) HR GEN c r i γ Heq Huart).
    - intros HR GEN HF c r i γ Heq Huart.
      exact (union_al_rx (HF := HF) HR GEN c r i γ Heq Huart).
    - exact union_al_xfer.
    - exact Hprog.
    - exact union_al_echo.
  Qed.
End UnionLaws.
