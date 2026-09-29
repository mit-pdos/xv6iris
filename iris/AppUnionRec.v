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
(*  round) and the conclusion [UnionOutPure.union_phi_sync].              *)
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
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionOutPure.
Require Import UnionOut.
Require Import UnionLinks.
Require UnionAdm.
Local Open Scope Z_scope.

Local Notation U := ulmG.

(* ====================================================================== *)
(*  1.  THE CONCLUSION                                                     *)
(*                                                                        *)
(*  [UnionOutPure.union_phi_sync] VERBATIM; it reads the trace alone.      *)
(* ====================================================================== *)
Definition union_phi : gstate -> list mobs -> Prop :=
  fun _ h => UnionOutPure.union_phi_sync h.

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
    iApply (ucl_sup c k h H ev with "Ht Ho").
  Qed.

  (* THE WILD LICENCE (seccomp design 10.2): the era's wild token steps
     its own era's claim by the two process events *)
  Lemma union_wild_lic (c : union_gn) (k : nat) :
    usecc_tok c k ⊢
      □ (∀ (h : list mobs) (H : LogEntryDefs.cons_hist) (ev : ConsLog.cons_ev),
           ⌜ConsLog.wild_ev ev⌝ -∗ ⌜ConsLog.cons_ev_ok H ev⌝ -∗
           union_cons c k h H ==∗ union_cons c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /union_cons. iIntros "#Htok".
    iDestruct (ucl_wild_lic c k with "Htok") as "#Hl".
    iIntros "!>" (h H ev) "%Hw %Hev Ho".
    iApply ("Hl" with "[%] [%] Ho"); [| exact Hev].
    destruct ev; cbn [ConsLog.wild_ev] in Hw; try done;
      [left; by eexists | right; by eexists].
  Qed.

  Definition union_ifc (c : union_gn) : app_iface Σ :=
    MkAppIface (union_tag c) (union_tag_persistent c) (union_tag_timeless c)
               (union_kill c) (union_kill_persistent c) (union_kill_timeless c)
               (union_cons c) (union_cons_timeless c) (union_cons_lic c)
               (* the seccomp universe's era credential: the era's wild
                  token (seccomp design 10.1) *)
               (usecc_tok c) (usecc_tok_persistent c) (usecc_tok_timeless c)
               (union_wild_lic c)
               (* the tokenless masked READER's credential: the era's token
                  at its line, and the reader's position there (seccomp
                  design 10.12, lane S5b) *)
               (urdwild c) (urdwild_persistent c) (urdwild_timeless c).

  (* THE ERA'S TURN IN ITS FOUR STAGES ([UnionOut.uturn] &c., sync SY3-A3bc) *)
  Definition union_turn (c : union_gn) : nat -> iProp Σ := uturn c.

  (* THE BOOT RESOURCE: the file application's, and the deed holder's share
     of the running claim's round position, founded at the length of the
     copy's line list the era's record pins (or the taint) *)
  Definition union_boot (c : union_gn) (k : nat) (r : file_names) : iProp Σ :=
    (∃ s : dst, file_boot_at (fgn_cl (ugn_file c)) k r s
     ∗ (file_taint (fgn_cl (ugn_file c))
        ∨ ∃ (vf : file_era) (ls : list fl_line),
            file_era_pin (ugn_file c) k vf ∗ fcp_pin vf ls ∗ fposh r (length ls)
            (* ...AND THE BOOT FACT at the deed's state (sync SY3-A4): the
               copy's files admissible after the era's floor's last record,
               which /init files beside the boot state ([FileOut.f0_bt]) *)
            ∗ fl_lb (fgn_cl (ugn_file c)) ls
            ∗ ⌜UnionAdm.uadm ls (slast (fe_floor vf)) (dst_content s)⌝
            (* ...and the deed's typed witness, out of the later *)
            ∗ f_typed (fgn_cl (ugn_file c)) s
            (* ...and the running claim's registration at the era (sync
               SY3-A4: how the deed's holder knows the record a sync hook
               is fired at is its own) *)
            ∗ run_reg (fgn_cl (ugn_file c)) k (fn_pos r) (fn_deed r)))%I.

  (* ====================================================================== *)
  (*  2.  THE RECORD                                                        *)
  (* ====================================================================== *)
  Definition app_union : xv6_app Σ :=
    MkApp union_gn union_cl_all file_names
          (fun c => file_pred (fgn_cl (ugn_file c)))
          union_boot
          union_R union_ifc
          (* the turn in its four stages (sync SY3-A3bc) *)
          uturn uturn' uturn'' uturn_i
          (* the birth's crash-slot part, what it keeps of the machine's
             names, the era's and the durable copy's record predicates, the
             token and the hook family (sync SY3-A3bc) *)
          union_cls union_born
          (fun _ k r => fn_era r = k) (fun _ r => fn_role r = true)
          (fun c k => union_tk (fgn_cl (ugn_file c)) k)
          (fun c k Q => union_hk file_pred (fgn_cl (ugn_file c)) k Q)
          union_phi.

  (* ---- the birth step ---- *)
  Lemma union_al_birth (γd γsw γreg γst : gname) :
    ⊢ |==> ∃ c : app_fixed app_union,
        ⌜app_born app_union γd γsw γreg γst c⌝ ∗
        app_cls app_union c ∗ app_cl app_union c.
  Proof using .
    cbn [app_union app_fixed app_born app_cls app_cl].
    iMod (union_birth_all γst) as (ug) "(%Hst & Hs & Hc)".
    iModIntro. iExists ug. iSplitR; [iPureIntro; exact Hst |].
    iFrame "Hs Hc".
  Qed.

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
    iApply (ucl_sup c k h H ev with "Ht Ho").
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
                  ∗ (match i with
                     | Uart0 => udrain_ret c (obs_boots h)
                                  (open_seg h ++ [ObsUartOut Uart0 b])
                     | _ => True
                     end))%I with "[Ho]" as ">[Ho Hgo]".
    { destruct i; last first.
      { iModIntro. by iFrame "Ho". }
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
      iModIntro. iFrame "Ho". rewrite Hbt. iExact "Hgo". }
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

  (* ---- THE POWER-ON TRANSPORT (sync SY3-A3bc): the file application's
         re-base ([AppFile.file_xfer_boot]) at the turn the on-arm yielded,
         the copy's line list pinned at the era's record ---- *)
  Lemma union_al_xfer (HSt : mono_natG Σ) (c : app_fixed app_union) (gen : nat)
      (γst : gname) :
    fa_st = HSt -> ff_st (fgn_cl (ugn_file c)) = γst ->
    ⊢ app_xfer_boot_raw HSt (app_pred app_union c) (app_okc app_union c)
        (app_boot app_union c (S gen))
        (app_turn app_union c (S gen)) (app_turn' app_union c (S gen)) γst gen.
  Proof using .
    intros <- <-.
    cbn [app_union app_fixed app_names app_pred app_boot app_turn app_turn' app_okc]
      in c |- *.
    rewrite /app_xfer_boot_raw.
    iIntros "!>" (r av n ->) "Hsa %Hr Htn Hp".
    iDestruct "Htn" as "(Hft & %γ & %vf & #Hreg & Hγ & #Hpin & Hcp & #Hbase & #HF)".
    iMod (file_xfer_boot (fgn_cl (ugn_file c)) gen r av γ (fe_base vf) (fe_floor vf) Hr
            with "Hsa Hγ Hreg Hbase HF Hp")
      as ">(Hsa & Hs & %r' & %ls & %Hr' & Hr'p & Hb & #Hls & Hrest)".
    iMod (fcp_set vf ls with "Hcp") as "#Hcp".
    iModIntro. iModIntro. iFrame "Hsa".
    iDestruct "Hrest" as "[#HT | (Hpos & Htk & #Hty & #Hrr & %Ls_c & _ & _ & %HFb)]".
    { iSplitL "Hft".
      { rewrite /uturn'. iFrame "Hft". iExists vf, ls. iFrame "Hpin Hcp Hls". by iLeft. }
      iExists (fn_with r γ (S gen) true), r'.
      iSplitR; [iPureIntro; by destruct r |]. iFrame "Hs Hr'p".
      rewrite /union_boot. iExists (fcontent_of av). iFrame "Hb". by iLeft. }
    iDestruct "Htk" as (γ' Ls) "(#Hreg' & Hq & #Hcm)".
    iDestruct (sl_lb_get with "Hq") as "#Hql".
    iSplitL "Hft Hq".
    { rewrite /uturn'. iFrame "Hft". iExists vf, ls. iFrame "Hpin Hcp Hls".
      iRight. iExists γ', Ls. iFrame "Hreg' Hq Hql Hcm". }
    iExists (fn_with r γ (S gen) true), r'.
    iSplitR; [iPureIntro; by destruct r |]. iFrame "Hs Hr'p".
    rewrite /union_boot. iExists (fcontent_of av). iFrame "Hb". iRight.
    iExists vf, ls. iFrame "Hpin Hcp Hpos". iSplitR; [iExact "Hls" |].
    iSplitR; [iPureIntro; exact (proj2 HFb) |]. iSplitR; [iExact "Hty" |]. iExact "Hrr".
  Qed.

  (* ---- THE MERGE (sync SY3-A3bc): the file application's, the started
         auth read at the union's copy of the started counter's name ---- *)
  Lemma union_al_merge `{!riscvFixedGS Σ} (c : app_fixed app_union) (k : nat) :
    (forall n : nat, start_auth n ⊣⊢ sync_st_auth (fgn_cl (ugn_file c)) n) ->
    ⊢ app_merge_raw (app_pred app_union c) (app_ok app_union c (S k)) (app_okc app_union c)
        (app_tk app_union c k) k.
  Proof using .
    intros Hst.
    cbn [app_union app_fixed app_names app_pred app_ok app_okc app_tk] in c |- *.
    exact (file_merge (fgn_cl (ugn_file c)) k Hst).
  Qed.

  (* ---- THE SYNC RUNNER: the hook IS the runner's body ---- *)
  Lemma union_al_sync_run `{!riscvGS Σ, !fsTopG Σ} (c : app_fixed app_union) (k : nat) :
    ⊢ app_sync_run_raw (app_pred app_union c) (app_ok app_union c (S k))
        (app_okc app_union c) (app_tk app_union c k) (app_hk app_union c k).
  Proof using .
    cbn [app_union app_fixed app_names app_pred app_ok app_okc app_tk app_hk] in c |- *.
    rewrite /app_sync_run_raw.
    iIntros "!>" (Q gt I r r') "%Hr %Hr' %Hrc HQ Hh Hn Hp HT".
    iMod ("HQ" $! I r r' Hr Hr' Hrc with "Hn Hp HT") as ">(Hn & Hp & HT & HQ)".
    iModIntro. iFrame "Hh Hn Hp HT HQ".
  Qed.

  (* ---- the era's record predicate off the boot resource ---- *)
  Lemma union_al_boot_ok (c : app_fixed app_union) (k : nat) (r : app_names app_union) :
    app_boot app_union c k r ⊢ ⌜app_ok app_union c k r⌝.
  Proof using .
    cbn [app_union app_fixed app_names app_boot app_ok] in c, r |- *.
    rewrite /union_boot /file_boot_at. iIntros "(%s & (_ & %H & _) & _)". by iPureIntro.
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

  (* ---- era 0's durable copy at the literal image, out of the birth's
         crash-slot part: the file application's ---- *)
  Lemma union_Happ_init (gst : gstate) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov ->
    fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_union,
      app_cls app_union c ⊢ |==> ∃ r : app_names app_union,
          ⌜app_okc app_union c r⌝ ∗
          app_pred app_union c r (abs_view (fss_inodes (FsDurImg.img_state
             (fs_blocks (v_disk (gst.(gdev).(dvirtio)))) sb nib))).
  Proof using .
    intros Himg Hdk Hsb Hcov c.
    cbn [app_union app_fixed app_names app_pred app_cls app_okc] in c |- *.
    rewrite /union_cls. iIntros "(%γ0 & #Hreg & Hh & Hcm & Hhi & Hra & #Hlb)".
    iApply (file_init_img (fgn_cl (ugn_file c)) _ XV6_DISK_BYTES sb nib cov γ0
              Himg Hdk Hsb Hcov with "Hreg Hh Hcm Hhi Hra Hlb").
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
      @riscv_sync_hook Σ (@riscv_fixedGS Σ HR) = app_hk app_union c ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_union c (S gen_id) r -∗
        app_iturn app_union c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0).

  (* THE FILE APPLICATION'S STARTED-COUNTER CAMERA IS THE MACHINE'S (sync
     SY3-A3bc, ruling (i)): [UUnionBootAdequacy] builds the instance so *)
  Context (Hfa : fa_st = riscv_pre_genGS).

  Global Instance union_laws : App.xv6_app_laws (app_union (Σ := Σ)).
  Proof using Hfa Hprog ufdG0.
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
    - intros c gen γd γsw γreg γst Hborn.
      exact (union_al_xfer riscv_pre_genGS c gen γst Hfa Hborn).
    - exact Hprog.
    - exact union_al_echo.
    - (* the founding: the token out of the returned turn *)
      intros c k. cbn [app_union app_turn'' app_tk app_iturn]. iIntros "H".
      iApply (union_found c k with "H").
    - intros c h. cbn [app_union app_R app_turn' app_turn'']. rewrite /union_R.
      iIntros "HR HT". iApply (union_led_back c h with "HR HT").
    - exact union_al_boot_ok.
    - intros HR c k Hgen Hborn. apply union_al_merge.
      intros n. rewrite /start_auth /sync_st_auth Hgen -Hfa.
      cbn [app_union app_born union_born] in Hborn. rewrite Hborn. reflexivity.
    - intros HR c k. exact (union_al_sync_run c k).
  Qed.
End UnionLaws.
