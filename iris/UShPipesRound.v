(* ===================================================================== *)
(* UShPipesRound.v -- THE PIPELINE ERA'S ROUND AT THE N-STAGE MODEL      *)
(* [PipesDisc.pipes_lmE] (cut C8).                                        *)
(*                                                                        *)
(* The loop's body at the era's two line shapes:                          *)
(*   - [echo ws]: the echo child at the generic record                    *)
(*     ([UShEchoPay.sh_exec_sup_echo_wq_holds_at_D] at                    *)
(*     [PipesStageInst.pipes_stage_inst_at]);                             *)
(*   - [echo ws | cat | ... | cat]: the pipe child                        *)
(*     ([UShPipesLaw.pipes_child_law], at [PipesCut.pipes_lp]).           *)
(* The era runs at the widened credential [UkShPipesFork.pterm_wcN]: the  *)
(*  record's own credential at every index, or a terminal or committed    *)
(*  round's shape below index 3.                                          *)
(*                                                                        *)
(*  SECTION MAP.                                                          *)
(*   S0  the era's PURE discipline readings -- [UkSh]'s section           *)
(*       hypotheses at [lm_disc_input pipes_lmE] and                      *)
(*       [PipesUline.ush_line_pipes].                                     *)
(*   S1  the families, the echo arm's laws, sh's panic, the kill law.     *)
(*   S2  the prompt's law at the widened credential.                      *)
(*   S3  the dispatch and [sh_round_holds_pipes].                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import ObsTrace.
Require Import ConsoleInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import LineModel.
Require Import PipesDisc.
Require FileDisc.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeOutN PipeOutNEv.
Require Import PipesLinks.
Require Import LinkRec.
Require Import StageRec.
Require Import GenLinksLine.
Require Import PipesLinkInst.
Require Import PipesStageInst.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UShLine.
Require Import UShEcho.
Require Import UShPanic.
Require Import UShEchoPay.
Require Import UShRest.
Require Import UInitSh.
Require Import SpecKexec.
Require Import UserPtTree.
Require Import UkShPipeForkTwin.
Require Import UShCatPay.
Require Import CtxIdDefs.
Require Import AppCfg AppPipeClaim.
Require Import PipeProto.
Require Import UkPipesIface.
Require Import UexecRet.
Require UexecExecMint.
Require Import UkShPipesFork.
Require Import PipesUline PipesCut.
Require Import UShPipesLaw.
Require UShKernel.
Local Open Scope Z_scope.

Local Notation fcE := (fun _ : ProgTree.bytes => @None ProgTree.bytes).

(* ===================================================================== *)
(*  S0  THE ERA'S PURE DISCIPLINE READINGS                                *)
(* ===================================================================== *)
Local Notation DscE := (lm_disc_input pipes_lmE).
Local Notation PBE := (pipes_lm_byte_laws fcE adm_echo).

Lemma psq_disc_snoc_val (I : list (bv 8)) (b : bv 8) :
  DscE (I ++ [b]) -> bv_unsigned b = 10%Z \/ (32 <= bv_unsigned b < 127)%Z.
Proof using.
  intros Hd. apply (lm_disc_input_byte_val pipes_lmE PBE (I ++ [b]) b Hd).
  apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

(* [UkSh]'s [Hdsc_ncr] at the pipeline discipline *)
Lemma psq_disc_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  DscE (I ++ [b])%list -> bv_unsigned b <> 13%Z.
Proof using. intro Hd. pose proof (psq_disc_snoc_val I b Hd). lia. Qed.

(* [UkSh]'s [Hdsc_short] *)
Lemma psq_disc_rest_short (I : list (bv 8)) :
  DscE I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat.
Proof using. intros (_ & _ & H). exact H. Qed.

(* ...AND THE ^D REFUTATION *)
Lemma psq_disc_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4 -> lm_disc pipes_lmE h -> False.
Proof using.
  intros [h0 ->] Hx Hd.
  assert (Hb : bv_unsigned b = 4).
  { destruct (decide (b = (mword_of_int 13 : mword 8))) as [-> | Hne].
    - rewrite cons_xlate_cr in Hx. vm_compute in Hx. discriminate Hx.
    - rewrite (cons_xlate_other b Hne) in Hx. exact Hx. }
  destruct (UkSh.ush_cycles_snoc_in h0 b) as (s0 & Hin).
  apply elem_of_list_In in Hin.
  pose proof (proj1 (Forall_forall _ _) Hd _ Hin) as (s & _ & Hseg & _).
  rewrite ins_app ins_in in Hseg.
  pose proof (psq_disc_snoc_val (ins s0) b Hseg) as Hv. lia.
Qed.

(* a newline closes an admissible body, which IS the era's own line at
   the three projections [UkSh.ush_line_at] reads *)
Lemma psq_disc_line (I : list (bv 8)) (f : nat -> bv 8) :
  DscE (I ++ [wl_nl])%list ->
  (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
  f (length (rest_of I)) = wl_nl ->
  exists lu : FileDisc.uline,
    ush_line_pipes lu
    /\ FileDisc.uline_ws lu = wl_words (rest_of I)
    /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
    /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))).
Proof using.
  intros (Hb & _ & _) Hby Hfnl.
  rewrite bodies_of_snoc_nl in Hb. apply Forall_app in Hb as [_ Hlast].
  apply Forall_inv in Hlast.
  set (J := rest_of I) in *.
  destruct (pl_body_ok_line adm_echo J Hlast) as (Ha & Hok & HJ).
  exists (uline_of_pl (pl_of J)).
  assert (Hbytes : FileDisc.line_bytes (uline_of_pl (pl_of J)) = J ++ [wl_nl]).
  { rewrite (line_bytes_of_pl (pl_of J) Ha). by rewrite -HJ. }
  assert (Hlen : length (FileDisc.line_bytes (uline_of_pl (pl_of J))) = S (length J))
    by (rewrite Hbytes length_app; cbn [length]; lia).
  split; [exists (pl_of J); split; [exact Ha | reflexivity] |].
  split; [rewrite (uline_ws_of_pl (pl_of J) Ha Hok); by rewrite -HJ |].
  split; [exact Hlen |].
  rewrite /UkSh.ush_line_at. split_and!.
  - exact (uline_ok_of_pl (pl_of J) Ha Hok).
  - by rewrite Hlen.
  - intros j Hj. rewrite Nat.add_0_l Hbytes.
    assert (Hnlat : (J ++ [wl_nl]) !!! length J = wl_nl).
    { pose proof (wl_lta_app_r J [wl_nl] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. exact Hr. }
    destruct (Nat.eq_dec j (length J)) as [-> | Hne].
    + by rewrite Hfnl Hnlat.
    + rewrite (Hby j ltac:(lia)).
      symmetry. exact (wl_lta_app_l J [wl_nl] j ltac:(lia)).
Qed.

(* THE ECHO LINE'S CONSTRUCTOR, off the loop's slot: a body some
   admissible line has, whose words are an echo line's, is that echo line *)
Lemma pipes_lineok_of (I : list (bv 8)) :
  FileDisc.fline_ok (UkSh.ush_lastbody I) ->
  line_ok (last_ws I) -> pipes_lineok I.
Proof using.
  intros [l [Hlok Hb]] Hok. rewrite /pipes_lineok.
  rewrite (_ : lineN fcE adm_echo I = pl_of (UkSh.ush_lastbody I)); [| reflexivity].
  rewrite (last_ws_lastbody I) in Hok |- *.
  change (bodies_of I !!! (nlines I - 1)%nat) with (UkSh.ush_lastbody I) in Hok |- *.
  rewrite Hb in Hok |- *.
  destruct l as [ws | ws | | ws npc].
  - cbn [FileDisc.line_body FileDisc.uline_ok] in *.
    rewrite (wl_words_body ws (line_ok_wf _ Hlok)).
    exact (pl_of_body (LEcho' ws) Hlok).
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok))) as Hbb.
    rewrite /FileDisc.line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    exact (FileDisc.wl_gt_not_body
             (proj1 (Forall_forall _ _) Hsuf FileDisc.wl_gt (proj1 (elem_of_list_In _ _) FileDisc.suf_gtf_gt))).
  - exfalso. rewrite /FileDisc.line_body in Hok.
    exact (FileDisc.cat_not_echo (line_ok_head _ Hok)).
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok))) as Hbb.
    rewrite /FileDisc.line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    destruct Hlok as (_ & Hn1 & _). destruct npc as [| m]; [lia |].
    rewrite FileDisc.suf_barcats_S in Hsuf. apply Forall_app in Hsuf as [Hsuf _].
    exact (FileDisc.fd_bar_not_body
             (proj1 (Forall_forall _ _) Hsuf FileDisc.fd_bar (proj1 (elem_of_list_In _ _) FileDisc.suf_barcat_bar))).
Qed.

(* ===================================================================== *)
(*  S1  THE FAMILIES AND THE ECHO ARM                                     *)
(* ===================================================================== *)
Section UShPipesRound.
  Context `{HRg : !riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.

  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Local Notation T := (echo_taint γ).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Context (rn : echo_names).
  Context (Heq : file_app = MkAppcfg echo_names (pipe_pred γ) rn).

  Local Notation PI := (pipes_link_inst_at g).
  Local Notation SI := (pipes_stage_inst_at g).
  Local Notation Wcf := (pipes_Wcl_at g).
  Local Notation Wbf := (pipes_Wbl_at g).
  Local Notation Wct := (pterm_wcN g).

  #[local] Instance psr_links_pers0 : Persistent (pipes_links g) | 0
    := pipes_links_persistent g.
  #[local] Instance psr_T_pers0 : Persistent T | 0 := echo_taint_persistent γ.
  #[local] Instance psr_T_tl0 : Timeless T | 0 := echo_taint_timeless γ.
  #[local] Instance psr_rres_pers0 (v : era_pins) (I : list (bv 8)) :
    Persistent (gwc_rres pipes_lmE (pipes_params g) v I) | 0
    := gwc_rres_persistent pipes_lmE (pipes_params g) v I.
  #[local] Instance psr_exf_at_pers0 (PSx : UexecSG.uprogSG Σ)
      (dg : list (bv 8)) (n : nat) (Cr Cd : iProp Σ) :
    Persistent (UkShDiag.ush_execfail_law_at (PS := PSx) dg n Cr Cd) | 0
    := UkShDiag.ush_execfail_law_at_persistent (PS := PSx) dg n Cr Cd.

  (* the era's kill credential IS the echo taint *)
  Lemma pipes_Hktaint : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  (* THE ECHO CHILD'S GUARD: the line is admissible and the era filed an
     echo line at that input *)
  Definition pipes_D (I : list (bv 8)) : Prop :=
    line_ok (last_ws I) /\ pipes_lineok I.

  Lemma pipes_D_of_line (I : list (bv 8)) (ws : list (list (bv 8))) :
    line_ok ws -> ws = last_ws I ->
    FileDisc.fline_ok (UkSh.ush_lastbody I) -> pipes_D I.
  Proof using .
    intros Hok Hwseq Hfb. subst ws. split; [exact Hok |].
    exact (pipes_lineok_of I Hfb Hok).
  Qed.

  Lemma pipes_D_exfb (I : list (bv 8)) :
    pipes_D I ->
    lk_exfb PI I = alt_execfail /\ (length (lk_exfb PI I) - 2)%nat = 17%nat.
  Proof using .
    intros [_ Hl]. exact (pipes_inst_exfb_echo g I (last_ws I) Hl).
  Qed.

  (* ---- the four [Wc] laws the supply takes, at [Hold := emp] ---- *)
  Local Lemma pwc3_t (I0 : list (bv 8)) :
    ⊢ Wct I0 3%nat -∗ ∃ v : era_pins,
        lk_pin PI (S gen_id) v ∗ lk_lpr PI (S gen_id) v I0 3%nat ∗ emp.
  Proof using .
    iIntros "H". iDestruct (pterm_wcN_3 g I0 with "H") as "H".
    rewrite /pipes_Wcl_at /lk_lcred. iDestruct "H" as (v) "[#Hp Hc]". iExists v.
    iSplitR; [iExact "Hp" |]. iSplitL; [iExact "Hc" | done].
  Qed.

  Local Lemma pwc3b_t (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_lpr PI (S gen_id) v0 I0 3%nat -∗
      emp -∗ Wct I0 3%nat.
  Proof using .
    iIntros "#Hp Hc _". iApply (pterm_wcN_of g I0 3%nat).
    rewrite /pipes_Wcl_at /lk_lcred. iExists v0. iSplitR; [iExact "Hp" | iExact "Hc"].
  Qed.

  Local Lemma pwc0_t (I0 : list (bv 8)) (v0 : era_pins) :
    ck_lineok (sk_cur SI) I0 ->
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_post PI (S gen_id) v0 I0 (sk_code SI I0) -∗
      emp -∗ Wct I0 0%nat.
  Proof using .
    intro Hlok. iIntros "#Hp Hc _". iApply (pterm_wcN_of g I0 0%nat).
    rewrite /pipes_Wcl_at.
    iApply (lk_lcred_of_post_a PI (S gen_id) I0 (sk_code SI I0) v0
              (sk_apr0 SI I0 Hlok) with "Hp Hc").
  Qed.

  Local Lemma pwct_t (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_T PI -∗ Wct I0 0%nat.
  Proof using .
    iIntros "#Hp #HT". iApply (pterm_wcN_of g I0 0%nat).
    rewrite /pipes_Wcl_at.
    iApply (lk_lcred_taint PI (S gen_id) I0 0%nat v0 with "Hp HT").
  Qed.

  (* ---- THE ECHO CHILD'S EXEC SUPPLY, at the generic record ---- *)
  Lemma pipes_Hchild_echo_t :
    ⊢ pipes_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq_at pipes_D Wct.
  Proof using Hkill.
    iIntros "#Hlk #Hdep #Hslot".
    iApply (sh_exec_sup_echo_wq_holds_at_D SI pipes_D Wct (fun _ => emp%I)
              ltac:(intros; apply _) pwc3_t pwc3b_t pwc0_t pwct_t pipes_Hktaint
              (fun I0 HD => proj1 HD) (fun I0 HD => proj2 HD)
              with "Hlk Hdep Hslot").
  Qed.

  (* ---- THE EXEC-FAILED DIAGNOSTIC'S LAW ---- *)
  Lemma pipes_Hexecfail_D_t :
    ⊢ pipes_links g -∗
      UkShEcho.ush_execfail_law_wq_at_D (PS := uprogSG_free) pipes_D
        (lk_exfb PI) (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat) Wct.
  Proof using .
    iIntros "#Hlk". rewrite /UkShEcho.ush_execfail_law_wq_at_D.
    iIntros "!>" (I) "_".
    iPoseProof (UShPanic.ush_execfail_law_hold_at (PS := uprogSG_free) PI
                  (fun _ => emp)%I I with "Hlk") as "#Hx".
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct (pterm_wcN_3 g I with "Hc") as "Hc".
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | iSplitL; [ rewrite /pipes_Wcl_at; iExact "Hc" | done ] | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iDestruct ("Hend" with "Hp") as "[Hc _]".
    iApply (pterm_wcN_of g I 0%nat). rewrite /pipes_Wcl_at. iExact "Hc".
  Qed.

  (* ---- sh's OWN FORK PANIC ---- *)
  Lemma pipes_Hpanic_t :
    ⊢ pipes_links g -∗ UkShDiag.ush_panic_law (PS := uprogSG_free) Wct Wbf.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) PI
                  (fun _ => emp)%I with "Hlk") as "#Hp".
    rewrite /UkShDiag.ush_panic_law. iIntros "!>" (N I l) "%Hfd Hc".
    iDestruct (pterm_wcN_3 g I with "Hc") as "Hc".
    iDestruct ("Hp" $! N I l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | iSplitL; [ rewrite /pipes_Wcl_at; iExact "Hc" | done ] | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp5".
    iDestruct ("Hend" with "Hp5") as "[Hb _]".
    rewrite /pipes_Wbl_at. iExact "Hb".
  Qed.

  (* ---- ...AND THE ECHO CHILD'S WHOLE LAW ---- *)
  Lemma pipes_child_law_echo_t :
    ⊢ pipes_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wct.
  Proof using Hkill.
    iIntros "#Hlk #Hdep #Hslot".
    iPoseProof (pipes_Hexecfail_D_t with "Hlk") as "#Hxl".
    iPoseProof (pipes_Hchild_echo_t with "Hlk Hdep Hslot") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) pipes_D (lk_exfb PI)
              (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat) Wct
              pipes_D_of_line pipes_D_exfb with "Hxl Hsup").
  Qed.

  (* ---- a KILLED child pays the payload with the taint ---- *)
  Lemma pipes_kill_law_t (v : era_pins) :
    era_pin γ (S gen_id) v -∗ UkShFork.ushf_kill_law Wct.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [ iApply pipes_Hktaint; iExact "Hk" | ].
    iApply (pterm_wcN_of g I 0%nat).
    iApply (pipes_Hcltaint g I 0%nat v with "Hpin HT").
  Qed.

  (* =================================================================== *)
  (*  S2  THE PROMPT'S LAW AT THE WIDENED CREDENTIAL                      *)
  (* =================================================================== *)
  Lemma pipes_sh_prompt_law_t :
    ⊢ pipes_links g -∗ UShKernel.sh_prompt_law (PS := uprogSG_free) Wct.
  Proof using Hcons.
    iIntros "#Hlk".
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free) Wcf)%I as "#Hpl0".
    { iApply (UShPanic.sh_prompt_law_holds_line_at PI (PS := uprogSG_free) with "Hlk"). }
    rewrite /UShKernel.sh_prompt_law. iIntros "!>" (Np) "#Hro".
    iPoseProof ("Hpl0" $! Np with "Hro") as "#Hlaw".
    rewrite {1}/UkSh.ush_prompt_law.
    iDestruct "Hlaw" as "[#Hplaw #Hclaw]".
    rewrite /UkSh.ush_prompt_law. iModIntro. iSplitR "".
    - iIntros (I l) "%Hfd2". destruct Hfd2 as [rb Hl2].
      iPoseProof (pterm_prompt_armN g Hcons Np I l rb Hl2 with "Hro") as "Hta".
      iPoseProof (pdone_prompt_armN g Hcons Np I l rb Hl2 with "Hro") as "Hda".
      iIntros (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
      rewrite {1}/pterm_wcN.
      iDestruct "Hc" as "[Hc | [[_ Hsh] | [_ Hsh]]]".
      + iApply ("Hplaw" $! I l with "[%] [%] [%] [%] Hcode [$Hstd $Hc] Hrun [Hcont]");
          [ by exists rb | exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (pterm_wcN_of g I 2%nat with "Hw").
      + iApply ("Hta" $! h m avail with "[%] [%] [%] Hcode [$Hstd Hsh] Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | | ].
        { rewrite Nat.add_0_r. iExact "Hsh". }
        iIntros (h' ret) "[Hstd Hsh'] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hsh'] Hrun").
        rewrite /pterm_wcN. iRight. iLeft.
        iSplitR; [ iPureIntro; lia | ]. iExact "Hsh'".
      + iApply ("Hda" $! h m avail with "[%] [%] [%] Hcode [$Hstd $Hsh] Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (pterm_wcN_of g I 2%nat with "Hw").
    - iExact "Hclaw".
  Qed.

  (* =================================================================== *)
  (*  S3  THE DISPATCH, AND THE ROUND                                     *)
  (* =================================================================== *)
  Context (γp : gname).
  Local Notation Pm := (UShLine.ush_mid_at (lk_rres PI) γ γp).

  (* the mid-line pieces carry the reader's residue at the same input *)
  Lemma pipes_mid_rres (I' : list (bv 8)) :
    ⊢ Pm I' -∗ Pm I' ∗ (∃ v : era_pins, era_pin γ (S gen_id) v
                                        ∗ gwc_rres pipes_lmE (pipes_params g) v I').
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hlb & #Hres)".
    iSplitR "".
    - iFrame "Hp Hpa Hrd". iExists v. by iFrame "Hpin Hdl Hlb Hres".
    - iExists v. by iFrame "Hpin Hres".
  Qed.

  Lemma pipes_pterm_read_law : pterm_read_lawN g Pm.
  Proof using . exact (pterm_read_lawN_of g Pm pipes_mid_rres). Qed.

  Lemma ushq_body_law_pipes (N : uk_names Σ) `{Hp : !ukn_const N} (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wct -∗
    UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wct -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      Wct pipes_lp (68 + UkSh.ush_Dpipe) -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wct Wbf -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      N γp T Wct Wbf Pm ush_line_pipes sz.
  Proof using .
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hchq #Hplaw".
    iPoseProof (UkShPipeForkTwin.ushf_body_law_echo_pipe (PS := uprogSG_free)
                  (SG := uexecSG_xv6) N γp T Wct Wbf Pm
                  (fun k H => H) sz Hszlo Hszal Hszok
                  (pterm_wcN_blk_line g)
                  with "Hkl Hchl Hplaw") as "#Hecho".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct (ush_line_pipes_cases lu Hd) as [[ws ->] | (ws & n' & ->)].
    - (* [echo ws] -- the landed walk *)
      iApply ("Hecho" $! (FileDisc.LEcho ws) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists ws | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* [echo ws | cat | .. | cat] -- the pipe child *)
      iDestruct (UkSh.ush_jtab_ro (ukn_t N) with "Hjt") as "#Hro".
      iApply (UkShPipeForkTwin.wp_kshm_body_pipe (PS := uprogSG_free)
                (SG := uexecSG_xv6) N γp T Wct Wbf Pm (fun k0 H => H)
                pipes_lp (68 + UkSh.ush_Dpipe) h m f k len
                (FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) n')) sz l n
                ltac:(lia) pipes_lp0
                Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (pipes_lp_of_at ws n' f k len Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb
                (pterm_wcN_blk_line g)
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchq Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp (ukn_t N) with "Hcode").
      + exact Hfd0.
  Qed.

  (* ...AND THE ROUND: the command loop's body obligation at the era's
     families, which is what [UInitSh.sh_pay_of_parts_at] takes *)
  Lemma sh_round_holds_pipes (N : uk_names Σ) :
    ⊢ pipes_links g -∗
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      UkSh.ush_rest_l_at (PS := uprogSG_free) N γp T Wct Wbf Pm ush_line_pipes
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using Hcons Hkill Heq pipeProtoG0 pnsRegG0 uartGhostG0.
    iIntros "#Hlk #Hdep #Hslot #Hcat #Hpin".
    iPoseProof (pipes_child_law g Hcons Hkill rn Heq) as "#Hchl0".
    iPoseProof ("Hchl0" with "Hslot Hcat") as "#Hchq".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (pipes_kill_law_t v with "Hp") as "#Hkl".
    iPoseProof (pipes_child_law_echo_t with "Hlk Hdep Hslot") as "#Hchl".
    iPoseProof (pipes_Hpanic_t with "Hlk") as "#Hplaw".
    iIntros "!>" (l) "%Hc".
    iPoseProof (ushq_body_law_pipes N (Hp := Hc) (kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  with "Hkl Hchl Hchq Hplaw") as "#Hbody".
    iPoseProof (UkShPipeForkTwin.ushf_rest_of_body_at_pipe
                  (PS := uprogSG_free)
                  (SG := uexecSG_xv6) (Hpay := Hc) N γp T Wct Wbf Pm
                  (fun k H => H) ush_line_pipes
                  (kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  (pterm_wcN_blk_line g) with "Hbody") as "Hb".
    rewrite /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.
End UShPipesRound.
