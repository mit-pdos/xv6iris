(* ===================================================================== *)
(* UShCatFStage.v -- [cat f] AT THE HEAD, ITS STAGE LAW PAID BY THE ENTRY *)
(* (union.md C9d', item 4).                                               *)
(*                                                                        *)
(* [cat f] cannot read `f`, nor learn that it is absent, without the     *)
(* application's deed ([UkCatFIface]'s core holds it), so node 0 LENDS   *)
(* it: the round's producer loan [Rd] ([UShPipesDefs.lrd]) rides beside  *)
(* node 0's lend [echo_raw] and comes back beside the left report         *)
(* [QcK 0].  [stage_catf] is the producer's exec arm at the lend with the *)
(* loan, [prod_crD]: [prod_cr], the fork's shot, the pipe's persistent    *)
(* facts and [Rd] -- its EXEC FAILS arm the family writer at [exec cat    *)
(* failed] with the loan back, its EXEC SUCCEEDS arm a premise.  The      *)
(* premise is [catf_stage_sup] at the deed [fdq rf qf sf], built from     *)
(* [UkCatFEntries.pse_catf_image_entry_gen]: the lend's kits are the      *)
(* stage's (the diagnostics' and the report's, its deposit FROM the       *)
(* permit), and the exit wand reads the producer device's final state     *)
(* into node 0's report, the deed back beside it.                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions csum excl agree.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import WpUart.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs FdSlots UserFd.
Require Import ProcGeom.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UserCwd UserChildren.
Require Import ChildTok.
Require Import FsCfg FsImg FsImgCheck FsCatPin FsAbsDefs.
Require Import UexecSlot UexecRet UexecSG UexecExecInst UexecExecMint.
Require Import ExecEntry ExecArgs ExecRun.
Require Import ElfFile ElfUser.
Require Import LineWords EchoDisc EchoOut AppEcho.
Require Import LineModel.
Require Import PipeOut PipeDisc.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN GenOut PipeOutN PipesView.
Require Import PipeNames PipeProto.
Require Import AppCfg AppInv.
Require Import AppFile AppFileCons FileOpen.
Require Import ProgTree ProgTreePipes.
Require Import CtxIdDefs.
Require Import UCodeShK.
Require Import UkSh UkShRun UkShMain UkShDiag.
Require Import UkShEcho UkShCat.
Require Import UShEcho UShEchoPipePay UShCatPay UShCat.
Require Import UShPipeLeaves.
Require Import UkConsOut.
Require Import UkPipesIface UkPipesEntries.
Require Import PipesFire UShPipesDefs UShPipesStage UShExecPin.
Require Import UkCatFIface UkCatFEntries.
Require ExecWords UkShDiagAt FileDisc UNamePath.
Require User.ShSyms.
Local Open Scope Z_scope.

(* the producer's words at any user file (cut W3) *)
Lemma catf_ws_exec_ok (f : list (bv 8)) :
  FileDisc.uname f -> ExecWords.exec_ok (FileDisc.prod_words (PrCatF f)).
Proof using . exact (UNamePath.cat_words_exec_ok f). Qed.

Lemma catf_ws_head (f : list (bv 8)) :
  FileDisc.prod_words (PrCatF f) !!! 0%nat = UShCatPay.cat_pl.
Proof using . exact (UNamePath.cat_words_head f). Qed.

(* the producer's two standard rows: fd 1 the first pipe's write end, fd 2
   the console *)
Definition catf_rows (γp : pipe_names) (l : list fdstate) : Prop :=
  UShEchoPipePay.ush_fd1pipe γp l /\ UkSh.ush_fd2p l.

Section UShCatFStage.
  Context `{HRg : !riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ, !cifRegG Σ}.
  #[local] Existing Instance eo_turn | 0.

  (* THE FILE SIDE *)
  Context (cf : file_fixed) (rf : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred cf) rf).

  (* THE ROUND ([UShPipesStage]'s section context, name for name) *)
  Context (g : pipe_gn).
  Context (LM : lmodel) (PV : pview LM) (CP : gen_cparams LM) (sd : lm_st LM).
  Context (WA : gen_wa LM CP sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT CP).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g LM CP sd WA).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Hypothesis Hsup : ⊢ □ (T -∗ app_sup).
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st LM) (lR : pline').
  Hypothesis HlR : pv_line PV (lineV LM I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc PV sR).
  Context (Hadmit : pns_admV PV lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)) (HL31 : pns_short L).
  Context (pr : producer).
  Context (γc γm : wid -> gname).
  Context (P : nat -> pnames) (gF gG : nat -> gname).

  #[local] Instance cfs_T_pers0 : Persistent T | 0 := gcT_pers CP.
  #[local] Instance cfs_T_tl0 : Timeless T | 0 := gcT_tl CP.

  Local Notation fcR := (pv_fc PV sR).
  Local Notation nc := (lcats lR).
  Local Notation wsN := (wids nc).
  Local Notation RUNN := (runN (pv_fc PV sR) lR).
  Local Notation PWN := (pwc_blkV g LM (gcPIN CP) (gcW CP) T v I sR).
  Local Notation WITN := (pwitV LM I sR).
  Local Notation TOKN := (tokN (pv_fc PV sR) lR).
  Local Notation pdepR := (pdep LM PV sR lR L pr P gF gG).
  Local Notation FAM := (blkN_inv wsN RUNN PWN termw TOKN pdepR pnsN (S gen_id) γc γm).
  Local Notation pkitR w s := (pns_kit LM PV I sR lR termw TOKN pdepR w s).
  Local Notation QcR Rd k := (QcK LM CP v I lR L pr Rd γc γm P k).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  Hypothesis Hfire : forall w s, w ∈ wsN -> fire_src fcR pr (lfilts lR) L w s ->
    fire_okN wsN RUNN WITN termw TOKN w s (EXf fcR pr (lfilts lR) nc L w s).

  #[local] Instance cfs_kit_pers0 w s : Persistent (pkitR w s) | 0 :=
    pns_kit_persistent LM PV I sR lR termw TOKN pdepR w s.

  Local Lemma cfs_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* ================================================================= *)
  (*  1.  THE EXEC SUPPLY OF [cat f] AT THE PIPE, AT A CALLER'S ENTRY    *)
  (* ================================================================= *)

  (* [UShEchoPipePay.sh_exec_sup_echo_pipe_of_entry] at cat's image: the
     entry at every image the exec can produce, the ledger fragment spent
     at the exec *)
  Lemma sh_exec_sup_catf_of_entry (f : list (bv 8)) (Hf : FileDisc.uname f)
      (γp : pipe_names) (Qv Cr : iProp Σ) :
    □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (gn : nat -> bv 8)
         (sts : list fdstate) (cs : gset gname) (pidv : mword 32) (rb1 rb2 : bool),
         ⌜UShEcho.echo_node_img (FileDisc.prod_words (PrCatF f)) M s0 t gn⌝ -∗
         ⌜UkShEcho.echo_argv_bytes (FileDisc.prod_words (PrCatF f)) gn⌝ -∗
         ⌜length sts = NOFILE⌝ -∗
         ⌜take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdPipe γp))⌝ -∗
         ⌜take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice ConsoleInv.CONSOLE))⌝ -∗
         UkRun.urun_nopipe sts -∗
         image_entry ElfUser.cat_elf M (mword_of_int (t + 8) : mword 64)
           sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qv) Cr uslot) -∗
    □ (app_taint -∗ Qv) -∗
    UShCatPay.sh_cat_slot T -∗
    UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6) (catf_rows γp)
      (FileDisc.prod_words (PrCatF f)) (fun _ : Z => Qv) Cr.
  Proof using .
    iIntros "#Hent #Hkt (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc s0 t gn ld) "%Hpeq %Ha0 %Ha1 %Hbytes %Hrows Hstd #Hcmd Hcr".
    destruct Hrows as [[rb1 Hl1] [rb2 Hl2]].
    iAssert (image_entry_taint T (fun _ : Z => Qv) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! Qv W' with "HT Hmp Hkt"). }
    iApply (udepw_at_refR_of_sup N' m pc (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShCatPay.cat_pl ElfUser.cat_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ UShCat.cat_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜UShEcho.echo_node_img (FileDisc.prod_words (PrCatF f)) M s0 t gn⌝)%I
      as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd_x (FileDisc.prod_words (PrCatF f)) _ _ _
                M pm sz s0 t gn (catf_ws_exec_ok f Hf) with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro. rewrite -(catf_ws_head f).
      exact (UShEcho.sh_exec_path_of_x_holds (FileDisc.prod_words (PrCatF f))
               (catf_ws_exec_ok f Hf) M s0 t gn Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsCatPin.era0_cat_pins T FsImg.ROOTINO
                UShCatPay.cat_pl [FsImg.ROOTINO; FsCatPin.CAT_INO] FsCatPin.CAT_INO
                (MkAnode (AFile ElfUser.cat_elf) 1%nat) UShCatPay.sh_cat_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [ | iFrame "Hstd Hcr" ].
    rewrite Hpeq.
    iPoseProof ("Hent" $! M s0 t gn fdv chs pidv rb1 rb2 with "[%] [%] [%] [%] [%] Hnp0") as "#He";
      [ exact Himg | exact Hbytes | exact Hflen | rewrite Hl; exact Hl1 | rewrite Hl; exact Hl2 | ].
    iApply (UShEchoPipePay.image_entry_pay_mono ElfUser.cat_elf M
              (mword_of_int (t + 8) : mword 64) fdv FsImg.ROOTINO ProcDefs.secc_all chs pidv
              (fun _ : Z => Qv) Cr (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I uslot with "[] He").
    iIntros "!> [_ Hc]". iExact "Hc".
  Qed.

  (* ================================================================= *)
  (*  2.  THE STAGE LAW AT A LEND WITH THE DEED                          *)
  (* ================================================================= *)

  (* the stage's lend at its exec: [prod_cr], the fork's shot, the first
     pipe's persistent facts, and the extra lend [Rd] *)
  Definition prod_crD (γp : pipe_names) (Rd : iProp Σ) : iProp Σ :=
    (prod_cr γc γm P ∗ osS (gG 0) ∗ pipe_inv (P 0) γp L ∗ pws_lb (P 0) [] ∗ Rd)%I.

  (* [cat f] AT THE HEAD, at the lend with the loan [Rd]: the EXEC FAILS
     arm is the stage's family writer at [exec cat failed] (the loan back
     beside the report), the EXEC SUCCEEDS arm the premise *)
  Lemma stage_catf (Rd : iProp Σ) (f : list (bv 8)) (s0 : Z) (gs : nat -> bv 8)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γp : pipe_names) (q szv : Z)
      (ld : list fdstate) (av : nat) :
    pr = PrCatF f -> ExecWords.exec_ok (FileDisc.prod_words (PrCatF f)) ->
    echo_argv_bytes (FileDisc.prod_words (PrCatF f)) gs ->
    (0 < nc)%nat ->
    ukn_pay N' = (fun _ : Z => QcR Rd 0) ->
    m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ->
    UShEchoPipePay.ush_fd1pipe γp ld -> UkSh.ush_fd2p ld -> (6 <= av)%nat ->
    FAM -∗
    UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
      (catf_rows γp) (FileDisc.prod_words (PrCatF f))
      (fun _ : Z => QcR Rd 0) (prod_crD γp Rd) -∗
    shk_code (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
    ush_cmd (ukn_d N') q (echo_cmd (FileDisc.prod_words (PrCatF f)) s0 gs) -∗
    usz (ukn_s N') szv -∗ UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    echo_raw L γc γm P gG γp -∗ Rd -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m' (mword_of_int ShSyms.runcmd)
      (2 + (UkShDiag.ush_Dg + av)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hadmit Hcons Hext Hfc Hfire HlR Hplok.
    intros Hpr Hok Hbytes Hn Hpeq Ha0 Hfd1 Hfd2 Hav.
    assert (Hdg0 : dg_execR = dg_st pr (lfilts lR) 0) by (rewrite Hpr; reflexivity).
    iIntros "#Hinv #Hsup #Hcode #Hjt #Hcmd Hsz Hstd Hcwd Hch Hraw HRd Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iDestruct "Hraw" as "(#Hpi & Hw & #Hlb & HsL & Hcw & Hmw & HG)".
    iApply cfs_fupd_mwp. iMod (os_shoot with "HG") as "#HGs". iModIntro.
    assert (Hw0 : WLeft 0 ∈ wsN) by (apply wids_elem; exact Hn).
    set (Cd := ((side_L (P 0) ∗ Rd) ∗ pns_wfin γc γm (WLeft 0) (Some dg_execR))%I).
    iAssert (UkShDiag.ush_execfail_law_at (SG := uexecSG_xv6) (PS := uprogSG_free)
               alt_execR 16%nat (prod_crD γp Rd) Cd)%I as "Hxl".
    { iApply (exf_writer g LM PV CP sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok L pr
                γc γm P gF gG (WLeft 0) dg_execR alt_execR 16%nat
                (EXf fcR pr (lfilts lR) nc L (WLeft 0) dg_execR) (prod_crD γp Rd) (side_L (P 0) ∗ Rd)%I Cd Hw0 ltac:(lia)
                ltac:(intros j b Hj Hb; exact (dg_app_lookup dg_execR u_prompt j b
                               ltac:(rewrite dg_execR_len; lia) Hb))
                (Hfire (WLeft 0) dg_execR Hw0 (or_introl (or_introl Hdg0)))
                ltac:(intros c Hcx; apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WLeft 0) dg_execR c);
                      [lia | rewrite dg_execR_len; lia | intros k Hk; discriminate Hk])
                with "Hinv [] [] []").
      - iApply (pexcl_left LM PV sR lR L pr P gF gG 0 dg_execR Hn ltac:(vm_compute; discriminate)).
        rewrite /pinv /pflow. iExists γp. cbn [prevP flowF]. iExact "Hpi".
      - iIntros "!> ((Hw & HsL & Hcw & Hmw) & #HG' & _ & _ & HRd)". iFrame "HsL HRd Hcw Hmw".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft 0) dg_execR
                   ltac:(vm_compute; discriminate) (or_introl (or_introl Hdg0))) /pdep_ne.
        rewrite bool_decide_true; [| left; exact Hdg0].
        iFrame "Hw HG'". rewrite /shotsF. done.
      - iIntros "!> HsL Hcw Hmw _". rewrite /Cd. iFrame "HsL".
        cbn [pns_wfin]. rewrite dg_execR_len.
        iFrame "Hcw Hmw". }
    replace (2 + (UkShDiag.ush_Dg + av))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat by lia.
    iApply (UkShEcho.wp_kshr_exec_x_at_holds (SG := uexecSG_xv6) (PS := uprogSG_free)
              (catf_rows γp) (FileDisc.prod_words (PrCatF f)) alt_execR
              (fun _ : Z => QcR Rd 0) (prod_crD γp Rd) Cd
              N' Hc h' m' q szv s0 gs ld (av - 6)%nat Hok catf_execfail_bytes Hpeq Ha0
              Hbytes (conj Hfd1 Hfd2) Hfd2
              with "Hcode Hsup Hxl [] Hjt Hcmd Hsz Hstd Hcwd [Hch] [Hw HsL Hcw Hmw HRd] Hrun").
    - iIntros "!> [[HsL HRd] Hf]". iRight. iLeft. iFrame "HsL".
      iSplitL "HRd"; [rewrite /lrd; iExact "HRd" |]. rewrite /lrep.
      iExists (Some dg_execR). iFrame "Hf". iLeft. iPureIntro.
      exists dg_execR. split; [reflexivity | left; exact Hdg0].
    - iApply (UserChildren.uch_any_of with "Hch").
    - rewrite /prod_crD /prod_cr. iFrame "Hw HsL Hcw Hmw HGs Hpi Hlb HRd".
  Qed.

  Lemma stage_catf_law (Rd : iProp Σ) (f : list (bv 8)) (s0 : Z) (gs : nat -> bv 8) :
    pr = PrCatF f -> ExecWords.exec_ok (FileDisc.prod_words (PrCatF f)) ->
    echo_argv_bytes (FileDisc.prod_words (PrCatF f)) gs -> (0 < nc)%nat ->
    FAM -∗
    □ (∀ γp : pipe_names,
         UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
           (catf_rows γp) (FileDisc.prod_words (PrCatF f))
           (fun _ : Z => QcR Rd 0) (prod_crD γp Rd)) -∗
    prod_stage_law LM CP v I lR L pr Rd γc γm P gG
      (UkShMain.ush_args s0 gs (echo_toks (FileDisc.prod_words (PrCatF f)))).
  Proof using Hadmit Hcons Hext Hfc Hfire HlR Hplok.
    intros Hpr Hok Hbytes Hn. iIntros "#Hfam #Hsup". rewrite /prod_stage_law.
    iIntros "!>" (N' h' m' γp q szv ld av) "%Hpeq %Ha0 %Hfd1 %Hfd2 %Hav #Hck #Hjt #Hcmd".
    iIntros "Hsz Hstd Hcwd Hch Hraw HRd Hrun".
    iApply (stage_catf Rd f s0 gs N' h' m' γp q szv ld av Hpr Hok Hbytes Hn Hpeq Ha0
              Hfd1 Hfd2 Hav with "Hfam [] Hck Hjt Hcmd Hsz Hstd Hcwd Hch Hraw HRd Hrun").
    iApply "Hsup".
  Qed.

  (* ================================================================= *)
  (*  3.  THE PREMISE, PAID BY THE ENTRY                                 *)
  (* ================================================================= *)

  Local Notation LEND f qf sf γp ds :=
    (cif_catf_lend cf rf g LM PV CP v I sR lR L termw TOKN pdepR γc γm qf sf (P 0) γp (WLeft 0)
       ds [cat_dg_open f] ds [cat_dg_open f] (fun _ : Z => QcR (fdq rf qf sf) 0)).

  (* the writer's kit at a diagnostic of [cat f], or at its report *)
  Lemma catf_kit (f s : list (bv 8)) (γp : pipe_names) :
    pr = PrCatF f -> (0 < nc)%nat -> s <> [] -> fire_src fcR pr (lfilts lR) L (WLeft 0) s ->
    pipe_inv (P 0) γp L -∗ pkitR (WLeft 0) s.
  Proof using Hadmit Hfire HlR.
    intros Hpr Hn Hs Hf. iIntros "#Hpi".
    assert (Hw0 : WLeft 0 ∈ wsN) by (apply wids_elem; exact Hn).
    iApply (pkit_of LM PV I sR lR HlR Hadmit L pr P gF gG (WLeft 0) s
              ltac:(intros k Hk; discriminate Hk) (Hfire (WLeft 0) s Hw0 Hf)).
    iApply (pexcl_left LM PV sR lR L pr P gF gG 0 s Hn Hs).
    rewrite /pinv /pflow. iExists γp. cbn [prevP flowF]. iExact "Hpi".
  Qed.

  (* THE LEND, out of the stage's: the writer unfired with the kits (the
     report's deposit FROM the permit), the deed, the file's context, and
     the exit wand reading the producer device's final state into node 0's
     report *)
  Lemma catf_lend_of (f : list (bv 8)) (qf : Qp) (sf : dst) (γp : pipe_names)
      (ds : list (list (bv 8))) :
    pr = PrCatF f -> FileDisc.uname f -> (0 < nc)%nat ->
    (ds = [[]; cat_dg_write] /\ is_Some (fcR f)) \/ ds = [[]] ->
    FAM -∗ □ (app_taint -∗ file_taint cf) -∗ □ (file_taint cf -∗ app_taint) -∗
    app_inv fsc_fs -∗ (∃ jo : option Z, file_cons_cred cf rf jo) -∗
    □ (prod_crD γp (fdq rf qf sf) -∗ LEND f qf sf γp ds).
  Proof using Hadmit Hfire Hkill HlR.
    intros Hpr Hf Hn Hds. iIntros "#Hfam #Hbr #Hrb #Hai #Hcr".
    iIntros "!> ((Hw & HsL & Hcw & Hmw) & #HGs & #Hpi & #Hlb & Hdq)".
    assert (Hw0 : WLeft 0 ∈ wsN) by (apply wids_elem; exact Hn).
    assert (Hfo : fire_src fcR pr (lfilts lR) L (WLeft 0) (cat_dg_open f)).
    { cbn [fire_src]. left. right. split; [reflexivity | by rewrite Hpr]. }
    assert (Hfso : fail_src pr (lfilts lR) 0 (cat_dg_open f)).
    { right. split; [reflexivity | by rewrite Hpr]. }
    iPoseProof (catf_kit f (cat_dg_open f) γp Hpr Hn (cat_dg_open_ne _) Hfo with "Hpi")
      as "#Hko".
    rewrite /cif_catf_lend. iFrame "Hpi Hw Hlb Hdq Hbr Hrb Hai Hcr".
    iSplitL "Hcw Hmw".
    - (* the writer, unfired, with its kits *)
      rewrite /cif_unf. iFrame "Hfam Hcw Hmw".
      iSplitR; [by iPureIntro |].
      iSplitR.
      { iPureIntro. split.
        - destruct Hds as [[-> _] | ->]; rewrite /cons_short; repeat constructor; vm_compute; lia.
        - rewrite /cons_short. constructor; [exact (UNamePath.catopen_short f Hf) | constructor]. }
      iSplitR; [iPureIntro; split; intros a Ha; exact Ha |].
      iSplitL.
      + destruct Hds as [[-> Hsome] | ->].
        * assert (Hh : prod_halts fcR pr) by (rewrite Hpr; exact Hsome).
          assert (Hfw : fire_src fcR pr (lfilts lR) L (WLeft 0) cat_dg_write).
          { cbn [fire_src]. right. split; [exact Hh | reflexivity]. }
          rewrite big_sepL_cons big_sepL_singleton. iSplitR; [by iLeft |]. iRight.
          iSplitR; [iApply (catf_kit f cat_dg_write γp Hpr Hn cat_dg_write_ne Hfw with "Hpi") |].
          iApply (pdep_left_write LM PV sR lR L pr P gF gG 0 Hh with "[] HGs").
          rewrite /shotsF. done.
        * rewrite big_sepL_singleton. by iLeft.
      + rewrite big_sepL_singleton. iRight. iFrame "Hko". iIntros "!> Hw0".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft 0) (cat_dg_open f)
                   (cat_dg_open_ne _) (or_introl Hfso)) /pdep_ne.
        rewrite bool_decide_true; [| exact Hfso].
        iFrame "Hw0 HGs". rewrite /shotsF. done.
    - (* the exit wand *)
      rewrite /cif_xkQ. iIntros "[#HT | [Hf Hdq]]"; [by iLeft |].
      rewrite big_sepL_singleton. cbn [cif_final snd].
      iDestruct "Hf" as "[[Hp Hcf] | (%x & %Hx & Hwf)]"; last first.
      { apply elem_of_list_singleton in Hx as ->.
        iRight. iLeft. iFrame "HsL".
        iSplitL "Hdq"; [rewrite /lrd; iExact "Hdq" |]. rewrite /lrep. iExists (Some (cat_dg_open f)).
        iFrame "Hwf". iLeft. iPureIntro. by exists (cat_dg_open f). }
      iDestruct "Hcf" as (o) "[_ Hwf]".
      iDestruct "Hp" as "[Hle | Hw0]"; last first.
      { iRight. iLeft. iFrame "HsL".
        iSplitL "Hdq"; [rewrite /lrd; iExact "Hdq" |]. rewrite /lrep. iExists o. iFrame "Hwf".
        iRight. iExists WrNone. cbn [wr_final]. rewrite /wtok.
        iSplitL "Hw0"; [iExact "Hw0" | iPureIntro; intros D HD; discriminate HD]. }
      rewrite /pns_lexit.
      iDestruct "Hle" as "[[Hw' #Hlb'] | [(%c & %HcL & [Hw' #Hlb'] & #Hro) | #Hta]]".
      + iRight. iLeft. iFrame "HsL".
        iSplitL "Hdq"; [rewrite /lrd; iExact "Hdq" |]. rewrite /lrep. iExists o. iFrame "Hwf".
        iRight. iExists (WrAll L). cbn [wr_final]. rewrite firstn_all.
        iSplitL; [| iPureIntro; intros D HD; by injection HD as <-].
        iFrame "Hlb'". by iLeft.
      + iRight. iLeft. iFrame "HsL".
        iSplitL "Hdq"; [rewrite /lrd; iExact "Hdq" |]. rewrite /lrep. iExists o. iFrame "Hwf".
        iRight. iExists (WrHalt (take c L)). cbn [wr_final].
        iSplitL; [| iPureIntro; intros D HD; discriminate HD].
        iExists c. iFrame "Hw' Hro". done.
      + iLeft. rewrite Hkill. iExact "Hta".
  Qed.

  (* THE PREMISE of [stage_catf_law] at the deed: [cat f]'s exec supply
     from the entry, at every pipe *)
  Lemma catf_stage_sup (f : list (bv 8)) (qf : Qp) (sf : dst) (ds : list (list (bv 8))) :
    pr = PrCatF f -> FileDisc.uname f -> (0 < nc)%nat ->
    (snd <$> sf !! f = Some L /\ fcR f = Some L /\ ds = [[]; cat_dg_write])
    \/ (sf !! f = None /\ ds = [[]]) ->
    FAM -∗ UShCatPay.sh_cat_slot T -∗
    □ (app_taint -∗ file_taint cf) -∗ □ (file_taint cf -∗ app_taint) -∗
    app_inv fsc_fs -∗ (∃ jo : option Z, file_cons_cred cf rf jo) -∗
    □ (∀ γp : pipe_names,
         UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
           (catf_rows γp) (FileDisc.prod_words (PrCatF f))
           (fun _ : Z => QcR (fdq rf qf sf) 0) (prod_crD γp (fdq rf qf sf))).
  Proof using HL31 Hadmit Hcons Heq Hext Hfc Hfire Hkill HlR Hplok Hsup cifRegG0.
    intros Hpr Hf Hn Hcase.
    iIntros "#Hfam #Hslot #Hbr #Hrb #Hai #Hcr !>" (γp).
    assert (Hds : (ds = [[]; cat_dg_write] /\ is_Some (fcR f)) \/ ds = [[]]).
    { destruct Hcase as [(_ & Hfc' & ->) | (_ & ->)]; [left; split; [done | by eexists] | by right]. }
    iPoseProof (catf_lend_of f qf sf γp ds Hpr Hf Hn Hds with "Hfam Hbr Hrb Hai Hcr") as "#Hlend".
    iApply (sh_exec_sup_catf_of_entry f Hf γp (QcR (fdq rf qf sf) 0) (prod_crD γp (fdq rf qf sf))
              with "[] [] Hslot").
    - iIntros "!>" (M s1 t1 g1 sts cs pidv rb1 rb2) "%Hi1 %Hb1 %Hl1 %Hr1 %Hr2 #Hnp".
      iApply (UShEchoPipePay.image_entry_pay_mono ElfUser.cat_elf M
                (mword_of_int (t1 + 8) : mword 64) sts FsImg.ROOTINO ProcDefs.secc_all cs pidv
                (fun _ : Z => QcR (fdq rf qf sf) 0) (LEND f qf sf γp ds) (prod_crD γp (fdq rf qf sf))
                uslot
                with "Hlend [Hnp]").
      assert (Hc2 : (snd <$> sf !! f = Some L /\ cat_dg_open f ∈ [cat_dg_open f]
                     /\ [] ∈ ds /\ cat_dg_write ∈ ds)
                    \/ (sf !! f = None /\ cat_dg_open f ∈ [cat_dg_open f])).
      { destruct Hcase as [(Hs & _ & ->) | (Hs & ->)].
        - left. split_and!; [exact Hs | by left | by left | by right; left].
        - right. split; [exact Hs | by left]. }
      iApply (pse_catf_image_entry_gen (PS := uprogSG_free) cf rf Heq g LM PV CP sd WA Hext
                Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31 termw TOKN pdepR
                (pdep_timeless LM PV sR lR L pr P gF gG) γc γm f M s1 t1 g1 sts
                FsImg.ROOTINO cs pidv (fun _ : Z => QcR (fdq rf qf sf) 0) (P 0) γp (WLeft 0)
                ds [cat_dg_open f] ds [cat_dg_open f] qf sf rb1 rb2
                (fun _ _ => eq_refl) Hf (catf_ws_exec_ok f Hf) Hi1 Hb1 Hl1 eq_refl Hr1 Hr2
                Hc2 with "Hnp []").
      iApply UexecExecMint.udep_free.
    - iIntros "!> #Ht". rewrite Hkill. by iLeft.
  Qed.

  (* ...AND THE PRODUCER'S STAGE LAW, PAID: [stage_catf_law] at the deed *)
  Lemma stage_catf_law_holds (f : list (bv 8)) (s0 : Z) (gs : nat -> bv 8)
      (qf : Qp) (sf : dst) (ds : list (list (bv 8))) :
    pr = PrCatF f -> FileDisc.uname f -> ExecWords.exec_ok (FileDisc.prod_words (PrCatF f)) ->
    echo_argv_bytes (FileDisc.prod_words (PrCatF f)) gs -> (0 < nc)%nat ->
    (snd <$> sf !! f = Some L /\ fcR f = Some L /\ ds = [[]; cat_dg_write])
    \/ (sf !! f = None /\ ds = [[]]) ->
    FAM -∗ UShCatPay.sh_cat_slot T -∗
    □ (app_taint -∗ file_taint cf) -∗ □ (file_taint cf -∗ app_taint) -∗
    app_inv fsc_fs -∗ (∃ jo : option Z, file_cons_cred cf rf jo) -∗
    prod_stage_law LM CP v I lR L pr (fdq rf qf sf) γc γm P gG
      (UkShMain.ush_args s0 gs (echo_toks (FileDisc.prod_words (PrCatF f)))).
  Proof using HL31 Hadmit Hcons Heq Hext Hfc Hfire Hkill HlR Hplok Hsup cifRegG0.
    intros Hpr Hf Hok Hbytes Hn Hcase.
    iIntros "#Hfam #Hslot #Hbr #Hrb #Hai #Hcr".
    iApply (stage_catf_law (fdq rf qf sf) f s0 gs Hpr Hok Hbytes Hn with "Hfam").
    iApply (catf_stage_sup f qf sf ds Hpr Hf Hn Hcase with "Hfam Hslot Hbr Hrb Hai Hcr").
  Qed.
End UShCatFStage.
