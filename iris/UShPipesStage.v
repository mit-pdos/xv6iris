(* ===================================================================== *)
(* UShPipesStage.v -- THE THREE STAGE LAWS OF THE N-STAGE ROUND, PAID    *)
(* (design claude-notes/design/pipes-general.md SS1.1-SS1.3, SS2.2; cut  *)
(* C7a).                                                                  *)
(*                                                                        *)
(* A stage is the forked sh that runs [runcmd] on one EXEC leaf of the    *)
(* right spine: echo at the head (the left child of node 0), a middle cat *)
(* (the left child of node k > 0) or the last cat (the right child of the *)
(* last node).  Each lemma here is sh's exec arm at that stage, both its  *)
(* arms paid:                                                             *)
(*   - EXEC SUCCEEDS: the arm's supply takes C6's entry                   *)
(*     ([UkPipesEntries.pse_echo_image_entry] / [pse_mid_image_entry] /   *)
(*     [pse_last_image_entry_m]) at a lend built out of the stage's raw   *)
(*     lend, whose exit wand reads the program's final devices into the   *)
(*     node's side-tagged payload [UShPipesDefs.QcK];                     *)
(*   - EXEC FAILS: sh prints [exec %s failed] as the stage's family       *)
(*     writer ([exf_writer]: the first byte fires the family, every       *)
(*     further byte steps it, each through [UShPipeAssembly.              *)
(*     ksh_w1_of_step]), depositing its untouched write permit, and pays   *)
(*     the node's payload with the writer at its whole source.            *)
(* Before either, the stage SHOOTS the one-shot of the fork that made it  *)
(* ([UShPipesDefs.gG] / [gF]): every deposit it makes from here on names  *)
(* that fork.                                                             *)
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
Require Import FsImg.
Require Import UexecSlot UexecRet UexecSG UexecExecInst UexecExecMint.
Require Import ExecEntry ExecArgs.
Require Import ElfFile ElfUser.
Require Import LineWords EchoDisc EchoOut AppEcho.
Require Import LineModel.
Require Import PipeOut PipeDisc.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN GenOut PipeOutN PipesView.
Require Import PipeNames PipeProto.
Require Import AppCfg AppInv.
Require Import ProgTree.
Require Import CtxIdDefs.
Require Import UCodeShK.
Require Import UkSh UkShRun UkShMain UkShDiag.
Require Import UkShEcho UkShCat.
Require Import UShEcho UShEchoPipePay UShCatPay.
Require Import UShPipeLeaves.   (* [ksh_w1_of_step], [alt_execfail_app] *)
Require Import UkConsOut.   (* [cons_short] *)
Require Import UkPipesIface UkPipesEntries.
Require Import PipesFire UShPipesDefs.
Require ExecWords UkShDiagAt FileDisc.
Require User.ShSyms.
Local Open Scope Z_scope.

(* sh's [exec cat failed], around the command's name *)
Lemma catf_execfail_bytes : UkShDiagAt.ush_execfail_bytes alt_execR FileDisc.fd_w_cat.
Proof using .
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros j Hj.
    assert (Hl : (j < length alt_execR)%nat) by (vm_compute in Hj |- *; lia).
    exact (list_lookup_lookup_total_lt alt_execR j Hl).
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
             (fun i : nat => alt_execR !!! i) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj3 : (j < 3)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| j]]]; try lia; vm_compute; reflexivity.
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
             (fun i : nat => alt_execR !!! (i + 1)%nat) 7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Section UShPipesStage.
  (* [UShPipeLaw]'s binder list, and C6's two classes *)
  Context `{HRg : !riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.

  (* THE ROUND ([UkPipesIface]'s section context, name for name) *)
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
  (* THE PRODUCER at the head of the line *)
  Context (pr : producer).
  (* the producer's loan ([UShPipesDefs.lrd]) *)
  Context (Rd : iProp Σ).
  Context (γc γm : wid -> gname).
  Context (P : nat -> pnames) (gF gG : nat -> gname).

  #[local] Instance stg_T_pers0 : Persistent T | 0 := gcT_pers CP.
  #[local] Instance stg_T_tl0 : Timeless T | 0 := gcT_tl CP.

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
  Local Notation QcR k := (QcK LM CP v I lR L pr Rd γc γm P k).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  (* ================================================================= *)
  (*  1.  A FAMILY WRITER'S DIAGNOSTIC, as sh's exec-failed law          *)
  (* ================================================================= *)

  (* [UkShDiag.ush_execfail_law_at] at writer [w]'s source [s]: the
     credential opens into the writer's two halves and its deposit; the
     first byte fires the family, every further one steps it; the end
     hands the halves at the cursor the law stops at, with what the fire
     learnt of the flag *)
  Lemma exf_writer (w : wid) (s dg : list (bv 8)) (n : nat)
      (EX : wid -> list (bv 8) -> Prop) (Cr R Cd : iProp Σ) :
    w ∈ wsN -> (0 < n)%nat ->
    (forall p b, (p < n)%nat -> dg !! p = Some b -> s !! p = Some b) ->
    fire_okN wsN RUNN WITN termw TOKN w s EX ->
    (forall c, (0 < c < n)%nat -> cstep_okN wsN RUNN WITN termw TOKN w s c) ->
    FAM -∗
    □ (∀ w' s', ⌜EX w' s'⌝ -∗ pdepR w' s' -∗ pdepR w s ={↑pipeN}=∗ False) -∗
    □ (Cr -∗ R ∗ wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None ∗ pdepR w s) -∗
    □ (R -∗ wcurN γc w (1/2) n -∗ wmodeN γm w (1/2) (Some s) -∗
       (⌜termw w s = false⌝ ∨ ptkV T v I (S gen_id)) -∗ Cd) -∗
    UkShDiag.ush_execfail_law_at (SG := uexecSG_xv6) (PS := uprogSG_free) dg n Cr Cd.
  Proof using Hadmit Hcons Hext HlR Hfc Hplok.
    intros Hw Hn Hdg Hok Hst.
    iIntros "#Hinv #Hex #Hsplit #Hend".
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hcr". destruct Hfd2 as [rb Hl2].
    iDestruct ("Hsplit" with "Hcr") as "(HR & Hc & Hm & Hd)".
    set (Pf := fun p : nat =>
                 (R ∗ match p with
                      | O => wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None ∗ pdepR w s
                      | S _ => wcurN γc w (1/2) p ∗ wmodeN γm w (1/2) (Some s)
                               ∗ (⌜termw w s = false⌝ ∨ ptkV T v I (S gen_id))
                      end)%I).
    iExists Pf.
    iSplitL "HR Hc Hm Hd"; [rewrite /Pf; iFrame |].
    iSplit.
    - iIntros "!>" (p b) "%Hb %Hp".
      iApply (ksh_w1_of_step (PS := uprogSG_free) N Pf l rb p b Hl2).
      iIntros "!>" (Φ) "HF HΦ". rewrite /Pf. iDestruct "HF" as "[HR HF]".
      destruct p as [| p'].
      + iDestruct "HF" as "(Hc & Hm & Hd)".
        iApply (pipesV_fire g LM PV CP sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok pnsN (↑pipeN) (S gen_id)
                  γc γm termw TOKN pdepR (pdep_timeless LM PV sR lR L pr P gF gG) w s b EX Φ
                  pnsN_uart pnsN_pipeN Hw (Hdg 0%nat b Hp Hb) Hok
                  with "Hex Hinv Hc Hm Hd").
        iIntros "Hc Hm #HT". iApply "HΦ". iFrame "HR Hc Hm HT".
      + iDestruct "HF" as "(Hc & Hm & #HT)".
        iApply (pipesV_cstep g LM PV CP sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok pnsN (S gen_id)
                  γc γm termw TOKN pdepR (pdep_timeless LM PV sR lR L pr P gF gG) w s (S p') b Φ
                  pnsN_uart Hw ltac:(lia) (Hdg (S p') b Hp Hb) (Hst (S p') ltac:(lia))
                  with "Hinv Hc Hm").
        iIntros "Hc Hm _". iApply "HΦ". iFrame "HR Hc Hm HT".
    - iIntros "!> HF". rewrite /Pf. destruct n as [| n']; [lia |].
      iDestruct "HF" as "(HR & Hc & Hm & HT)". iApply ("Hend" with "HR Hc Hm HT").
  Qed.

  (* the diagnostic's bytes are the family source's, up to the prompt *)
  Lemma dg_app_lookup (s u : list (bv 8)) (p : nat) (b : bv 8) :
    (p < length s)%nat -> (s ++ u) !! p = Some b -> s !! p = Some b.
  Proof using . intros Hp Hb. by rewrite lookup_app_l in Hb. Qed.

  (* NAME THE LEAF, DO NOT SEARCH ([UShPipeLaw.pl_exf_at_pers0]'s note) *)
  #[local] Instance stg_exf_pers0 (dg : list (bv 8)) (n : nat) (Cr Cd : iProp Σ) :
    Persistent (UkShDiag.ush_execfail_law_at (SG := uexecSG_xv6) (PS := uprogSG_free)
                  dg n Cr Cd) | 0
    := UkShDiag.ush_execfail_law_at_persistent (SG := uexecSG_xv6) (PS := uprogSG_free)
         dg n Cr Cd.

  Local Lemma stg_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* THE ROUND'S FIRING PREMISE: every commit a process of the round
     makes is admitted by the model, or refuted by a committed deposit *)
  Hypothesis Hfire : forall w s, w ∈ wsN -> fire_src fcR pr L w s ->
    fire_okN wsN RUNN WITN termw TOKN w s (EXf fcR pr nc L w s).

  Lemma dg_execL_len : length dg_execL = 17%nat.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma dg_execR_len : length dg_execR = 16%nat.
  Proof using . vm_compute. reflexivity. Qed.

  (* ================================================================= *)
  (*  2.  ECHO AT THE HEAD: the left child of node 0                     *)
  (* ================================================================= *)

  (* what node 0 lends its left child: the first pipe's write side and
     side token, the stage's family writer, and the pending one-shot of
     the fork that makes it *)
  Definition echo_raw (γp : pipe_names) : iProp Σ :=
    (pipe_inv (P 0) γp L ∗ wcur (P 0) 0 ∗ pws_lb (P 0) [] ∗ side_L (P 0)
     ∗ wcurN γc (WLeft 0) (1/2) 0 ∗ wmodeN γm (WLeft 0) (1/2) None ∗ osP (gG 0))%I.

  Lemma stage_echo `{!Persistent Rd} (ws : list (list (bv 8))) (s0 : Z) (gs : nat -> bv 8)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γp : pipe_names) (q szv : Z)
      (ld : list fdstate) (av : nat) :
    pr = PrEcho ws -> line_ok ws -> echo_argv_bytes ws gs -> L = wl_line (drop 1 ws) ->
    (0 < nc)%nat ->
    ukn_pay N' = (fun _ : Z => QcR 0) ->
    m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ->
    UShEchoPipePay.ush_fd1pipe γp ld -> UkSh.ush_fd2p ld -> (6 <= av)%nat ->
    FAM -∗ UShEcho.sh_echo_slot T -∗
    shk_code (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
    ush_cmd (ukn_d N') q (echo_cmd ws s0 gs) -∗
    usz (ukn_s N') szv -∗ UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    echo_raw γp -∗ Rd -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m' (mword_of_int ShSyms.runcmd)
      (2 + (UkShDiag.ush_Dg + av)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hfire Hkill Hplok pnsRegG0.
    intros Hpr Hok Hbytes HLw Hn Hpeq Ha0 Hfd1 Hfd2 Hav.
    assert (Hdg0 : dg_execL = dg_st pr 0) by (rewrite Hpr; reflexivity).
    iIntros "#Hinv #Hslot #Hcode #Hjt #Hcmd Hsz Hstd Hcwd Hch Hraw #HRd Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iDestruct "Hraw" as "(#Hpi & Hw & #Hlb & HsL & Hcw & Hmw & HG)".
    iApply stg_fupd_mwp. iMod (os_shoot with "HG") as "#HGs". iModIntro.
    assert (Hw0 : WLeft 0 ∈ wsN) by (apply wids_elem; exact Hn).
    set (Cr := (wcur (P 0) 0 ∗ side_L (P 0)
                ∗ wcurN γc (WLeft 0) (1/2) 0 ∗ wmodeN γm (WLeft 0) (1/2) None)%I).
    set (Cd := (side_L (P 0) ∗ pns_wfin γc γm (WLeft 0) (Some dg_execL))%I).
    (* ---- THE EXEC SUPPLY, AT C6'S ENTRY ---- *)
    iPoseProof (sh_exec_sup_echo_pipe_of_entry ws (QcR 0) Cr T γp Hok
                  with "[] [] Hslot") as "#Hsup".
    { iIntros "!>" (M s1 t1 g1 sts cs pidv rb) "%Hi1 %Hb1 %Hl1 %Hr1 #Hnp".
      iApply (image_entry_pay_mono ElfUser.echo_elf M (mword_of_int (t1 + 8) : mword 64)
                sts FsImg.ROOTINO cs pidv (fun _ : Z => QcR 0)
                (pns_echo_lend LM CP L γc γm (P 0) γp (fun _ : Z => QcR 0)) Cr uslot
                with "[] [Hnp]").
      - iIntros "!> (Hw & HsL & Hcw & Hmw)". rewrite /pns_echo_lend.
        iFrame "Hpi Hw Hlb". rewrite /pns_xkQ.
        iIntros "[#HT | [Hf _]]"; [by iLeft |].
        cbn [pns_final snd].
        iDestruct "Hf" as "[Hf | Hw0]"; last first.
        { (* the write end untouched: [WrNone] *)
          iRight. iLeft. iFrame "HsL". iSplitR; [rewrite /lrd; iExact "HRd" |]. rewrite /lrep. iExists None.
          cbn [pns_wfin]. iFrame "Hcw Hmw". iRight. iExists WrNone.
          cbn [wr_final]. rewrite /wtok.
          iSplitL "Hw0"; [iExact "Hw0" | iPureIntro; intros D HD; discriminate HD]. }
        rewrite /pns_lexit.
        iDestruct "Hf" as "[Hf | [Hf | #Hta]]"; last first.
        { iLeft. rewrite Hkill. iExact "Hta". }
        + iDestruct "Hf" as (c) "(%HcL & [Hw' #Hlb'] & #Hro)".
          iRight. iLeft. iFrame "HsL". iSplitR; [rewrite /lrd; iExact "HRd" |]. rewrite /lrep. iExists None.
          cbn [pns_wfin]. iFrame "Hcw Hmw". iRight. iExists (WrHalt (take c L)).
          cbn [wr_final]. iSplitL; [| iPureIntro; intros D HD; discriminate HD].
          iExists c. iFrame "Hw' Hro". done.
        + iDestruct "Hf" as "[Hw' #Hlb']".
          iRight. iLeft. iFrame "HsL". iSplitR; [rewrite /lrd; iExact "HRd" |]. rewrite /lrep. iExists None.
          cbn [pns_wfin]. iFrame "Hcw Hmw". iRight. iExists (WrAll L).
          cbn [wr_final]. rewrite firstn_all.
          iSplitL; [| iPureIntro; intros D HD; by injection HD as <-].
          iFrame "Hlb'". by iLeft.
      - iApply (pse_echo_image_entry (PS := uprogSG_free) g LM PV CP sd WA Hext Hcons Hkill Hsup
                  v I sR lR HlR Hfc Hadmit Hplok L HL31 termw TOKN pdepR (pdep_timeless LM PV sR lR L pr P gF gG)
                  γc γm ws M s1 t1 g1 sts FsImg.ROOTINO cs pidv rb (fun _ : Z => QcR 0)
                  (P 0) γp (fun _ _ => eq_refl) Hok Hi1 Hb1 Hl1 Hr1 HLw
                  with "Hnp []").
        iApply UexecExecMint.udep_free. }
    { iIntros "!> #Ht". rewrite Hkill. by iLeft. }
    (* ---- THE EXEC-FAILED LAW: the stage's family writer ---- *)
    iAssert (UkShDiag.ush_execfail_law (SG := uexecSG_xv6) (PS := uprogSG_free) Cr Cd)%I
      as "#Hxl".
    { rewrite /UkShDiag.ush_execfail_law.
      iApply (exf_writer (WLeft 0) dg_execL EchoDisc.alt_execfail 17%nat
                (EXf fcR pr nc L (WLeft 0) dg_execL) Cr (side_L (P 0)) Cd Hw0 ltac:(lia)
                ltac:(intros p b Hp Hb; rewrite alt_execfail_app in Hb;
                      exact (dg_app_lookup dg_execL u_prompt p b
                               ltac:(rewrite dg_execL_len; lia) Hb))
                (Hfire (WLeft 0) dg_execL Hw0 (or_introl (or_introl Hdg0)))
                ltac:(intros c Hcx; apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WLeft 0) dg_execL c);
                      [lia | rewrite dg_execL_len; lia | intros k Hk; discriminate Hk])
                with "Hinv [] [] []").
      - iApply (pexcl_left LM PV sR lR L pr P gF gG 0 dg_execL Hn ltac:(vm_compute; discriminate)).
        rewrite /pinv. iExists γp. cbn [prevP flow_U]. iExact "Hpi".
      - iIntros "!> (Hw & HsL & Hcw & Hmw)". iFrame "HsL Hcw Hmw".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft 0) dg_execL
                   ltac:(vm_compute; discriminate) (or_introl (or_introl Hdg0))) /pdep_ne.
        rewrite bool_decide_true; [| left; exact Hdg0].
        iFrame "Hw HGs". rewrite /shotsF. done.
      - iIntros "!> HsL Hcw Hmw _". rewrite /Cd. iFrame "HsL".
        cbn [pns_wfin]. rewrite dg_execL_len. iFrame "Hcw Hmw". }
    (* ---- ...AND THE ARM ---- *)
    replace (2 + (UkShDiag.ush_Dg + av))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat by lia.
    iApply (UkShEcho.wp_kshr_exec_echo_at_holds (SG := uexecSG_xv6) (PS := uprogSG_free)
              (UShEchoPipePay.ush_fd1pipe γp) ws (fun _ : Z => QcR 0) Cr Cd
              N' Hc h' m' q szv s0 gs ld (av - 6)%nat Hok Hpeq Ha0 Hbytes Hfd1 Hfd2
              with "Hcode Hsup Hxl [] Hjt Hcmd Hsz Hstd Hcwd [Hch] [Hw HsL Hcw Hmw] Hrun").
    - iIntros "!> [HsL Hf]". iRight. iLeft. iFrame "HsL". iSplitR; [rewrite /lrd; iExact "HRd" |]. rewrite /lrep.
      iExists (Some dg_execL). iFrame "Hf". iLeft. iPureIntro.
      exists dg_execL. split; [reflexivity | left; exact Hdg0].
    - iApply (UserChildren.uch_any_of with "Hch").
    - rewrite /Cr. iFrame.
  Qed.

  (* ================================================================= *)
  (*  2b. THE PRODUCER'S STAGE LAW, and [cat f] AT THE HEAD              *)
  (* ================================================================= *)

  (* WHAT NODE 0'S LEFT CHILD DOES, whatever the producer: sh's exec arm
     at the stage's command [args0], on node 0's lend [echo_raw], paying
     node 0's side-tagged report.  Echo's is [stage_echo]
     ([stage_echo_law]); [cat f]'s is [stage_catf] at the entry C9d'
     builds ([stage_catf_law]). *)
  Definition prod_stage_law (args0 : list uarg) : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γp : pipe_names) (q szv : Z)
          (ld : list fdstate) (av : nat),
          ⌜ukn_pay N' = (fun _ : Z => QcR 0)⌝ -∗
          ⌜m' !!! Regidx a0_idx = (mword_of_int q : mword 64)⌝ -∗
          ⌜UShEchoPipePay.ush_fd1pipe γp ld⌝ -∗ ⌜UkSh.ush_fd2p ld⌝ -∗ ⌜(6 <= av)%nat⌝ -∗
          shk_code (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
          ush_cmd (ukn_d N') q (UExec args0) -∗
          usz (ukn_s N') szv -∗ UserFd.ustd (ukn_fd N') ld -∗
          UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
          UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
          echo_raw γp -∗ Rd -∗
          urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m' (mword_of_int ShSyms.runcmd)
            (2 + (UkShDiag.ush_Dg + av)) -∗
          mWP (Loop : expr riscv_lang)))%I.

  Global Instance prod_stage_law_persistent args0 : Persistent (prod_stage_law args0) | 0.
  Proof using . rewrite /prod_stage_law. apply bi.intuitionistically_persistent. Qed.

  Lemma stage_echo_law `{!Persistent Rd} (ws : list (list (bv 8))) (s0 : Z) (gs : nat -> bv 8) :
    pr = PrEcho ws -> line_ok ws -> echo_argv_bytes ws gs -> L = wl_line (drop 1 ws) ->
    (0 < nc)%nat ->
    FAM -∗ UShEcho.sh_echo_slot T -∗
    prod_stage_law (UkShMain.ush_args s0 gs (echo_toks ws)).
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hfire Hkill Hplok pnsRegG0.
    intros Hpr Hok Hbytes HLw Hn. iIntros "#Hfam #Hes". rewrite /prod_stage_law.
    iIntros "!>" (N' h' m' γp q szv ld av) "%Hpeq %Ha0 %Hfd1 %Hfd2 %Hav #Hck #Hjt #Hcmd".
    iIntros "Hsz Hstd Hcwd Hch Hraw HRd Hrun".
    iApply (stage_echo ws s0 gs N' h' m' γp q szv ld av Hpr Hok Hbytes HLw Hn Hpeq Ha0
              Hfd1 Hfd2 Hav with "Hfam Hes Hck Hjt Hcmd Hsz Hstd Hcwd Hch Hraw HRd Hrun").
  Qed.

  (* what the head stage holds at its exec: the first pipe's write permit,
     its side token and the stage's family writer ([stage_echo]'s [Cr]) *)
  Definition prod_cr : iProp Σ :=
    (wcur (P 0) 0 ∗ side_L (P 0)
     ∗ wcurN γc (WLeft 0) (1/2) 0 ∗ wmodeN γm (WLeft 0) (1/2) None)%I.


  (* [cat f] AT THE HEAD is [UShCatFStage.stage_catf]: the exec arm at the
     words [cat f] on node 0's lend with the producer's loan (the deed) --
     the EXEC SUCCEEDS arm the entry C9d' builds, the EXEC FAILS arm the
     stage's family writer at [exec cat failed], the loan back in both. *)

  #[local] Instance stg_kit_pers0 w s : Persistent (pkitR w s) | 0 :=
    pns_kit_persistent LM PV I sR lR termw TOKN pdepR w s.

  Lemma cons_short_A2 : cons_short [[]; cat_dg_write].
  Proof using . rewrite /cons_short. repeat constructor; vm_compute; reflexivity. Qed.

  (* a halted cat's deposit: a middle cat, or the [cat f] producer *)
  Lemma pdep_left_write (k : nat) :
    (k <> 0%nat \/ prod_halts fcR pr) -> shotsF gF k -∗ osS (gG k) -∗ pdepR (WLeft k) cat_dg_write.
  Proof using .
    intros Hk. iIntros "#Hs #HG".
    rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft k) cat_dg_write
               ltac:(vm_compute; discriminate) (or_intror (conj Hk eq_refl))) /pdep_ne.
    rewrite bool_decide_false; [| intros Hq; exact (fail_src_ne_write pr k _ Hq eq_refl)].
    iFrame "Hs HG".
  Qed.

  (* ================================================================= *)
  (*  3.  A MIDDLE CAT: the left child of node [k = S k']                *)
  (* ================================================================= *)

  (* what node [k] lends its left child: the input pipe's read permit (its
     own fd 0's), the output pipe's write side and side token, the stage's
     family writer, the pending one-shot of the fork that makes it, and the
     shots above it *)
  Definition mid_raw (k' : nat) (gin γp : pipe_names) : iProp Σ :=
    ((∃ prev, pipe_invU (P k') gin L (flow_U L prev))
     ∗ pipe_invU (P (S k')) γp L (flow_U L (Some (P k')))
     ∗ rcur (P k') 0 ∗ wcur (P (S k')) 0 ∗ pws_lb (P (S k')) [] ∗ side_L (P (S k'))
     ∗ wcurN γc (WLeft (S k')) (1/2) 0 ∗ wmodeN γm (WLeft (S k')) (1/2) None
     ∗ osP (gG (S k')) ∗ shotsF gF (S k'))%I.

  Definition mid_fd0 (gin γp : pipe_names) (l : list fdstate) : Prop :=
    (exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe gin)))
    /\ (exists rb, l !! 1%nat = Some (FdOpen rb true (FdPipe γp)))
    /\ (exists rb, l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE))).

  Lemma stage_mid (k' a b : nat) (s0 : Z) (gs : nat -> bv 8)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (gin γp : pipe_names) (q szv : Z)
      (ld : list fdstate) (av : nat) :
    UkShCat.cat_argv_bytes a b gs -> (S k' < nc)%nat ->
    ukn_pay N' = (fun _ : Z => QcR (S k')) ->
    m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ->
    mid_fd0 gin γp ld -> (6 <= av)%nat ->
    FAM -∗ UShCatPay.sh_cat_slot T -∗
    shk_code (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
    ush_cmd (ukn_d N') q (UkShCat.cat_cmd a b s0 gs) -∗
    usz (ukn_s N') szv -∗ UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    mid_raw k' gin γp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m' (mword_of_int ShSyms.runcmd)
      (2 + (UkShDiag.ush_Dg + av)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hfire Hkill Hplok pnsRegG0 uartGhostG0.
    intros Hbytes Hk Hpeq Ha0 Hfd Hav.
    iIntros "#Hinv #Hslot #Hcode #Hjt #Hcmd Hsz Hstd Hcwd Hch Hraw Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iDestruct "Hraw" as "(#Hpin & #Hpo & Hr & Hw & #Hlb & HsL & Hcw & Hmw & HG & #Hsk)".
    iApply stg_fupd_mwp. iMod (os_shoot with "HG") as "#HGs". iModIntro.
    assert (Hwk : WLeft (S k') ∈ wsN) by (apply wids_elem; exact Hk).
    assert (Hfd2 : UkSh.ush_fd2p ld) by (destruct Hfd as (_ & _ & Hf2); exact Hf2).
    iAssert (pinv L P (S k')) as "#Hpk".
    { rewrite /pinv. iExists γp. cbn [prevP]. iExact "Hpo". }
    iAssert (pkitR (WLeft (S k')) cat_dg_write) as "#Hkw".
    { rewrite /pns_kit. iSplit.
      - iExists (EXf fcR pr nc L (WLeft (S k')) cat_dg_write). iSplitR.
        + iPureIntro. apply (Hfire (WLeft (S k')) cat_dg_write Hwk).
          cbn [fire_src]. right. split; [left; lia | reflexivity].
        + iApply (pexcl_left LM PV sR lR L pr P gF gG (S k') cat_dg_write Hk
                    ltac:(vm_compute; discriminate) with "Hpk").
      - iPureIntro. intros c [Hc0 Hcl].
        apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WLeft (S k')) cat_dg_write c Hc0 Hcl).
        intros j Hj; discriminate Hj. }
    set (A2 := [[]; cat_dg_write]).
    set (Cr := (rcur (P k') 0 ∗ wcur (P (S k')) 0 ∗ side_L (P (S k'))
                ∗ wcurN γc (WLeft (S k')) (1/2) 0 ∗ wmodeN γm (WLeft (S k')) (1/2) None)%I).
    set (Cd := (side_L (P (S k')) ∗ pns_wfin γc γm (WLeft (S k')) (Some dg_execR))%I).
    replace (2 + (UkShDiag.ush_Dg + av))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat by lia.
    iApply (wp_kshr_exec_cat_paid_of_entry (PS := uprogSG_free) (mid_fd0 gin γp) a b T
              (QcR (S k')) Cr Cd N' Hc h' m' q szv s0 gs ld (av - 6)%nat
              Hpeq Ha0 Hbytes Hfd Hfd2
              with "[] [] Hslot Hcode [] [] Hjt Hcmd Hsz Hstd Hcwd [Hch] [Hr Hw HsL Hcw Hmw] Hrun").
    - iIntros "!> #Ht". rewrite Hkill. by iLeft.
    - (* ---- THE EXEC SUPPLY, AT C6'S ENTRY ---- *)
      iIntros "!>" (M s1 t1 g1 sts cs pidv) "%Ht1 %Hs1 %Hb1 %Hi1 %Hl1 %Hf1 #Hnp".
      destruct Hf1 as ([wb Hr0] & [rb1 Hr1] & [rb2 Hr2]).
      iApply (image_entry_pay_mono ElfUser.cat_elf M (mword_of_int (t1 + 8) : mword 64)
                sts FsImg.ROOTINO cs pidv (fun _ : Z => QcR (S k'))
                (pns_copy_lend g LM PV CP v I sR lR L termw TOKN pdepR γc γm (WLeft (S k')) A2 A2
                   (P k') gin (CSPipe (P (S k')) γp) (fun _ : Z => QcR (S k'))) Cr uslot
                with "[] [Hnp]").
      + iIntros "!> (Hr & Hw & HsL & Hcw & Hmw)". rewrite /pns_copy_lend.
        iSplitR; [cbn [pns_pk_inv]; iFrame "Hpin Hpo" |].
        iFrame "Hr". iSplitL "Hw".
        { rewrite /pns_sink take_0. iFrame "Hw Hlb". }
        iSplitR.
        { iPureIntro. split_and!; [exact cons_short_A2 | exact Hwk | done]. }
        iSplitR; [iExact "Hinv" |]. iFrame "Hcw Hmw".
        iSplitR.
        { rewrite /A2. iSplitR; [by iLeft |]. iSplitR; [| done]. iRight.
          iFrame "Hkw". iApply (pdep_left_write (S k') ltac:(left; lia) with "Hsk HGs"). }
        rewrite /pns_xkQ. iIntros "[#HT | (Hf0 & Hf1 & _)]"; [by iLeft |].
        cbn [pns_final snd].
        iDestruct "Hf0" as (o) "[_ Ho]".
        iRight. iLeft. iFrame "HsL". iSplitR; [iApply lrd_S |]. rewrite /lrep. iExists o. iFrame "Ho". iRight.
        iDestruct "Hf1" as "[Hf1 | Hf1]".
        * iDestruct "Hf1" as (c) "(#Heof & _ & Hw' & #Hlb')".
          iExists (WrAll (take c L)). cbn [wr_final]. iFrame "Hlb'".
          iSplitL "Hw'".
          { destruct (decide (length L <= c)%nat) as [Hge | Hlt].
            - iLeft. iPureIntro. by rewrite take_ge.
            - iRight. rewrite length_take Nat.min_l; [iExact "Hw'" | lia]. }
          iExists (RdEof (take c L)). cbn [rd_final]. iFrame "Heof".
          iPureIntro. intros D HD. injection HD as <-. reflexivity.
        * iDestruct "Hf1" as (c wc) "(_ & Hw' & #Hro)".
          iExists (WrHalt (take wc L)). cbn [wr_final].
          iSplitL "Hw'"; [iExists wc; iFrame "Hw' Hro"; done |].
          iExists RdGone. cbn [rd_final]. iSplit; [done |].
          iPureIntro. intros D HD. discriminate HD.
      + iApply (pse_mid_image_entry (PS := uprogSG_free) g LM PV CP sd WA Hext Hcons Hkill Hsup
                  v I sR lR HlR Hfc Hadmit Hplok L HL31 termw TOKN pdepR (pdep_timeless LM PV sR lR L pr P gF gG)
                  γc γm a b M s1 t1 g1 sts FsImg.ROOTINO cs pidv (fun _ : Z => QcR (S k'))
                  (WLeft (S k')) A2 A2 (P k') gin (P (S k')) γp wb rb1 rb2
                  (fun _ _ => eq_refl) Ht1 Hs1 Hb1 Hi1 Hl1 Hr0 Hr1 Hr2
                  (elem_of_list_here _ _) (elem_of_list_further _ _ _ (elem_of_list_here _ _))
                  with "Hnp []").
        iApply UexecExecMint.udep_free.
    - (* ---- THE EXEC-FAILED LAW: the stage's family writer ---- *)
      iApply (exf_writer (WLeft (S k')) dg_execR alt_execR 16%nat
                (EXf fcR pr nc L (WLeft (S k')) dg_execR) Cr (side_L (P (S k'))) Cd Hwk ltac:(lia)
                ltac:(intros p b' Hp Hb; exact (dg_app_lookup dg_execR u_prompt p b'
                               ltac:(rewrite dg_execR_len; lia) Hb))
                (Hfire (WLeft (S k')) dg_execR Hwk (or_introl (or_introl eq_refl)))
                ltac:(intros c Hcx;
                      apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WLeft (S k')) dg_execR c);
                      [lia | rewrite dg_execR_len; lia | intros j Hj; discriminate Hj])
                with "Hinv [] [] []").
      + iApply (pexcl_left LM PV sR lR L pr P gF gG (S k') dg_execR Hk (dg_st_ne pr (S k'))
                  with "Hpk").
      + iIntros "!> (_ & Hw & HsL & Hcw & Hmw)". iFrame "HsL Hcw Hmw".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft (S k')) dg_execR (dg_st_ne pr (S k'))
                   (or_introl (or_introl eq_refl)))
          /pdep_ne.
        rewrite bool_decide_true; [| by left].
        iFrame "Hw HGs Hsk".
      + iIntros "!> HsL Hcw Hmw _". rewrite /Cd. iFrame "HsL".
        cbn [pns_wfin]. rewrite dg_execR_len. iFrame "Hcw Hmw".
    - iIntros "!> [HsL Hf]". iRight. iLeft. iFrame "HsL". iSplitR; [iApply lrd_S |]. rewrite /lrep.
      iExists (Some dg_execR). iFrame "Hf". iLeft. iPureIntro.
      exists dg_execR. split; [reflexivity | by left].
    - iApply (UserChildren.uch_any_of with "Hch").
    - rewrite /Cr. iFrame.
  Qed.

  (* ================================================================= *)
  (*  4.  THE LAST CAT: the right child of the last node [m]             *)
  (* ================================================================= *)

  (* what node [m] lends its right child: the last pipe's read side and
     right side token, the content writer, the pending one-shot of the fork
     that makes it, the shots above it, and every pipe's invariant (the
     flow chain its first byte runs) *)
  Definition last_raw (m : nat) (γp : pipe_names) : iProp Σ :=
    (pipe_invU (P m) γp L (flow_U L (prevP P m)) ∗ ([∗ list] i ∈ seq 0 nc, pinv L P i)
     ∗ rcur (P m) 0 ∗ side_R (P m)
     ∗ wcurN γc WLast (1/2) 0 ∗ wmodeN γm WLast (1/2) None
     ∗ osP (gF m) ∗ shotsF gF m)%I.

  Definition last_fd0 (γp : pipe_names) (l : list fdstate) : Prop :=
    (exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe γp)))
    /\ (exists rb, l !! 1%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)))
    /\ (exists rb, l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE))).

  Lemma wsub_last (m : nat) : nc = S m -> wsub lR (S m) = [WLast].
  Proof using . intros Hm. rewrite /wsub Hm Nat.sub_diag. reflexivity. Qed.

  Lemma stage_last (m a b : nat) (s0 : Z) (gs : nat -> bv 8)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γp : pipe_names) (q szv : Z)
      (ld : list fdstate) (av : nat) :
    UkShCat.cat_argv_bytes a b gs -> nc = S m ->
    ukn_pay N' = (fun _ : Z => QcR m) ->
    m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ->
    last_fd0 γp ld -> (6 <= av)%nat ->
    FAM -∗ UShCatPay.sh_cat_slot T -∗
    shk_code (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
    ush_cmd (ukn_d N') q (UkShCat.cat_cmd a b s0 gs) -∗
    usz (ukn_s N') szv -∗ UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    last_raw m γp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m' (mword_of_int ShSyms.runcmd)
      (2 + (UkShDiag.ush_Dg + av)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hfire Hkill Hplok pnsRegG0 uartGhostG0.
    intros Hbytes Hm Hpeq Ha0 Hfd Hav.
    iIntros "#Hinv #Hslot #Hcode #Hjt #Hcmd Hsz Hstd Hcwd Hch Hraw Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iDestruct "Hraw" as "(#Hpo & #Hinvs & Hr & HsR & Hcw & Hmw & HF & #Hsm)".
    iApply stg_fupd_mwp. iMod (os_shoot with "HF") as "#HFs". iModIntro.
    iDestruct (shotsF_snoc with "Hsm HFs") as "#Hsn". rewrite -Hm.
    assert (Hwl : WLast ∈ wsN) by (apply wids_elem; done).
    assert (Hfd2 : UkSh.ush_fd2p ld) by (destruct Hfd as (_ & _ & Hf2); exact Hf2).
    (* THE CONTENT WRITER'S KIT AND DEPOSIT, at a nonempty line *)
    iAssert (⌜L = []⌝ ∨ (pkitR WLast L
               ∗ □ (pws_lb (P (nc - 1)) (take 1 L) ={↑pipeN}=∗ pdepR WLast L)))%I as "#Hkd".
    { destruct (decide (L = [])) as [HL0 | HLne]; [by iLeft |]. iRight. iSplit.
      - rewrite /pns_kit. iSplit.
        + iExists (EXf fcR pr nc L WLast L). iSplitR.
          * iPureIntro. exact (Hfire WLast L Hwl (or_introl (conj eq_refl HLne))).
          * iApply (pexcl_last LM PV sR lR L pr P gF gG L HLne with "Hinvs").
        + iPureIntro. intros c [Hc0 Hcl].
          apply (cstep_okV_tok LM PV I sR lR HlR Hadmit WLast L c Hc0 Hcl).
          intros j Hj; discriminate Hj.
      - iApply (pdep_last_of_lb LM PV sR lR L pr P gF gG HLne ltac:(lia) with "Hsn Hinvs"). }
    replace (nc - 1)%nat with m by lia.
    set (Cr := (rcur (P m) 0 ∗ side_R (P m)
                ∗ wcurN γc WLast (1/2) 0 ∗ wmodeN γm WLast (1/2) None)%I).
    set (Cd := (side_R (P m) ∗ pns_wfin γc γm WLast (Some dg_execR))%I).
    replace (2 + (UkShDiag.ush_Dg + av))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat by lia.
    iApply (wp_kshr_exec_cat_paid_of_entry (PS := uprogSG_free) (last_fd0 γp) a b T
              (QcR m) Cr Cd N' Hc h' m' q szv s0 gs ld (av - 6)%nat
              Hpeq Ha0 Hbytes Hfd Hfd2
              with "[] [] Hslot Hcode [] [] Hjt Hcmd Hsz Hstd Hcwd [Hch] [Hr HsR Hcw Hmw] Hrun").
    - iIntros "!> #Ht". rewrite Hkill. by iLeft.
    - (* ---- THE EXEC SUPPLY, AT C6'S ENTRY (fd 2 mute) ---- *)
      iIntros "!>" (M s1 t1 g1 sts cs pidv) "%Ht1 %Hs1 %Hb1 %Hi1 %Hl1 %Hf1 #Hnp".
      destruct Hf1 as ([wb Hr0] & [rb1 Hr1] & [rb2 Hr2]).
      iApply (image_entry_pay_mono ElfUser.cat_elf M (mword_of_int (t1 + 8) : mword 64)
                sts FsImg.ROOTINO cs pidv (fun _ : Z => QcR m)
                (pns_copy_lend_m g LM PV CP v I sR lR L termw TOKN pdepR γc γm (P m) γp (CSCon WLast)
                   (fun _ : Z => QcR m)) Cr uslot
                with "[] [Hnp]").
      + iIntros "!> (Hr & HsR & Hcw & Hmw)". rewrite /pns_copy_lend_m.
        iSplitR; [cbn [pns_pk_inv]; iSplit; [iExists (prevP P m); iExact "Hpo" | done] |].
        iFrame "Hr". iSplitL "Hcw Hmw".
        { rewrite /pns_sink. iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hinv" |].
          iSplitR; [iExact "Hkd" |]. cbn [pns_cmode]. iFrame "Hcw Hmw". }
        rewrite /pns_xkQ. iIntros "[#HT | (_ & Hf1 & _)]"; [by iLeft |].
        cbn [pns_final snd].
        iDestruct "Hf1" as (c) "(%HcL & #Heof & _ & Hcw & Hmw)".
        iRight. iRight. iFrame "HsR". rewrite /rrep.
        iExists (RdEof (take c L)). replace (S m - 1)%nat with m by lia.
        cbn [rd_final]. iFrame "Heof". iLeft. rewrite /sufN.
        destruct c as [| c'].
        * iExists None. iSplitR; [iPureIntro; intros c Hc'; discriminate Hc' |].
          iSplitL; [| rewrite (wsub_last m Hm) big_sepL_singleton; done].
          rewrite /wlast /wfin. iExists None.
          cbn [pns_wfin pns_cmode]. iFrame "Hcw Hmw". iPureIntro. intros s Hs; discriminate Hs.
        * iExists (Some (S c')). iSplitR.
          { iPureIntro. intros c Hc'. injection Hc' as <-. reflexivity. }
          iSplitL; [| rewrite (wsub_last m Hm) big_sepL_singleton; done].
          rewrite /wlast. cbn [pns_cmode]. iFrame "Hcw Hmw".
          iPureIntro. lia.
      + iApply (pse_last_image_entry_m (PS := uprogSG_free) g LM PV CP sd WA Hext Hcons Hkill Hsup
                  v I sR lR HlR Hfc Hadmit Hplok L HL31 termw TOKN pdepR (pdep_timeless LM PV sR lR L pr P gF gG)
                  γc γm a b M s1 t1 g1 sts FsImg.ROOTINO cs pidv (fun _ : Z => QcR m)
                  (P m) γp WLast wb rb1 rb2
                  (fun _ _ => eq_refl) Ht1 Hs1 Hb1 Hi1 Hl1 Hr0 Hr1 Hr2
                  with "Hnp []").
        iApply UexecExecMint.udep_free.
    - (* ---- THE EXEC-FAILED LAW: the content writer ---- *)
      iApply (exf_writer WLast dg_execR alt_execR 16%nat
                (EXf fcR pr nc L WLast dg_execR) Cr (side_R (P m)) Cd Hwl ltac:(lia)
                ltac:(intros p b' Hp Hb; exact (dg_app_lookup dg_execR u_prompt p b'
                               ltac:(rewrite dg_execR_len; lia) Hb))
                (Hfire WLast dg_execR Hwl (or_intror eq_refl))
                ltac:(intros c Hcx;
                      apply (cstep_okV_tok LM PV I sR lR HlR Hadmit WLast dg_execR c);
                      [lia | rewrite dg_execR_len; lia | intros j Hj; discriminate Hj])
                with "Hinv [] [] []").
      + iApply (pexcl_last LM PV sR lR L pr P gF gG dg_execR (dg_st_ne pr 1) with "Hinvs").
      + iIntros "!> (_ & HsR & Hcw & Hmw)". iFrame "HsR Hcw Hmw".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG WLast dg_execR (dg_st_ne pr 1)
                   (or_intror eq_refl)) /pdep_ne.
        iFrame "Hsn". case_bool_decide as Hq; [| done]. iRight. by iPureIntro.
      + iIntros "!> HsR Hcw Hmw _". rewrite /Cd. iFrame "HsR".
        cbn [pns_wfin]. rewrite dg_execR_len. iFrame "Hcw Hmw".
    - iIntros "!> [HsR Hf]". iRight. iRight. iFrame "HsR". rewrite /rrep.
      iExists RdGone. replace (S m - 1)%nat with m by lia. cbn [rd_final].
      iSplitR; [done |]. iLeft. rewrite /sufN.
      iExists None. iSplitR; [iPureIntro; intros c Hc'; discriminate Hc' |].
      iSplitL; [| rewrite (wsub_last m Hm) big_sepL_singleton; done]. rewrite /wlast /wfin. iExists (Some dg_execR). iFrame "Hf".
      iPureIntro. intros s Hs. reflexivity.
    - iApply (UserChildren.uch_any_of with "Hch").
    - rewrite /Cr. iFrame.
  Qed.
End UShPipesStage.
