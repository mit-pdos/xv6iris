(* ===================================================================== *)
(* UShPipesLaw.v -- THE PIPE CHILD'S LAW AT ANY NUMBER OF CATS (cut C8). *)
(*                                                                        *)
(* The main loop forks a child on a line [echo ws | cat | ... | cat]       *)
(* ([PipesCut.pipes_lp], [n >= 1] cats) holding the era's lend at the     *)
(* widened credential [UkShPipesFork.pterm_wcN].  The child                *)
(*   - parses the line ([UkShPipesRound.wp_kshm_child_pipes_g], the        *)
(*     lexer's stages read off the line by [PipesCut.lines_of_pipe]);     *)
(*   - allocates the round: a pipe and two one-shot names per node, and   *)
(*     the N-writer family out of the lend ([PipeOutN.pipesN_alloc]);     *)
(*   - runs the right spine ([UShPipesNode.wp_pipes_round_alloc]) at the   *)
(*     cut the parser made ([PipesCut.pcut_echo_bytes] /                  *)
(*     [pcut_cat_bytes]),                                                  *)
(* and exits paying [UkShFork.ushf_wq pterm_wcN I]: the taint, the round   *)
(* committed ([pdone_shapeN]) or a fork failed at some node                *)
(* ([pterm_shapeN] at cursor 5) -- [pipes_fin] reads the round's [Qtop]    *)
(* into it.                                                               *)
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
Require Import LineWords EchoDisc EchoOut AppEcho.
Require Import LineModel.
Require Import PipeOut.
Require Import PipesDisc PipeBothNPure PipeBothN PipeOutN PipeOutNEv.
Require Import PipeNames PipeProto.
Require Import AppCfg AppInv AppPipeClaim.
Require Import ProgTree.
Require Import CtxIdDefs.
Require Import UCodeShK UCodeShP.
Require Import UkSh UkShRun UkShMain UkShDiag UkShFork UkShMalloc.
Require Import UkShEcho UkShCat.
Require Import UkShPipe UkShPipeLex UkShPipesRound UkShPipesSeam UkShPipesLex UkShPipesCmd.
Require Import UShEcho UShCatPay.
Require Import UShPipeAssembly.
Require Import UkPipesIface.
Require Import GenLinksLine LinkRec.
Require Import PipesLinks PipesLinkInst.
Require Import UShPipesDefs UShPipesNode.
Require Import UkShPipesFork.
Require Import PipesUline PipesCut.
Require UkPipesEntries.
Require User.ShSyms.
Local Open Scope Z_scope.

Local Notation fcE := (fun _ : bytes => @None bytes).

(* ===================================================================== *)
(*  S0  PURE                                                             *)
(* ===================================================================== *)

(* the three rows the child law hands over are the whole tracked ledger *)
Lemma pls_fd_lowest_none (l : list fdstate) :
  length l = NSTD ->
  UkSh.ush_fd0c l -> UkSh.ush_fd1p l -> UkSh.ush_fd2p l ->
  fd_lowest_closed l = None.
Proof using.
  intros Hlen [wr0 H0] [rb1 H1] [rb2 H2].
  destruct l as [| a [| b [| c [| d tl]]]];
    try (exfalso; cbn in Hlen; unfold NSTD in Hlen; lia).
  cbn in H0, H1, H2.
  injection H0 as ->. injection H1 as ->. injection H2 as ->.
  reflexivity.
Qed.

Lemma nlines_pos_of_ws (I : list (bv 8)) : last_ws I <> [] -> (1 <= nlines I)%nat.
Proof using.
  rewrite /last_ws /nlines. destruct (bodies_of I) as [| b bs]; cbn [length].
  - intros H. exfalso. apply H. reflexivity.
  - intros _. lia.
Qed.

(* THE MODEL'S LINE at the input whose last body the loop typed *)
Lemma pls_lineN (I : list (bv 8)) (wsf ws : list (list (bv 8))) (n : nat) :
  wsf = last_ws I ->
  FileDisc.fline_ok (UkSh.ush_lastbody I) ->
  wsf = FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) n) ->
  FileDisc.uline_ok (FileDisc.LPipe (PrEcho ws) n) ->
  lineN fcE adm_echo I = LPipes (PrEcho ws) n.
Proof using.
  intros Hlws Hfb Hwsf Hok.
  destruct Hok as (Hws & Hn & Hlm).
  assert (Hb : UkSh.ush_lastbody I = FileDisc.line_body (FileDisc.LPipe (PrEcho ws) n)).
  { apply (fline_ok_pipes_words _ ws n Hfb Hws Hn).
    rewrite /UkSh.ush_lastbody -last_ws_lastbody -Hlws. exact Hwsf. }
  rewrite (_ : lineN fcE adm_echo I = pl_of (UkSh.ush_lastbody I)); [| reflexivity].
  rewrite Hb. apply pl_of_pipe_body.
  exact (pl_ok_of_uline_pipe ws n (conj Hws (conj Hn Hlm))).
Qed.

(* at most fifteen cats fit the line *)
Lemma pls_cats_le (ws : list (list (bv 8))) (n : nat) :
  FileDisc.uline_ok (FileDisc.LPipe (PrEcho ws) n) -> (n <= 16)%nat.
Proof using.
  intros (_ & _ & Hlm). rewrite line_bytes_pipe_length in Hlm.
  unfold EchoDisc.line_max in Hlm. lia.
Qed.

(* ===================================================================== *)
(*  S1  THE LAW                                                          *)
(* ===================================================================== *)
Section UShPipesLaw.
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
  Local Notation lE I := (lineN fcE adm_echo I).
  Local Notation pc0 ws := (Nat.add (length (wl_body ws)) 3).
  Local Notation RT ws n := (ushq_rtoks (pc0 ws) (replicate n ushq_cat)).
  (* the parser's stages, and the right spine's tail below the first cat *)
  Local Notation STG ws n len gf s0 :=
    (map (UkShMain.ush_args s0 (pcut ws n len gf)) (wl_toks ws :: RT ws n)).
  Local Notation REST ws n' len gf s0 :=
    (map (UkShMain.ush_args s0 (pcut ws (S n') len gf))
       (ushq_rtoks (pc0 ws + length ushq_cat + 3) (replicate n' ushq_cat))).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Context (rn : echo_names).
  Context (Heq : file_app = MkAppcfg echo_names (pipe_pred γ) rn).

  #[local] Instance pls_T_pers0 : Persistent T | 0 := echo_taint_persistent γ.

  Local Lemma pls_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* THE LEND AT THE LOOP'S LINE INDEX, as the family's allocation takes it *)
  Lemma pls_lend_blkN (I : list (bv 8)) :
    pipes_Wcl_at g I 3%nat -∗
    ∃ v : era_pins, era_pin γ (S gen_id) v ∗ (inp_lb v I ∨ T)
      ∗ pwc_blkN g fcE adm_echo v I (S gen_id) [] false.
  Proof using .
    rewrite /pipes_Wcl_at pipes_inst_lcred. iIntros "H".
    iDestruct "H" as (v) "[#Hpin Hc]". cbn [gwc_lpr].
    iExists v. iFrame "Hpin". rewrite /gwc_blk.
    iDestruct "Hc" as "[Hx | #HT]"; [| iSplitR; [by iRight | by iRight]].
    iDestruct "Hx" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & _)".
    iSplitR; [by iLeft |].
    destruct s0. rewrite /pwc_blkN /pwc_blkV. iLeft. iExists ps, cs, tt, P.
    rewrite ?Nat.add_0_r. cbn [lm_blkcs length]. rewrite ?Nat.add_0_r.
    iFrame "Htn Hps Hcs HE".
    iSplitR; [iPureIntro; split; [exact Hw | by destruct (lm_upto _ _ _ _ _)] |].
    rewrite /pledV. by iLeft.
  Qed.

  (* THE TOP NODE'S PAYMENT, read into the child's exit payload *)
  Lemma pipes_fin (v : era_pins) (I L : list (bv 8)) (pr : producer) (P : nat -> pnames)
      (gF gG : nat -> gname) (γc γm : wid -> gname) :
    adm_echo (lE I) = true -> pl_ok (lE I) -> (1 <= nlines I)%nat ->
    (era_pin γ (S gen_id) v ∗ (inp_lb v I ∨ T))
    ∗ blkN_inv (wids (lcats (lE I))) (runN fcE (lE I)) (pwc_blkN g fcE adm_echo v I)
        termw (tokN fcE (lE I)) (pdep fcE adm_echo I L pr P gF gG) pnsN (S gen_id) γc γm
    ∗ Qtop g fcE adm_echo v I γc γm
    ⊢ UkShFork.ushf_wq (pterm_wcN g) I.
  Proof using .
    intros Ha Hl Hpos.
    iIntros "((#Hpin & #Hi) & #Hinv & Hq)".
    rewrite (pterm_wqN_pay g I).
    iDestruct "Hi" as "[#Hlb | #HT]"; [| iApply (pterm_payN_taint g v I with "Hpin HT")].
    rewrite /Qtop. iDestruct "Hq" as "[#HT | [Hall | Hter]]".
    - iApply (pterm_payN_taint g v I with "Hpin HT").
    - (* committed *)
      rewrite /pterm_payN. iRight. iRight. rewrite /pdone_shapeN.
      iExists v, γc, γm, (pdep fcE adm_echo I L pr P gF gG).
      iSplitR; [iPureIntro; split_and!; [intros ??; apply pdep_timeless | exact Ha | exact Hl] |].
      iFrame "Hpin Hlb Hinv".
      iApply (big_sepL_mono with "Hall"). iIntros (k w _) "Hw".
      rewrite /wdone. iDestruct "Hw" as (s) "[Hw %Ht]".
      iEval (cbn [pns_wfin]) in "Hw". iDestruct "Hw" as "[Hc Hm]". iExists s. iFrame "Hc Hm". by iPureIntro.
    - (* a fork failed at node [i] *)
      iDestruct "Hter" as (i) "(%Hi & Hter & Hws)".
      rewrite /terT. iDestruct "Hter" as "(Hc & Hm & #Htk)".
      iAssert ([∗ list] j ∈ seq 0 i, ∃ s : list (bv 8),
                 wcurN γc (WLeft j) (1/2) (length s) ∗ wmodeN γm (WLeft j) (1/2) (Some s))%I
        with "[Hws]" as "Hws".
      { iApply (big_sepL_mono with "Hws"). iIntros (k j _) "Hw".
        rewrite /wdone. iDestruct "Hw" as (s) "[Hw _]".
        iEval (cbn [pns_wfin]) in "Hw". iExists s. iExact "Hw". }
      iDestruct (big_sepL_exist_fun [] (seq 0 i) _ (NoDup_seq 0 i) with "Hws") as (sw) "Hws".
      rewrite /pterm_payN. iRight. iLeft. rewrite /pterm_shapeN.
      iExists v, γc, γm, (pdep fcE adm_echo I L pr P gF gG), i, sw.
      iSplitR; [iPureIntro; split_and!; [intros ??; apply pdep_timeless | exact Ha | exact Hl | exact Hi
                                        | exact Hpos] |].
      iFrame "Hpin Hlb". rewrite /pwc_fork_exitN. iFrame "Hinv Hc Hm Htk".
      rewrite /heldN big_sepL_fmap. cbn [fst snd]. iExact "Hws".
  Qed.

  (* THE NODES' NAMES: a pipe and two one-shot names per node *)
  Lemma pls_nodes_alloc (n : nat) :
    ⊢ |==> ∃ (P : nat -> pnames) (gF gG : nat -> gname),
        [∗ list] j ∈ seq 0 n, osP (gF j) ∗ osP (gG j) ∗ pbundle (P j).
  Proof using .
    iAssert ([∗ list] j ∈ seq 0 n, |==> ∃ x : gname * gname * pnames,
               osP x.1.1 ∗ osP x.1.2 ∗ pbundle x.2)%I as "Hl".
    { iApply big_sepL_intro. iIntros "!>" (k j _).
      iMod os_alloc as (γ1) "H1". iMod os_alloc as (γ2) "H2".
      iMod pipe_names_alloc as (pn) "Hpn".
      iModIntro. iExists (γ1, γ2, pn). cbn [fst snd]. rewrite /pbundle.
      iFrame "H1 H2 Hpn". }
    iMod (big_sepL_bupd with "Hl") as "Hl2".
    iDestruct (big_sepL_exist_fun (1%positive, 1%positive, MkPNames 1%positive 1%positive 1%positive 1%positive 1%positive 1%positive 1%positive)
                 (seq 0 n) _ (NoDup_seq 0 n) with "Hl2") as (F) "Hl3".
    iModIntro. iExists (fun j => (F j).2), (fun j => (F j).1.1), (fun j => (F j).1.2).
    iExact "Hl3".
  Qed.

  Local Lemma pls_um_usz (N : uk_names Σ) (sz : Z) (m : nat) :
    ⊢ ushq_um N sz (0 + 2 * m + 1)%nat -∗ usz (ukn_s N) (sz + 65536).
  Proof using .
    rewrite (_ : (0 + 2 * m + 1)%nat = S (2 * m)); [| lia].
    iApply ushq_um_usz.
  Qed.

  (* THE LAW: the main loop's pipe child, at the line predicate
     [PipesCut.pipes_lp] and the widened credential *)
  Definition sh_pipes_child_law : iProp Σ :=
    (□ (UShEcho.sh_echo_slot T -∗ UShCatPay.sh_cat_slot T -∗
        UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
          (pterm_wcN g) pipes_lp (68 + UkSh.ush_Dpipe)))%I.

  Global Instance sh_pipes_child_law_persistent : Persistent sh_pipes_child_law.
  Proof using . rewrite /sh_pipes_child_law. apply bi.intuitionistically_persistent. Qed.

  Lemma pipes_child_law : ⊢ sh_pipes_child_law.
  Proof using Hcons Hkill Heq pipeProtoG0 pnsRegG0 uartGhostG0.
    rewrite /sh_pipes_child_law.
    iIntros "!> #Hes #Hcs".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv s0 len wsf gf sz ld nn I)
      "%Hpeq %Hs1 %Hlp %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcp Hrun".
    destruct Hlp as (ws & n & Hwsf & Hlat).
    pose proof Hlat as (Hok_u & Hlen & Hby).
    pose proof Hok_u as (Hok & Hn & _).
    pose proof (pls_cats_le ws n Hok_u) as Hn16.
    pose proof (pls_lineN I wsf ws n Hlws Hfbk Hwsf Hok_u) as HlN.
    assert (Hpos : (1 <= nlines I)%nat).
    { apply nlines_pos_of_ws. rewrite -Hlws Hwsf. cbn [FileDisc.uline_ws FileDisc.prod_words].
      pose proof (line_ok_pos ws Hok) as Hp. intros Hq.
      apply (f_equal length) in Hq. rewrite length_app in Hq. cbn [length] in Hq. lia. }
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hcst.
    destruct Hrows as (Hfd0c & Hfd1p & Hfd2p).
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen3.
    pose proof (pls_fd_lowest_none ld Hlen3 Hfd0c Hfd1p Hfd2p) as Hnone.
    destruct Hfd0c as [wr0 Hl0]. destruct Hfd1p as [rb1 Hl1]. destruct Hfd2p as [rb2 Hl2].
    destruct n as [| n']; [lia |].
    (* ---- the line is the lexer's ---- *)
    assert (Hbat : bat gf 0 (FileDisc.line_bytes (FileDisc.LPipe (PrEcho ws) (S n')))).
    { intros j Hj. apply Hby. rewrite Hlen. exact Hj. }
    pose proof (ushq_lines_bars ws (replicate (S n') ushq_cat) gf 0%nat len
                  (lines_of_pipe ws (S n') gf len Hok Hn Hbat Hlen)) as Hbars.
    (* ---- THE PARSE ---- *)
    assert (E1 : (68 + UkSh.ush_Dpipe + (8 + (UkShDiag.ush_Dg + nn)))%nat
                 = (68 + (length (RT ws (S n')) * 6 + (96 + nn - 6 * S n')))%nat)
      by (rewrite rtoks_cats_length; unfold UkSh.ush_Dpipe, UkShDiag.ush_Dg; lia).
    iEval (rewrite E1) in "Hrun".
    iApply (wp_kshm_child_pipes_g (SG := uexecSG_xv6) (PS := uprogSG_free) N'
              (ushq_um N' sz) 340
              (ushq_um_chain (SG := uexecSG_xv6) (PS := uprogSG_free) N' (fun k H => H)
                 sz ltac:(lia) Hszal Hszok)
              h m dw dv s0 len gf (wl_toks ws) (RT ws (S n'))
              0%nat (96 + nn - 6 * S n')%nat (pterm_wcN g I 3%nat)
              Hbars ltac:(rewrite rtoks_cats_length; lia) Hs1 Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hstr Hws Hsy HM Hcp [] Hrun").
    { iIntros "!> H". rewrite Hpeq. rewrite /UkShFork.ushf_wq. iLeft. iExact "H". }
    iIntros (h' m' q) "%Ha0' #Hcmd _ _ HM3 Hcp Hrun".
    iPoseProof (pls_um_usz N' sz _ with "HM3") as "Hsz".
    (* ---- THE ROUND'S ALLOCATION ---- *)
    iDestruct (pterm_wcN_3 g I with "Hcp") as "Hcp".
    iDestruct (pls_lend_blkN I with "Hcp") as (v) "(#Hpin & #Hlb & HPW)".
    assert (Hadmit : pns_adm fcE adm_echo I) by (rewrite /pns_adm HlN; reflexivity).
    assert (Hplok : pl_ok (lE I)).
    { rewrite HlN. exact (pl_ok_of_uline_pipe ws (S n') Hok_u). }
    iApply pls_fupd_mwp.
    iMod (pls_nodes_alloc (lcats (lE I))) as (P gF gG) "Hnodes".
    iMod (pipesN_alloc g fcE adm_echo v I Hplok ⊤ pnsN (S gen_id) termw
            (tokN fcE (lE I)) (pdep fcE adm_echo I (wl_line (drop 1 ws)) (PrEcho ws) P gF gG)
            with "HPW") as (γc γm) "[#Hfam Hh]".
    iModIntro.
    (* ---- THE STAGES, at the parser's cut ---- *)
    assert (Hlenst : length (STG ws (S n') len gf s0) = S (lcats (lE I))).
    { rewrite length_map HlN. cbn [length lcats]. by rewrite rtoks_cats_length. }
    assert (Hstc : forall k, (1 <= k <= lcats (lE I))%nat ->
              exists a b, STG ws (S n') len gf s0 !! k
                            = Some (UkShMain.ush_args s0 (pcut ws (S n') len gf) (UkShCat.cat_toks a b))
                          /\ UkShCat.cat_argv_bytes a b (pcut ws (S n') len gf)).
    { rewrite HlN. cbn [lcats]. intros k Hk. destruct k as [| k]; [lia |].
      exists (pc0 ws + 6 * k)%nat, (pc0 ws + 6 * k + 3)%nat. split.
      - rewrite map_lookup_fmap.
        rewrite (_ : (wl_toks ws :: RT ws (S n')) !! S k = RT ws (S n') !! k); [| reflexivity].
        rewrite rtoks_cats_lookup; [reflexivity | lia].
      - exact (pcut_cat_bytes ws (S n') gf len k Hlat ltac:(lia)). }
    pose proof (pcut_echo_bytes ws (S n') gf len Hlat) as Hbytes.
    iPoseProof (ush_cldep_nonpipe (SG := uexecSG_xv6) (PS := uprogSG_free)
                  (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
                  ltac:(intros rb wb gp Hq; discriminate Hq)) as "#Hcd0".
    assert (E2 : (68 + (length (RT ws (S n')) * 6 + (96 + nn - 6 * S n')))%nat
                 = (6 + (2 + (UkShDiag.ush_Dg
                    + (6 * length (REST ws n' len gf s0)
                       + (6 + (32 + (96 + nn - 6 * S n')))))))%nat)
      by (rewrite length_map !rtoks_cats_length; unfold UkShDiag.ush_Dg; lia).
    iEval (rewrite E2) in "Hrun".
    (* THE PRODUCER'S LAW: echo's *)
    iPoseProof (plaw_echo g fcE adm_echo pipes_lm_echo_laws Hcons Hkill rn Heq fc_none_ok
                  v I Hadmit Hplok (wl_line (drop 1 ws))
                  (UkPipesEntries.pe_line_len ws Hok) (PrEcho ws) γc γm P gF gG
                  ltac:(rewrite HlN; reflexivity) eq_refl s0 (pcut ws (S n') len gf)
                  ws eq_refl Hok Hbytes with "Hfam Hes") as "#Hpl".
    iApply (wp_pipes_round_alloc g fcE adm_echo pipes_lm_echo_laws Hcons Hkill rn Heq fc_none_ok
              v I Hadmit Hplok (wl_line (drop 1 ws))
              (UkPipesEntries.pe_line_len ws Hok) (PrEcho ws) γc γm P gF gG
              (UkShFork.ushf_wq (pterm_wcN g) I)
              (era_pin γ (S gen_id) v ∗ (inp_lb v I ∨ T))%I
              (pipes_fin v I (wl_line (drop 1 ws)) (PrEcho ws) P gF gG γc γm Hadmit Hplok Hpos)
              ltac:(rewrite HlN; reflexivity) eq_refl s0 (pcut ws (S n') len gf)
              (STG ws (S n') len gf s0) Hlenst
              (UkShMain.ush_args s0 (pcut ws (S n') len gf) (wl_toks ws)) eq_refl Hstc
              ld rb1 rb2 Hl1 Hl2 Hnone
              (REST ws n' len gf s0)
              (UkShMain.ush_args s0 (pcut ws (S n') len gf) (wl_toks ws))
              (UkShMain.ush_args s0 (pcut ws (S n') len gf)
                 [(pc0 ws, pc0 ws + length ushq_cat)%nat])
              N' h' m' q (sz + 65536) (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
              (32 + (96 + nn - 6 * S n'))%nat
              eq_refl Hpeq Ha0' Hl0 ltac:(discriminate)
              with "Hfam Hpl Hcs Hh Hnodes [] Hpid Hcode Hjt Hcmd Hsz Hstd Hcd0 Hcwd Hch Hrun").
    iFrame "Hpin Hlb".
  Qed.
End UShPipesLaw.
