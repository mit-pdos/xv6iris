(* ===================================================================== *)
(* UShPipesNode.v -- THE PAYING NODE LAW: the right spine's pipeline,    *)
(* every process paid, at ANY number of stages (design claude-notes/     *)
(* design/pipes-general.md SS1.1-SS1.3, SS2.2; cuts C7a and C7b).        *)
(*                                                                        *)
(* [UkShPipesRound.wp_kshr_runcmd_pipes_law_g] is the induction on the    *)
(* stages at an ABSTRACT payment; this file is its PAYING instance:       *)
(*   - [Qc k] is [UShPipesDefs.QcK k], node [k]'s two children's side-     *)
(*     tagged reports;                                                     *)
(*   - the left and last laws are [UShPipesStage]'s three stages;          *)
(*   - the entry law and the top node's bundle are [node_obl_of]: node     *)
(*     [k]'s pipe is registered at its FLOW parameter ([node_registrar]),  *)
(*     its credential splits into the two children's lends, its [pipe]    *)
(*     and [fork] panics are family writers [WSh k] (the pipe panic        *)
(*     silences the never-forked writers below it first; a fork panic is   *)
(*     the TERMINAL round), and after its two waits the node reads its     *)
(*     pipe ([node_read]: the two children's outcomes paired through the   *)
(*     protocol, an exec failure refuted against the content through the  *)
(*     family's deposit), commits its silent writers ([fam_silence]) and   *)
(*     pays its own parent.                                               *)
(* The top node pays the round's [UShPipesDefs.Qtop].                     *)
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
Require Import PipeOut PipeDisc.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN GenOut PipeOutN PipesView.
Require Import PipeNames PipeQueue PipeReg PipeProto.
Require Import AppCfg AppInv.
Require Import ProgTree.
Require Import CtxIdDefs.
Require Import UCodeShK.
Require Import UkSh UkShRun UkShMain UkShDiag.
Require Import UkShEcho UkShCat.
Require Import UkShPipe UkShPipePaid UkShPipesRound.
Require Import UShEcho UShEchoPipePay UShCatPay UShPipeCall.
Require Import UShPipeLeaves.
Require Import UkConsOut.
Require Import UkPipesIface UkPipesEntries.
Require Import PipesFire UShPipesDefs UShPipesStage.
Require ExecWords FileDisc.
Require User.ShSyms.
Local Open Scope Z_scope.

(* a nonempty prefix of a line is not empty *)
Lemma take_pos_ne_at (L : list (bv 8)) (c : nat) : (0 < c <= length L)%nat -> take c L <> [].
Proof using.
  intros Hc Hq. apply (f_equal length) in Hq. rewrite length_take in Hq. cbn [length] in Hq. lia.
Qed.

Section UShPipesNode.
  Context `{HRg : !riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.

  (* THE ROUND *)
  (* THE ROUND'S CLAIM at a line model with a pipeline view (cut C9c') *)
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
  (* THE PRODUCER at the head of the line: echo, or [cat f] *)
  Context (pr : producer).
  (* THE PRODUCER'S LOAN ([UShPipesDefs.lrd]): node 0 holds it from its
     credential, lends it to its left child and gets it back in the left
     report; a committed round hands it to the caller in [Qtop] *)
  Context (Rd : iProp Σ) `{HRd_tl : !Timeless Rd}.
  Context (γc γm : wid -> gname).
  Context (P : nat -> pnames) (gF gG : nat -> gname).

  #[local] Instance nd_T_pers0 : Persistent T | 0 := gcT_pers CP.
  #[local] Instance nd_T_tl0 : Timeless T | 0 := gcT_tl CP.

  Local Notation fcR := (pv_fc PV sR).
  Local Notation nc := (lcats lR).
  Local Notation wsN := (wids nc).
  Local Notation RUNN := (runN fcR lR).
  Local Notation PWN := (pwc_blkV g LM (gcPIN CP) (gcW CP) T v I sR).
  Local Notation WITN := (pwitV LM I sR).
  Local Notation TOKN := (tokN fcR lR).
  Local Notation pdepR := (pdep LM PV sR lR L pr P gF gG).
  Local Notation FAM := (blkN_inv wsN RUNN PWN termw TOKN pdepR pnsN (S gen_id) γc γm).
  Local Notation QcR k := (QcK LM CP v I lR L pr Rd γc γm P k).
  Local Notation QtopR := (Qtop LM CP v I lR Rd γc γm).
  (* the producer's stage law ([UShPipesStage.prod_stage_law]) *)
  Local Notation PLAW a := (prod_stage_law LM CP v I lR L pr Rd γc γm P gG a).
  (* WHAT THE TOP NODE PAYS (cut C8): the round's [Qtop], read into the
     caller's own payload by a conversion that may use the family *)
  Context (Qfin Rtop : iProp Σ).
  Context (Hfin : (Rtop ∗ FAM ∗ QtopR ⊢ Qfin)%I).
  Local Notation wdoneR w := (wdone γc γm w).
  Local Notation wfinR w := (wfin γc γm w).
  Local Notation lrepR k := (lrep L pr γc γm P k).
  Local Notation rrepR j := (rrep LM CP v I lR L γc γm P j).
  Local Notation sufR j ro := (suf LM CP v I lR L γc γm j ro).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  (* THE ROUND'S PURE PREMISE ON THE MODEL: every commit its processes make
     is admitted, or refuted by a deposit ([UShPipesStage.Hfire]).  A silent
     commit is always admitted ([PipeOutN.silence_okN_tok]). *)
  (* THE LINE the model reads: the producer, then [cat] [nc] times; the
     content that flows is the producer's *)
  Hypothesis Hline : lR = LPipes pr nc.
  Hypothesis HLw : L = prod_content fcR pr.

  (* the line has a cat: the model's line is well formed *)
  Lemma nc_pos : (1 <= nc)%nat.
  Proof using Hline Hplok.
    pose proof Hplok as Hok. rewrite Hline in Hok. rewrite Hline. exact (proj1 (proj2 Hok)).
  Qed.

  Lemma Hfire : forall w s, w ∈ wsN -> fire_src fcR pr L w s ->
    fire_okN wsN RUNN WITN termw TOKN w s (EXf fcR pr nc L w s).
  Proof using HLw Hadmit HlR Hline Hplok.
    intros w s. rewrite HLw. exact (pipes_fire_ok LM PV I sR lR HlR Hadmit pr nc nc_pos Hline w s).
  Qed.

  #[local] Instance rd_final_pers0 pn ro : Persistent (rd_final pn ro).
  Proof using . destruct ro; apply _. Qed.

  (* ================================================================= *)
  (*  1.  THE WRITERS AT THEIR END                                       *)
  (* ================================================================= *)

  Lemma termw_nil (w : wid) : termw w [] = false.
  Proof using . destruct w; reflexivity. Qed.

  (* a final writer, committed: silent if it never fired *)
  Lemma wfin_done (E : coPset) (w : wid) :
    ↑pnsN ⊆ E -> w ∈ wsN -> FAM -∗ wfinR w ={E}=∗ wdoneR w.
  Proof using Hadmit Hcons Hext HlR Hfc Hplok.
    intros HE Hw. iIntros "#Hinv Hf". iDestruct "Hf" as (o) "[Ho %Ht]".
    destruct o as [s |].
    - iModIntro. iExists s. iFrame "Ho". iPureIntro. exact (Ht s eq_refl).
    - cbn [pns_wfin]. iDestruct "Ho" as "[Hc Hm]".
      iMod (fam_silence g LM PV CP sd WA Hcons v I sR lR HlR Hfc Hadmit Hplok L pr γc γm P gF gG E w HE Hw
              (silence_okV_tok LM PV sR lR w (fun _ _ => False)) with "Hinv Hc Hm") as "[Hc Hm]".
      iModIntro. iExists []. cbn [pns_wfin length]. iFrame "Hc Hm".
      iPureIntro. exact (termw_nil w).
  Qed.

  Lemma halves_wfin (w : wid) :
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ wfinR w.
  Proof using .
    iIntros "Hc Hm". iExists None. cbn [pns_wfin]. iFrame "Hc Hm".
    iPureIntro. intros s Hs. discriminate Hs.
  Qed.

  Lemma wsub_cons (k : nat) :
    (k < nc)%nat -> wsub lR k = WSh k :: WLeft k :: wsub lR (S k).
  Proof using P gF gG.
    intros Hk. rewrite /wsub. replace (nc - k)%nat with (S (nc - S k)) by lia.
    reflexivity.
  Qed.

  Lemma wlast_pos (oc : option nat) :
    wlast L γc γm oc -∗ wlast L γc γm oc
      ∗ ⌜forall c, oc = Some c -> (0 < c <= length L)%nat⌝.
  Proof using .
    destruct oc as [c |]; [| iIntros "$"; iPureIntro; intros c Hc; discriminate Hc].
    iIntros "(Hc & Hm & %Hc0)". iFrame "Hc Hm". iSplit; [done |].
    iPureIntro. intros c' Hc'. injection Hc' as <-. exact Hc0.
  Qed.

  Local Notation take_pos_ne c := (take_pos_ne_at L c).

  (* the suffix's writers, the content writer committed *)
  Lemma wst_all (k m : nat) :
    ([∗ list] w ∈ wids_from k m, wst γc γm w) -∗ wdoneR WLast -∗
    [∗ list] w ∈ wids_from k m, wdoneR w.
  Proof using .
    revert k. induction m as [| m IH]; intros k; cbn [wids_from].
    - iIntros "_ Hl". rewrite big_sepL_singleton. iExact "Hl".
    - iIntros "(Hs & Hl & Hr) HL". iFrame "Hs Hl".
      iApply (IH (S k) with "Hr HL").
  Qed.

  (* ================================================================= *)
  (*  2.  THE NODE'S READING (design SS1.1's node step, item 4)          *)
  (* ================================================================= *)

  (* the chain one node up: whatever the suffix's content writer is at,
     the suffix read it through the node's pipe, which the left stage wrote
     whole -- so the left stage read it too *)
  Lemma chain_up (wo : wr_out) (ro' ro : rd_out) (oc : option nat) :
    pipe_pair wo ro' -> chain L ro' oc -> (forall c, oc = Some c -> (0 < c <= length L)%nat) ->
    copier ro wo -> chain L ro oc.
  Proof using .
    intros Hpair Hch Hpos Hcop c Hc. pose proof (Hch c Hc) as Hro'. subst ro'.
    pose proof (Hpos c Hc) as Hc0.
    destruct wo as [D | D |]; cbn [pipe_pair] in Hpair.
    - apply Hcop. by rewrite Hpair.
    - done.
    - exfalso. exact (take_pos_ne c Hc0 Hpair).
  Qed.

  (* NODE [k]'s READING: after its two waits, its own writer silent, the
     left stage's report and the suffix's are one report of the suffix
     from stage [k] *)
  Lemma node_read (k : nat) (γp : pipe_names) :
    (k < nc)%nat ->
    FAM -∗ pipe_invU (P k) γp L (flow_U L (prevP P k)) -∗
    wcurN γc (WSh k) (1/2) 0 -∗ wmodeN γm (WSh k) (1/2) None -∗
    lrepR k -∗ rrepR (S k) ={⊤}=∗
    ∃ ro, (match k with O => ⌜ro = RdEof L \/ ro = RdGone⌝ | S k' => rd_final (P k') ro end)
          ∗ sufR k ro.
  Proof using Hadmit Hcons Hext HlR Hfc HL31 Hline HLw Hplok.
    intros Hk. iIntros "#Hfam #Hinv Hc Hm Hl Hr".
    assert (HwS : WSh k ∈ wsN) by (apply wids_elem; exact Hk).
    assert (HwL : WLeft k ∈ wsN) by (apply wids_elem; exact Hk).
    (* ---- node k's own writer: it did not panic, it commits silence ---- *)
    iMod (fam_silence g LM PV CP sd WA Hcons v I sR lR HlR Hfc Hadmit Hplok L pr γc γm P gF gG ⊤ (WSh k)
            ltac:(done) HwS (silence_okV_tok LM PV sR lR (WSh k) (fun _ _ => False)) with "Hfam Hc Hm") as "[Hc Hm]".
    iAssert (wdoneR (WSh k)) with "[Hc Hm]" as "Hsh".
    { iExists []. cbn [pns_wfin length]. iFrame "Hc Hm". iPureIntro. reflexivity. }
    iDestruct "Hr" as (ro') "[#Hrd Hsuf]".
    assert (Hsk : (S k - 1)%nat = k) by lia. iEval (rewrite Hsk) in "Hrd".
    iDestruct "Hl" as (o) "[Ho Hl]".
    iDestruct "Hsuf" as "[Hn | Ht]".
    - (* ---- THE SUFFIX RAN TO ITS END ---- *)
      iDestruct "Hn" as (oc) "(%Hch & Hwl & Hws)".
      iDestruct (wlast_pos with "Hwl") as "[Hwl %Hpos]".
      iDestruct "Hl" as "[%Hex | Hl]".
      + (* THE LEFT STAGE FAILED (its exec, or the [cat f] producer's open):
           nothing reached the pipe, so the suffix read nothing -- the
           family's deposit of the failed stage against the pipe's frozen
           contents *)
        destruct Hex as (s & -> & Hfl).
        iAssert (|={⊤}=> ⌜oc = None⌝ ∗ pns_wfin γc γm (WLeft k) (Some s))%I
          with "[Ho]" as ">[%Hoc Ho]".
        { destruct oc as [c |]; [| iModIntro; by iFrame "Ho"].
          pose proof (Hch c eq_refl) as Hro. subst ro'. cbn [rd_final].
          pose proof (Hpos c eq_refl) as Hc0.
          cbn [pns_wfin]. iDestruct "Ho" as "[Hcw Hmw]".
          iMod (fam_peek g LM PV CP v I sR lR L pr γc γm P gF gG ⊤ (WLeft k) s
                  (length s) False%I ltac:(done) HwL
                  ltac:(pose proof (fail_src_ne pr k s Hfl) as Hne; destruct s; [done | cbn; lia])
                  with "Hfam Hcw Hmw [Hrd]") as "(_ & _ & [])".
          iIntros "Hd".
          rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WLeft k) s (fail_src_ne pr k s Hfl)
                     (or_introl Hfl)) /pdep_ne.
          rewrite bool_decide_true; [| exact Hfl]. iDestruct "Hd" as "(_ & _ & Hw)".
          iInv "Hinv" as ">Hb" "Hclose".
          iDestruct (pipe_body_execLU with "Hb Hw Hrd") as %Hnil.
          exfalso. exact (take_pos_ne c Hc0 Hnil). }
        subst oc.
        iMod (wfin_done ⊤ (WLeft k) ltac:(done) HwL with "Hfam [Ho]") as "Hld".
        { iExists (Some s). iFrame "Ho". iPureIntro. intros s' _. reflexivity. }
        iModIntro. iExists RdGone.
        iSplitR; [destruct k; [iPureIntro; by right | done] |].
        iLeft. iExists None.
        iSplitR; [iPureIntro; intros c Hc; discriminate Hc |]. iFrame "Hwl".
        rewrite (wsub_cons k Hk) !big_sepL_cons. iFrame "Hsh Hld Hws".
      + (* THE LEFT STAGE RAN: its write outcome and the suffix's read
           outcome pair through the protocol ([node_body_readingU]) *)
        iDestruct "Hl" as (wo) "[Hwo Hup]".
        iInv "Hinv" as ">Hb" "Hclose".
        iDestruct (node_body_readingU with "Hb Hwo Hrd") as %(Hpair & _ & _).
        iMod ("Hclose" with "[Hb]") as "_"; [iNext; iExact "Hb" |].
        iMod (wfin_done ⊤ (WLeft k) ltac:(done) HwL with "Hfam [Ho]") as "Hld".
        { iExists o. iFrame "Ho". iPureIntro. intros s _. reflexivity. }
        destruct k as [| k'].
        * (* the producer: its [WrAll] is the whole line *)
          iDestruct "Hup" as %Hall.
          set (roup := match wo with WrAll _ => RdEof L | _ => RdGone end).
          assert (Hch' : chain L roup oc).
          { apply (chain_up wo ro' roup oc Hpair Hch Hpos).
            intros D HD. rewrite /roup HD. rewrite (Hall D HD). reflexivity. }
          iModIntro. iExists roup.
          iSplitR; [iPureIntro; rewrite /roup; destruct wo; [left | right | right]; done |].
          iLeft. iExists oc. iSplitR; [iPureIntro; exact Hch' |]. iFrame "Hwl".
          rewrite (wsub_cons 0 Hk) !big_sepL_cons. iFrame "Hsh Hld Hws".
        * (* a middle cat: what it wrote whole, it read *)
          iDestruct "Hup" as (rok) "[#Hrk %Hcop]".
          assert (Hch' : chain L rok oc) by exact (chain_up wo ro' rok oc Hpair Hch Hpos Hcop).
          iModIntro. iExists rok. iFrame "Hrk".
          iLeft. iExists oc. iSplitR; [iPureIntro; exact Hch' |]. iFrame "Hwl".
          rewrite (wsub_cons (S k') Hk) !big_sepL_cons. iFrame "Hsh Hld Hws".
    - (* ---- THE SUFFIX IS TERMINAL: this stage was waited ---- *)
      iDestruct "Ht" as (i) "(%Hi & Hter & Hwt)".
      iMod (wfin_done ⊤ (WLeft k) ltac:(done) HwL with "Hfam [Ho]") as "Hld".
      { iExists o. iFrame "Ho". iPureIntro. intros s _. reflexivity. }
      iModIntro. iExists RdGone.
      iSplitR; [destruct k; [iPureIntro; by right | done] |].
      iRight. iExists i. iSplitR; [iPureIntro; lia |]. iFrame "Hter".
      replace (i - k)%nat with (S (i - S k)) by lia.
      rewrite (_ : seq k (S (i - S k)) = k :: seq (S k) (i - S k)); [| reflexivity].
      rewrite big_sepL_cons. iFrame "Hld Hwt".
  Qed.

  (* THE TOP NODE'S END: the whole line read, the content writer at its
     end (the chain meets the producer's whole line), every writer
     committed *)
  Lemma top_finish (ro : rd_out) :
    FAM -∗ ⌜ro = RdEof L \/ ro = RdGone⌝ -∗ sufR 0 ro -∗ Rd ={⊤}=∗ QtopR.
  Proof using Hadmit Hcons Hext HlR Hfc Hplok.
    iIntros "#Hfam %Hro [Hn | Ht] HRd".
    - iDestruct "Hn" as (oc) "(%Hch & Hwl & Hws)".
      assert (Hwl : WLast ∈ wsN) by (apply wids_elem; done).
      iAssert (|={⊤}=> wdoneR WLast)%I with "[Hwl]" as ">HL".
      { destruct oc as [c |].
        - iDestruct "Hwl" as "(Hc & Hm & %Hc0)".
          pose proof (Hch c eq_refl) as Hro'.
          iMod (fam_cur_le g LM PV CP v I sR lR L pr γc γm P gF gG ⊤ WLast L c ltac:(done) Hwl
                  with "Hfam Hc Hm") as "(%Hle & Hc & Hm)".
          assert (Htk : take c L = L).
          { destruct Hro as [-> | ->]; [by injection Hro' | discriminate Hro']. }
          assert (Hcl : c = length L).
          { pose proof (f_equal length Htk) as Hlen. rewrite length_take in Hlen. lia. }
          iModIntro. iExists L. cbn [pns_wfin]. rewrite -Hcl. iFrame "Hc Hm".
          iPureIntro. reflexivity.
        - iApply (wfin_done ⊤ WLast ltac:(done) Hwl with "Hfam Hwl"). }
      iModIntro. iRight. iLeft. iFrame "HRd". rewrite /wsub Nat.sub_0_r.
      iApply (wst_all 0 nc with "Hws HL").
    - iDestruct "Ht" as (i) "(%Hi & Hter & Hw)".
      iModIntro. iRight. iRight. iExists i. rewrite Nat.sub_0_r. iFrame "Hter Hw".
      iPureIntro. lia.
  Qed.

  (* ================================================================= *)
  (*  3.  THE NODE'S RESOURCES                                          *)
  (* ================================================================= *)

  (* a pipe named before the walk: the body's own half, both permits and
     both side tokens *)
  Definition pbundle (pn : pnames) : iProp Σ :=
    (pipe_pre pn ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn)%I.
  Definition halvesN (w : wid) : iProp Σ :=
    (wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None)%I.
  (* what sh node [j] will own: its two writers, its two forks' pending
     shots, its pipe *)
  Definition nodeown (j : nat) : iProp Σ :=
    (halvesN (WSh j) ∗ halvesN (WLeft j) ∗ osP (gF j) ∗ osP (gG j) ∗ pbundle (P j))%I.
  (* ...everything strictly below node [k] *)
  Definition below (k : nat) : iProp Σ :=
    (([∗ list] j ∈ seq (S k) (nc - S k), nodeown j) ∗ halvesN WLast)%I.
  (* what node [k] knows: the shots of the right forks above it and the
     pipes above it *)
  Definition nknow (k : nat) : iProp Σ :=
    (shotsF gF k ∗ [∗ list] i ∈ seq 0 k, pinv L P i)%I.

  Global Instance nknow_persistent k : Persistent (nknow k).
  Proof using . rewrite /nknow. apply _. Qed.

  (* the read end a node's fd 0 is, below the top *)
  Definition gin_of (st : fdstate) : option pipe_names :=
    match st with FdOpen true _ (FdPipe gin) => Some gin | _ => None end.

  Lemma gin_of_some (st : fdstate) (gin : pipe_names) :
    gin_of st = Some gin -> exists wb, st = FdOpen true wb (FdPipe gin).
  Proof using .
    destruct st as [| [|] wb [? ? ? | gp | ?]]; cbn; try discriminate.
    intros Hq. injection Hq as <-. by exists wb.
  Qed.

  (* NODE [k]'s INPUT: nothing at the top; below it, the pipe above at the
     kernel names of its fd 0, its read permit and right side token *)
  Definition ninp (k : nat) (st0 : fdstate) : iProp Σ :=
    match k with
    | O => Rtop ∗ Rd
    | S k' =>
        match gin_of st0 with
        | Some gin =>
            pipe_invU (P k') gin L (flow_U L (prevP P k')) ∗ rcur (P k') 0 ∗ side_R (P k')
        | None => False
        end
    end%I.

  (* NODE [k]'s CREDENTIAL, what its split parts *)
  Definition ncred (k : nat) (st0 : fdstate) : iProp Σ :=
    (halvesN (WSh k) ∗ halvesN (WLeft k) ∗ osP (gF k) ∗ osP (gG k) ∗ below k
     ∗ nknow k ∗ ninp k st0)%I.

  (* THE TOP NODE'S CREDENTIAL, out of the round's allocation: the family's
     halves at every writer, two one-shot names and a pipe per node *)
  Lemma below_of_halves (k m : nat) :
    ([∗ list] w ∈ wids_from k m, halvesN w) -∗
    ([∗ list] j ∈ seq k m, osP (gF j) ∗ osP (gG j) ∗ pbundle (P j)) -∗
    ([∗ list] j ∈ seq k m, nodeown j) ∗ halvesN WLast.
  Proof using .
    revert k. induction m as [| m IH]; intros k; cbn [wids_from seq].
    - iIntros "H _". rewrite big_sepL_singleton big_sepL_nil. iFrame "H".
    - rewrite !big_sepL_cons.
      iIntros "(HS & HL & Hw) [(HF & HG & Hp) Hr]".
      iDestruct (IH (S k) with "Hw Hr") as "[Hn HW]".
      iFrame "HS HL HF HG Hp Hn HW".
  Qed.

  Lemma ncred0_of (st0 : fdstate) :
    (1 <= nc)%nat ->
    ([∗ list] w ∈ wsN, halvesN w) -∗
    ([∗ list] j ∈ seq 0 nc, osP (gF j) ∗ osP (gG j) ∗ pbundle (P j)) -∗
    Rtop -∗ Rd -∗ ncred 0 st0 ∗ pbundle (P 0).
  Proof using GEN.
    intros Hn. iIntros "Hh Ho HR HRd".
    rewrite /ncred /below /nknow /shotsF /wids. cbn [ninp].
    assert (Hnc : lcats lR = S (lcats lR - 1)) by lia.
    rewrite Hnc. generalize (lcats lR - 1)%nat. intros m.
    rewrite (_ : (S m - 1)%nat = m); [| lia].
    cbn [wids_from seq]. rewrite !big_sepL_cons.
    iDestruct "Hh" as "(HS & HL & Hh)". iDestruct "Ho" as "[(HF & HG & Hp) Ho]".
    iDestruct (below_of_halves 1 m with "Hh Ho") as "[Hb HW]".
    iFrame "HS HL HF HG Hp Hb HW HR HRd". all: try rewrite !big_sepL_nil. all: try done.
  Qed.

  (* WHAT ITS pipe(2) ANSWERS: the pipe at its flow parameter, both
     permits, both side tokens *)
  Definition Rreg (k : nat) (γp : pipe_names) : iProp Σ :=
    (pipe_invU (P k) γp L (flow_U L (prevP P k)) ∗ rtok (P k) ∗ side_L (P k) ∗ side_R (P k)
     ∗ wcur (P k) 0 ∗ pws_lb (P k) [])%I.

  (* node [k+1]'s entry, as node [k]'s right lend *)
  Definition nraw (k : nat) (γp : pipe_names) : iProp Σ :=
    (pipe_invU (P k) γp L (flow_U L (prevP P k)) ∗ nknow k ∗ osP (gF k)
     ∗ rcur (P k) 0 ∗ side_R (P k) ∗ nodeown (S k) ∗ below (S k))%I.

  (* THE LAW'S THREE FAMILIES *)
  Definition Qcf (k : nat) (st : fdstate) (z : Z) : iProp Σ := QcR k.
  Definition RcLf (k : nat) (st0 : fdstate) (γp : pipe_names) : iProp Σ :=
    match k with
    | O => echo_raw L γc γm P gG γp ∗ Rd
    | S k' =>
        match gin_of st0 with
        | Some gin => mid_raw L γc γm P gF gG k' gin γp
        | None => False
        end
    end%I.
  Definition RcRf (k : nat) (st0 : fdstate) (γp : pipe_names) : iProp Σ :=
    if decide (S k = nc) then last_raw lR L γc γm P gF k γp else nraw k γp.
  Definition Rkf (k : nat) (γp : pipe_names) : iProp Σ :=
    pipe_invU (P k) γp L (flow_U L (prevP P k)).
  Definition Cxf (k : nat) (γp : pipe_names) : iProp Σ :=
    (halvesN (WSh k) ∗ match k with O => Rtop | S k' => side_R (P k') end)%I.

  (* WHAT NODE [k] ITSELF PAYS: the round's at the top, its parent's right
     child's below *)
  Definition npay (k : nat) : iProp Σ :=
    match k with O => Qfin | S k' => QcR k' end.

  (* ================================================================= *)
  (*  4.  THE REGISTRAR, AT THE FLOW PARAMETER                           *)
  (* ================================================================= *)

  (* [UShPipeAssembly.pipe_inv_alloc_at] at any flow parameter: the pipe
     is born empty, so its flow clause holds by its left arm *)
  Lemma pipe_inv_alloc_atU (pn : pnames) (gp : pipe_names) (U : iProp Σ) `{!Timeless U} :
    pipe_pre pn -∗ pipe_qfrag (pn_queue gp) pst0 ={⊤}=∗ pipe_invU pn gp L U ∗ pipe_reg gp.
  Proof using GEN P gF gG.
    iIntros "(Hh & Hw & Hr & He & Ho) Hfrag".
    iMod (inv_alloc pipeN ⊤ (pipe_bodyU pn gp L U) with "[Hfrag Hh Hw Hr He Ho]") as "#Hinv".
    { iNext. iExists pst0. rewrite /pst0 /=. iFrame "Hfrag Hh Hw Hr".
      iSplitR; [iPureIntro; apply prefix_nil |].
      iSplitR; [iPureIntro; cbn; lia |].
      iSplitL "He"; [by iLeft |].
      iSplitL "Ho"; [by iLeft | by iLeft]. }
    iModIntro. rewrite /pipe_invU. iFrame "Hinv".
    iApply (pipe_reg_of_invU pn gp L U with "Hinv").
  Qed.

  Lemma node_registrar (k : nat) :
    pbundle (P k) -∗
    ∀ γp, pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ Rreg k γp.
  Proof using GEN gF gG.
    iIntros "(Hpre & Hw & Hr & HsL & HsR)" (γp) "Hfrag".
    iMod (pipe_inv_alloc_atU (P k) γp (flow_U L (prevP P k)) with "Hpre Hfrag")
      as "[#Hinv Hreg]".
    iMod (pws_lb_of_invU (P k) γp L (flow_U L (prevP P k)) 0 with "Hinv Hw") as "[Hw #Hlb]".
    iModIntro. iFrame "Hreg Hinv Hr HsL HsR Hw". rewrite take_0. iExact "Hlb".
  Qed.

  (* ================================================================= *)
  (*  5.  THE SPLIT                                                     *)
  (* ================================================================= *)

  Lemma below_cons (k : nat) :
    (S k < nc)%nat -> below k ⊣⊢ nodeown (S k) ∗ below (S k).
  Proof using .
    intros Hk. rewrite /below.
    replace (nc - S k)%nat with (S (nc - S (S k))) by lia.
    rewrite (_ : seq (S k) (S (nc - S (S k))) = S k :: seq (S (S k)) (nc - S (S k)));
      [| reflexivity].
    rewrite big_sepL_cons. iSplit; [iIntros "[[$ $] $]" | iIntros "($ & $ & $)"].
  Qed.

  Lemma below_last (k : nat) : S k = nc -> below k ⊣⊢ halvesN WLast.
  Proof using .
    intros Hk. rewrite /below. replace (nc - S k)%nat with 0%nat by lia. cbn.
    iSplit; [iIntros "[_ $]" | iIntros "$"].
  Qed.

  Lemma node_split (k : nat) (st0 : fdstate) (γp : pipe_names) :
    (k < nc)%nat ->
    ncred k st0 -∗ Rreg k γp -∗
    RcLf k st0 γp ∗ (RcRf k st0 γp ∗ (Rkf k γp ∗ Cxf k γp)).
  Proof using GEN.
    intros Hk.
    iIntros "(HSh & [HLc HLm] & HF & HG & Hbel & #Hkn & Hinp)
             (#Hinv & Hr & HsL & HsR & Hw & #Hlb)".
    iDestruct "Hkn" as "[#Hsk #Hinvs]".
    (* ---- the parent keeps the pipe's invariant; the tails the node's own
       writer and its input's side token ---- *)
    iAssert (Rkf k γp) as "#HRk"; [iExact "Hinv" |].
    destruct k as [| k'].
    - (* THE TOP: the producer on the left, with the loan *)
      iDestruct "Hinp" as "[Hinp HRd]".
      iSplitL "Hw HsL HLc HLm HG HRd".
      { rewrite /RcLf /echo_raw /pipe_inv. iFrame "Hw HsL HLc HLm HG Hlb HRd".
        iExact "Hinv". }
      iSplitL "HF Hr HsR Hbel"; [| iFrame "HRk"; rewrite /Cxf; iFrame "HSh Hinp"].
      rewrite /RcRf. case_decide as Hlast.
      + rewrite (below_last 0 Hlast). iDestruct "Hbel" as "[Hc Hm]". rewrite /last_raw.
        iFrame "Hinv HF Hr HsR Hc Hm". iSplitR; [| rewrite /shotsF; done].
        rewrite -Hlast. rewrite (_ : seq 0 1 = [0%nat]); [| reflexivity].
        rewrite big_sepL_singleton. iExists γp. iExact "Hinv".
      + rewrite /nraw (below_cons 0 ltac:(lia)).
        iFrame "Hinv HF Hr HsR Hbel". rewrite /nknow. iFrame "Hsk Hinvs".
    - (* BELOW THE TOP: a middle cat on the left, reading the pipe above *)
      rewrite /ninp. destruct (gin_of st0) as [gin |] eqn:Hg; [| iDestruct "Hinp" as %[]].
      iDestruct "Hinp" as "(#Hpin & Hrin & HsRin)".
      iSplitL "Hw HsL HLc HLm HG Hrin".
      { rewrite /RcLf Hg /mid_raw. iFrame "Hw HsL HLc HLm HG Hrin Hlb Hsk".
        iSplitR; [iExists (prevP P k'); iExact "Hpin" |]. iExact "Hinv". }
      iSplitL "HF Hr HsR Hbel"; [| iFrame "HRk"; rewrite /Cxf; iFrame "HSh HsRin"].
      rewrite /RcRf. case_decide as Hlast.
      + rewrite (below_last (S k') Hlast). iDestruct "Hbel" as "[Hc Hm]". rewrite /last_raw.
        iFrame "Hinv HF Hr HsR Hc Hm Hsk". rewrite -Hlast.
        rewrite (seq_S (S k')) big_sepL_app big_sepL_singleton /=. iFrame "Hinvs".
        iExists γp. iExact "Hinv".
      + rewrite /nraw (below_cons (S k') ltac:(lia)).
        iFrame "Hinv HF Hr HsR Hbel". rewrite /nknow. iFrame "Hsk Hinvs".
  Qed.

  (* ================================================================= *)
  (*  6.  THE NODE'S TAILS                                              *)
  (* ================================================================= *)

  Local Lemma nd_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  #[local] Instance nd_exf_pers0 (dg : list (bv 8)) (n : nat) (Cr Cd : iProp Σ) :
    Persistent (UkShDiag.ush_execfail_law_at (SG := uexecSG_xv6) (PS := uprogSG_free)
                  dg n Cr Cd) | 0
    := UkShDiag.ush_execfail_law_at_persistent (SG := uexecSG_xv6) (PS := uprogSG_free)
         dg n Cr Cd.

  Lemma wdone_wfin (w : wid) : wdoneR w -∗ wfinR w.
  Proof using .
    iIntros "(%s & Hs & %Ht)". iExists (Some s). iFrame "Hs". iPureIntro.
    intros s' Hs'. injection Hs' as <-. exact Ht.
  Qed.

  Lemma alt_forkc_panic : alt_forkc = alt_panic ++ u_prompt.
  Proof using . reflexivity. Qed.

  Lemma termw_pipe (k : nat) : termw (WSh k) dg_pipe_b = false.
  Proof using . cbn [termw]. apply bool_decide_eq_false_2. exact dg_pipe_ne_fork. Qed.

  Lemma wids_top : (0 < nc)%nat -> wids nc = WSh 0 :: WLeft 0 :: wsub lR 1.
  Proof using P gF gG.
    intros Hn. rewrite -(wsub_cons 0 Hn). rewrite /wsub Nat.sub_0_r. reflexivity.
  Qed.

  (* the never-forked writers below a node, committed silent *)
  Lemma nodes_silence (j m : nat) :
    (j + m <= nc)%nat ->
    FAM -∗ ([∗ list] i ∈ seq j m, nodeown i) ={⊤}=∗ [∗ list] w ∈ wids_from j m, wst γc γm w.
  Proof using Hadmit Hcons Hext HlR Hfc Hplok.
    revert j. induction m as [| m IH]; intros j Hjm; iIntros "#Hfam Hn".
    - iModIntro. cbn. iSplit; done.
    - cbn [seq wids_from]. rewrite big_sepL_cons.
      iDestruct "Hn" as "(([Hsc Hsm] & [Hlc Hlm] & _) & Hn)".
      assert (HwS : WSh j ∈ wsN) by (apply wids_elem; lia).
      assert (HwL : WLeft j ∈ wsN) by (apply wids_elem; lia).
      iMod (wfin_done ⊤ (WSh j) ltac:(done) HwS with "Hfam [Hsc Hsm]") as "Hsd";
        [iApply (halves_wfin with "Hsc Hsm") |].
      iMod (wfin_done ⊤ (WLeft j) ltac:(done) HwL with "Hfam [Hlc Hlm]") as "Hld";
        [iApply (halves_wfin with "Hlc Hlm") |].
      iMod (IH (S j) ltac:(lia) with "Hfam Hn") as "Hr".
      iModIntro. iFrame "Hsd Hld Hr".
  Qed.

  Lemma below_silence (k : nat) :
    (k < nc)%nat ->
    FAM -∗ below k ={⊤}=∗ ([∗ list] w ∈ wsub lR (S k), wst γc γm w) ∗ wdoneR WLast.
  Proof using Hadmit Hcons Hext HlR Hfc Hplok.
    intros Hk. iIntros "#Hfam [Hn [Hc Hm]]".
    assert (HwL : WLast ∈ wsN) by (apply wids_elem; done).
    iMod (nodes_silence (S k) (nc - S k) ltac:(lia) with "Hfam Hn") as "Hws".
    iMod (wfin_done ⊤ WLast ltac:(done) HwL with "Hfam [Hc Hm]") as "HL";
      [iApply (halves_wfin with "Hc Hm") |].
    iModIntro. iFrame "Hws HL".
  Qed.

  (* THE [pipe(2)]-FAILED TAIL: the writers below are never forked, so the
     node commits them silent; then [pipe] goes out as its own writer; the
     payment is the round's (at the top) or its parent's (the suffix read
     nothing and every writer of it is committed) *)
  Lemma node_pipe_panic (k : nat) (st0 : fdstate) (N : uk_names Σ) `{!ukn_const N}
      (ld : list fdstate) (h' : CpuId) (m' : regfile) (av : nat) :
    (k < nc)%nat -> ukn_pay N = (fun _ : Z => npay k) -> UkSh.ush_fd2p ld ->
    uint (m' !!! Regidx a0_idx) = 0x12c8 ->
    FAM -∗ shk_code (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
    UserFd.ustd (ukn_fd N) ld -∗ ncred k st0 -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h' m' (mword_of_int ShSyms.panic)
      (UkShDiag.ush_Dg + (2 + av)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hfin Hadmit Hcons Hext HlR Hfc Hline HLw Hplok.
    intros Hk Hpeq Hfd2 Ha0.
    iIntros "#Hfam #Hcode #Hjt Hstd (HSh & [HLc HLm] & HF & HG & Hbel & #Hkn & Hinp) Hrun".
    iDestruct "Hkn" as "[#Hsk _]".
    iDestruct (UkSh.ush_jtab_ro with "Hjt") as "#Hro".
    assert (HwS : WSh k ∈ wsN) by (apply wids_elem; exact Hk).
    assert (HwL : WLeft k ∈ wsN) by (apply wids_elem; exact Hk).
    iApply nd_fupd_mwp.
    iMod (wfin_done ⊤ (WLeft k) ltac:(done) HwL with "Hfam [HLc HLm]") as "Hld";
      [iApply (halves_wfin with "HLc HLm") |].
    iMod (below_silence k Hk with "Hfam Hbel") as "[Hws HL]".
    iModIntro.
    iDestruct "HSh" as "[Hc Hm]".
    iApply (wp_kshd_panic_paid_at (SG := uexecSG_xv6) (PS := uprogSG_free) N 0x12c8 dg_pipe_b
              (wcurN γc (WSh k) (1/2) 0 ∗ wmodeN γm (WSh k) (1/2) None ∗ osP (gF k) ∗ osP (gG k))%I
              (wcurN γc (WSh k) (1/2) 5 ∗ wmodeN γm (WSh k) (1/2) (Some dg_pipe_b))%I
              ld h' m' (2 + av)%nat Hfd2 Ha0 ltac:(discriminate) ushq_pipe_msg_fmt
              ushq_pipe_msg_len ushq_pipe_msg_byte ushq_pipe_msg_nl
              with "[] Hcode Hro Hstd [Hc Hm HF HG] [Hld Hws HL Hinp] Hrun").
    - iApply (exf_writer g LM PV CP sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok L pr γc γm P gF gG
                (WSh k) dg_pipe_b dg_pipe_b 5%nat (EXf fcR pr nc L (WSh k) dg_pipe_b) _ emp%I _
                HwS ltac:(lia) (fun p b _ Hb => Hb)
                (Hfire (WSh k) dg_pipe_b HwS (or_introl eq_refl))
                ltac:(intros c Hc; apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WSh k) dg_pipe_b c);
                      [lia | rewrite dg_pipe_b_len; lia |
                       intros j Hj Hs; exfalso; exact (dg_pipe_ne_fork Hs)])
                with "Hfam [] [] []").
      + iApply (pexcl_sh LM PV sR lR L pr P gF gG k dg_pipe_b Hk (or_introl eq_refl)).
      + iIntros "!> (Hc & Hm & HF & HG)". iFrame "Hc Hm".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WSh k) dg_pipe_b
                   (panic_src_ne dg_pipe_b (or_introl eq_refl)) (or_introl eq_refl)) /pdep_ne.
        rewrite bool_decide_true; [| done]. iFrame "Hsk HF HG".
      + iIntros "!> _ Hc Hm _". iFrame "Hc Hm".
    - iFrame "Hc Hm HF HG".
    - iIntros "_ [Hc Hm]". rewrite Hpeq.
      iAssert (wdoneR (WSh k)) with "[Hc Hm]" as "Hsd".
      { iExists dg_pipe_b. cbn [pns_wfin]. rewrite dg_pipe_b_len. iFrame "Hc Hm".
        iPureIntro. exact (termw_pipe k). }
      destruct k as [| k'].
      + (* THE TOP: every writer committed, the loan never lent *)
        cbn [npay]. iApply Hfin. iDestruct "Hinp" as "[Hinp HRd]". iFrame "Hfam Hinp".
        iRight. iLeft. iFrame "HRd". rewrite (wids_top Hk) !big_sepL_cons.
        iFrame "Hsd Hld". iApply (wst_all 1 (nc - 1) with "Hws HL").
      + (* BELOW: the suffix read nothing *)
        cbn [npay]. rewrite /ninp. destruct (gin_of st0) as [gin |]; [| iDestruct "Hinp" as %[]].
        iDestruct "Hinp" as "(_ & _ & HsR)".
        iRight. iRight. iFrame "HsR". rewrite /rrep. iExists RdGone.
        iSplitR; [done |]. iLeft. iExists None.
        iSplitR; [iPureIntro; intros c Hc; discriminate Hc |].
        iSplitL "HL"; [iApply (wdone_wfin with "HL") |].
        rewrite (wsub_cons (S k') Hk) !big_sepL_cons. iFrame "Hsd Hld Hws".
  Qed.

  (* what a fork's panic takes out of the right lend: the pending shot of
     the fork that failed, and the shots above it *)
  Lemma rcr_fork (k : nat) (st0 : fdstate) (γp : pipe_names) :
    RcRf k st0 γp -∗ osP (gF k) ∗ shotsF gF k.
  Proof using .
    rewrite /RcRf. case_decide.
    - iIntros "(_ & _ & _ & _ & _ & _ & $ & $)".
    - iIntros "(_ & [$ _] & $ & _)".
  Qed.

  (* THE [fork]-FAILED TAILS: [fork] goes out as the node's own writer, and
     that is the TERMINAL round -- its writer at the line's end, the main
     loop's prompt still owed *)
  Lemma node_fork_panic (k : nat) (st0 : fdstate) (N : uk_names Σ) `{!ukn_const N}
      (ld : list fdstate) (h' : CpuId) (m' : regfile) (av : nat) (γp : pipe_names) :
    (k < nc)%nat -> ukn_pay N = (fun _ : Z => npay k) -> UkSh.ush_fd2p ld ->
    uint (m' !!! Regidx a0_idx) = 0x1298 ->
    FAM -∗ shk_code (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
    UserFd.ustd (ukn_fd N) ld -∗ RcRf k st0 γp -∗ Cxf k γp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h' m' (mword_of_int ShSyms.panic)
      (UkShDiag.ush_Dg + av) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hfin Hadmit Hcons Hext HlR Hfc Hline HLw Hplok.
    intros Hk Hpeq Hfd2 Ha0.
    iIntros "#Hfam #Hcode #Hjt Hstd HRc [HSh Hsr] Hrun".
    iDestruct (rcr_fork with "HRc") as "[HF #Hsk]".
    iDestruct (UkSh.ush_jtab_ro with "Hjt") as "#Hro".
    assert (HwS : WSh k ∈ wsN) by (apply wids_elem; exact Hk).
    iDestruct "HSh" as "[Hc Hm]".
    iApply (wp_kshd_panic_paid_at (SG := uexecSG_xv6) (PS := uprogSG_free) N 0x1298 alt_panic
              (wcurN γc (WSh k) (1/2) 0 ∗ wmodeN γm (WSh k) (1/2) None ∗ osP (gF k))%I
              (wcurN γc (WSh k) (1/2) 5 ∗ wmodeN γm (WSh k) (1/2) (Some alt_forkc)
               ∗ ptkV T v I (S gen_id))%I
              ld h' m' av Hfd2 Ha0 ltac:(discriminate) ushq_fork_msg_fmt
              ush_fork_msg_len ush_fork_msg_byte ush_fork_msg_nl
              with "[] Hcode Hro Hstd [Hc Hm HF] [Hsr] Hrun").
    - iApply (exf_writer g LM PV CP sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok L pr γc γm P gF gG
                (WSh k) alt_forkc alt_panic 5%nat (EXf fcR pr nc L (WSh k) alt_forkc) _ emp%I _
                HwS ltac:(lia)
                ltac:(intros p b Hp Hb; rewrite alt_forkc_panic;
                      rewrite lookup_app_l; [exact Hb | rewrite ush_fork_msg_len; lia])
                (Hfire (WSh k) alt_forkc HwS (or_intror eq_refl))
                ltac:(intros c Hc; apply (cstep_okV_tok LM PV I sR lR HlR Hadmit (WSh k) alt_forkc c);
                      [lia | rewrite alt_forkc_len; lia |
                       intros j Hj _; rewrite dg_fork_b_len; lia])
                with "Hfam [] [] []").
      + iApply (pexcl_sh LM PV sR lR L pr P gF gG k alt_forkc Hk (or_intror eq_refl)).
      + iIntros "!> (Hc & Hm & HF)". iFrame "Hc Hm".
        rewrite (pdep_unfold LM PV sR lR L pr P gF gG (WSh k) alt_forkc
                   (panic_src_ne alt_forkc (or_intror eq_refl)) (or_intror eq_refl)) /pdep_ne.
        rewrite bool_decide_false; [| intros Hq; exact (dg_pipe_ne_fork (eq_sym Hq))].
        rewrite bool_decide_true; [| done]. iFrame "Hsk HF".
      + iIntros "!> _ Hc Hm HT". iFrame "Hc Hm".
        iDestruct "HT" as "[%Hf | $]". exfalso. revert Hf. vm_compute. discriminate.
    - iFrame "Hc Hm HF".
    - iIntros "_ (Hc & Hm & #HT)". rewrite Hpeq.
      destruct k as [| k'].
      + cbn [npay]. iApply Hfin. iFrame "Hfam Hsr".
        iRight. iRight. iExists 0%nat. iSplitR; [iPureIntro; lia |].
        rewrite /terT. iFrame "Hc Hm HT". done.
      + cbn [npay]. iRight. iRight. iFrame "Hsr". rewrite /rrep. iExists RdGone.
        iSplitR; [done |]. iRight. iExists (S k'). iSplitR; [iPureIntro; lia |].
        rewrite /terT Nat.sub_diag. iFrame "Hc Hm HT". done.
  Qed.

  (* THE PARENT, at 0xea: both children waited, the node reads its pipe and
     pays its own parent (the round, at the top) *)
  Lemma node_parent (k : nat) (st0 : fdstate) (N : uk_names Σ) `{!ukn_const N}
      (h' : CpuId) (m' : regfile) (γp : pipe_names) (r1 r2 rw1 rw2 : mword 64)
      (S1 S2 S3 S4 : gset gname) (avail : nat) :
    (k < nc)%nat -> ukn_pay N = (fun _ : Z => npay k) ->
    r1 <> (mword_of_int (-1) : mword 64) -> r2 <> (mword_of_int (-1) : mword 64) ->
    FAM -∗ shk_code (ukn_t N) -∗
    ush_fork_ans (∅ : gset gname) S1 (RcLf k st0 γp) (Qcf k st0) r1 -∗
    ush_fork_ans S1 S2 (RcRf k st0 γp) (Qcf k st0) r2 -∗
    ush_wait_pid_ans rw1 S2 S3 -∗ ush_wait_pid_ans rw2 S3 S4 -∗
    Rkf k γp -∗ Cxf k γp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h' m' (mword_of_int 0xea) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hfin Hadmit Hcons Hext HlR Hfc HL31 Hline HLw Hplok HRd_tl.
    intros Hk Hpeq Hn1 Hn2.
    iIntros "#Hfam #Hcode Hf1 Hf2 Hw1 Hw2 #HRk [HSh Hsr] Hrun".
    iAssert (⌜S1 <> S2⌝ ∧ ush_fork_ans S1 S2 (RcRf k st0 γp) (Qcf k st0) r2)%I
      with "[Hf2]" as "Hf2'".
    { iSplit; [| iExact "Hf2"].
      iApply (ush_fork_ans_grows (RcRf k st0 γp) (Qcf k st0) r2 S1 S2 Hn2 with "Hf2"). }
    iDestruct "Hf2'" as "[%HS12 Hf2]".
    iDestruct "Hw1" as (pidv) "(%Hpv & %Hm1 & Hw1)".
    iDestruct "Hw2" as (pidw) "(%Hpw & %Hm2 & Hw2)".
    iApply nd_fupd_mwp.
    iMod (pipe_round_answers (QcR k) (RcLf k st0 γp) (RcRf k st0 γp) r1 r2 rw1 rw2
            S1 S2 S3 S4 pidv pidw _ Hpv Hpw Hn1 Hn2 HS12 Hm1 Hm2
            with "Hf1 Hf2 Hw1 Hw2") as "[HQ1 HQ2]".
    iAssert (|={⊤}=> npay k)%I with "[HQ1 HQ2 HSh Hsr]" as ">Hpay".
    { iDestruct "HQ1" as "[#HT | HQ1]";
        [destruct k; iModIntro; [iApply Hfin; iFrame "Hfam Hsr"; by iLeft | by iLeft] |].
      iDestruct "HQ2" as "[#HT | HQ2]";
        [destruct k; iModIntro; [iApply Hfin; iFrame "Hfam Hsr"; by iLeft | by iLeft] |].
      iDestruct (pipe_Qc_two with "HQ1 HQ2") as "[[_ [HRd Hl]] [_ Hr]]".
      iDestruct "HSh" as "[Hc Hm]".
      iMod (node_read k γp Hk with "Hfam HRk Hc Hm Hl Hr") as (ro) "[Hro Hsuf]".
      destruct k as [| k'].
      - cbn [npay]. iMod (top_finish ro with "Hfam Hro Hsuf HRd") as "Hq".
        iModIntro. iApply Hfin. iFrame "Hfam Hq Hsr".
      - cbn [npay]. iModIntro. iRight. iRight. iFrame "Hsr". rewrite /rrep. iExists ro.
        replace (S k' - 1)%nat with k' by lia. iFrame "Hro Hsuf". }
    iModIntro.
    iApply (wp_kshr_exit0_paid (PS := uprogSG_free) N h' m' 0xea 0xec 0xf0
              (mword_of_int 0 : mword 6) (mword_of_int 2970 : mword 21) avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcode [] [] [Hpay] Hrun").
    - iApply (uis_shk_ea with "Hcode").
    - iApply (uis_shk_ec with "Hcode").
    - rewrite Hpeq. iExact "Hpay".
  Qed.

  (* ================================================================= *)
  (*  7.  THE NODE'S BUNDLE                                             *)
  (* ================================================================= *)

  Lemma node_obl_of (k : nat) (st0 : fdstate) (N : uk_names Σ) `{!ukn_const N}
      (ld : list fdstate) (szv cwdv : Z) (av : nat) :
    (k < nc)%nat -> ukn_pay N = (fun _ : Z => npay k) ->
    fd_lowest_closed ld = None -> UkSh.ush_fd2p ld ->
    FAM -∗ ncred k st0 -∗ pbundle (P k) -∗ UkSh.ush_pid N -∗
    shk_code (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
    ush_node_obl (SG := uexecSG_xv6) (PS := uprogSG_free) N ld szv cwdv ∅ av
      (Qcf k st0) (RcLf k st0) (RcRf k st0).
  Proof using Hfin Hadmit Hcons Hext HlR Hfc Hkill HL31 Hline HLw Hplok HRd_tl.
    intros Hk Hpeq Hnone Hfd2.
    iIntros "#Hfam Hcr Hpb Hpid #Hcode #Hjt".
    rewrite /ush_node_obl.
    iExists (ncred k st0), (UkSh.ush_pid N), ush_wait_pid_ans, (Rreg k), (Rkf k), (Cxf k).
    iSplitR.
    { iIntros "!> #Ht". rewrite /Qcf Hkill. by iLeft. }
    iFrame "Hcr".
    iSplitR.
    { iIntros (γp) "Hcr HR". iApply (node_split k st0 γp Hk with "Hcr HR"). }
    iSplitL "Hpb".
    { iApply (ush_pipe_call_paid_reg (PS := uprogSG_free) (fun k H => H) N ld (Rreg k) Hnone).
      iApply (node_registrar k with "Hpb"). }
    iFrame "Hpid".
    iSplitR.
    { iApply (ush_wait0_law_pid (SG := uexecSG_xv6) (PS := uprogSG_free) (fun k H => H) N). }
    iSplitR.
    { iIntros "!>" (h' m') "%Ha0 Hstd Hcr Hrun".
      iApply (node_pipe_panic k st0 N ld h' m' av Hk Hpeq Hfd2 Ha0
                with "Hfam Hcode Hjt Hstd Hcr Hrun"). }
    iSplitR.
    { iIntros "!>" (h' m' r γp) "%Ha0 %Hr _ Hstd HRc HCx Hrun".
      iApply (node_fork_panic k st0 N ld h' m' av γp Hk Hpeq Hfd2 Ha0
                with "Hfam Hcode Hjt Hstd HRc HCx Hrun"). }
    iSplitR.
    { iIntros "!>" (h' m' r γp S1) "%Ha0 %Hr Hans Hstd HCx Hrun".
      iDestruct "Hans" as "[(_ & _ & HRc) | Hpv]"; last first.
      { iDestruct "Hpv" as (γ' pidv) "(%Hr' & %Hrng & _)". exfalso.
        apply (ushq_pid_sext_ne_m1 pidv Hrng). by rewrite -Hr' Hr. }
      iApply (node_fork_panic k st0 N ld h' m' av γp Hk Hpeq Hfd2 Ha0
                with "Hfam Hcode Hjt Hstd HRc HCx Hrun"). }
    iIntros (h' m' γp r1 r2 rw1 rw2 S1 S2 S3 S4)
      "%Hn1 %Hn2 Hf1 Hf2 Hw1 Hw2 _ _ _ _ _ HRk HCx _ Hrun".
    iApply (node_parent k st0 N h' m' γp r1 r2 rw1 rw2 S1 S2 S3 S4 _ Hk Hpeq Hn1 Hn2
              with "Hfam Hcode Hf1 Hf2 Hw1 Hw2 HRk HCx Hrun").
  Qed.

  (* ================================================================= *)
  (*  8.  THE LAW, PAID: the line's stages and sh's ledger               *)
  (* ================================================================= *)

  (* the stages as the parse cut them: the producer's command [args0],
     then [cat] n times *)
  Context (s0 : Z) (gs : nat -> bv 8) (stgs : list (list uarg)).
  Hypothesis Hlen : length stgs = S nc.
  Context (args0 : list uarg).
  Hypothesis Hst0 : stgs !! 0%nat = Some args0.
  Hypothesis Hstc : forall k, (1 <= k <= nc)%nat ->
    exists a b, stgs !! k = Some (UkShMain.ush_args s0 gs (UkShCat.cat_toks a b))
                /\ UkShCat.cat_argv_bytes a b gs.
  (* sh's ledger at the top node: fds 1 and 2 the console, nothing shut *)
  Context (ld0 : list fdstate) (rb1 rb2 : bool).
  Hypothesis Hld1 : ld0 !! 1%nat = Some (FdOpen rb1 true (FdDevice ConsoleInv.CONSOLE)).
  Hypothesis Hld2 : ld0 !! 2%nat = Some (FdOpen rb2 true (FdDevice ConsoleInv.CONSOLE)).
  Hypothesis Hnone : fd_lowest_closed ld0 = None.

  Local Notation rd γp := (FdOpen true false (FdPipe γp)).
  Local Notation wr γp := (FdOpen false true (FdPipe γp)).

  Lemma ld0_len : (2 < length ld0)%nat.
  Proof using Hld2. exact (lookup_lt_Some _ _ _ Hld2). Qed.

  (* THE LEFT STAGES: the producer's law at stage 0, a middle cat below *)
  Lemma left_law_holds (szv : Z) (e : nat) :
    FAM -∗ PLAW args0 -∗ UShCatPay.sh_cat_slot T -∗
    ush_left_law (SG := uexecSG_xv6) (PS := uprogSG_free) stgs ld0 szv FsImg.ROOTINO (6 + e)
      Qcf RcLf.
  Proof using Hadmit Hcons Hext HlR Hsup Hfc Hkill HL31 Hld2 Hlen Hline HLw Hplok Hst0 Hstc pnsRegG0 uartGhostG0.
    pose proof nc_pos as Hn.
    iIntros "#Hfam #Hpl #Hcs". rewrite /ush_left_law.
    iIntros (k st0 args N' h' m' γ' γp q av)
      "%Hk %Hlt %Hav %Hpeq %Ha0 _ #Hck #Hjt #Hcmd Hsz Hstd Hcwd Hch _ _ HRc Hrun".
    pose proof ld0_len as Hl.
    set (ld := <[1%nat := wr γp]> (<[0%nat := st0]> ld0)).
    assert (H1 : ld !! 1%nat = Some (wr γp)).
    { rewrite /ld. apply list_lookup_insert. rewrite length_insert. lia. }
    assert (H2 : ld !! 2%nat = Some (FdOpen rb2 true (FdDevice ConsoleInv.CONSOLE))).
    { rewrite /ld list_lookup_insert_ne; [| lia]. rewrite list_lookup_insert_ne; [| lia].
      exact Hld2. }
    destruct k as [| k'].
    - rewrite Hst0 in Hk. injection Hk as <-.
      rewrite /prod_stage_law /RcLf. iDestruct "HRc" as "[HRc HRd]".
      iApply ("Hpl" $! N' h' m' γp q szv ld av with "[%] [%] [%] [%] [%] Hck Hjt Hcmd Hsz Hstd
                Hcwd Hch HRc HRd Hrun").
      + exact Hpeq.
      + exact Ha0.
      + exists false; exact H1.
      + exists rb2; exact H2.
      + lia.
    - destruct (Hstc (S k') ltac:(lia)) as (a & b & Hka & Hab).
      rewrite Hka in Hk. injection Hk as <-.
      rewrite /RcLf. destruct (gin_of st0) as [gin |] eqn:Hg; [| iDestruct "HRc" as %[]].
      destruct (gin_of_some st0 gin Hg) as [wb ->].
      assert (H0 : ld !! 0%nat = Some (FdOpen true wb (FdPipe gin))).
      { rewrite /ld list_lookup_insert_ne; [| lia]. apply list_lookup_insert. lia. }
      iApply (stage_mid g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31 pr
                Rd γc γm P gF gG Hfire k' a b s0 gs N' h' m' gin γp q szv ld av
                Hab ltac:(lia) Hpeq Ha0
                ltac:(split; [exists wb; exact H0 | split; [exists false; exact H1 |
                                                          exists rb2; exact H2]])
                ltac:(lia)
                with "Hfam Hcs Hck Hjt Hcmd Hsz Hstd Hcwd Hch HRc Hrun").
  Qed.

  (* THE LAST STAGE *)
  Lemma last_law_holds (szv : Z) (e : nat) :
    FAM -∗ UShCatPay.sh_cat_slot T -∗
    ush_last_law (SG := uexecSG_xv6) (PS := uprogSG_free) stgs ld0 szv FsImg.ROOTINO (6 + e)
      Qcf RcRf.
  Proof using Hadmit Hcons Hext HlR Hsup Hfc Hkill HL31 Hld1 Hld2 Hlen Hline HLw Hplok Hstc pnsRegG0 uartGhostG0.
    pose proof nc_pos as Hn.
    iIntros "#Hfam #Hcs". rewrite /ush_last_law.
    iIntros (k st0 args N' h' m' γ' γp q av)
      "%Hk %Hlen' %Hav %Hpeq %Ha0 _ #Hck #Hjt #Hcmd Hsz Hstd Hcwd Hch _ _ HRc Hrun".
    pose proof ld0_len as Hl.
    assert (Hnc : nc = S k) by lia.
    destruct (Hstc (S k) ltac:(lia)) as (a & b & Hka & Hab).
    rewrite Hka in Hk. injection Hk as <-.
    rewrite /RcRf. case_decide as Hq; [| lia].
    set (ld := <[0%nat := rd γp]> ld0).
    assert (H0 : ld !! 0%nat = Some (rd γp)) by (apply list_lookup_insert; lia).
    assert (H1 : ld !! 1%nat = Some (FdOpen rb1 true (FdDevice ConsoleInv.CONSOLE))).
    { rewrite /ld list_lookup_insert_ne; [exact Hld1 | lia]. }
    assert (H2 : ld !! 2%nat = Some (FdOpen rb2 true (FdDevice ConsoleInv.CONSOLE))).
    { rewrite /ld list_lookup_insert_ne; [exact Hld2 | lia]. }
    iApply (stage_last g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31 pr
              Rd γc γm P gF gG Hfire k a b s0 gs N' h' m' γp q szv ld av
              Hab Hnc Hpeq Ha0
              ltac:(split; [exists false; exact H0 | split; [exists rb1; exact H1 |
                                                         exists rb2; exact H2]])
              ltac:(lia)
              with "Hfam Hcs Hck Hjt Hcmd Hsz Hstd Hcwd Hch HRc Hrun").
  Qed.

  (* THE ENTRY: node [k]'s right child is node [k+1]: it shoots the fork
     that made it and takes its bundle *)
  Lemma entry_law_holds (szv : Z) (e : nat) :
    FAM -∗
    ush_entry_law_g (SG := uexecSG_xv6) (PS := uprogSG_free) stgs ld0 szv FsImg.ROOTINO (6 + e)
      Qcf RcLf RcRf.
  Proof using Hfin Hadmit Hcons Hext HlR Hfc Hkill HL31 Hld2 Hlen Hline HLw Hnone Hplok HRd_tl.
    pose proof nc_pos as Hn.
    iIntros "#Hfam". rewrite /ush_entry_law_g.
    iIntros (k st0 N' γ' γp av) "%Hlt %Hav %Hpeq _ HRc Hpid #Hck #Hjt".
    pose proof ld0_len as Hl.
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    rewrite /RcRf. case_decide as Hq; [lia |].
    iDestruct "HRc" as "(#Hinv & [#Hsk #Hinvs] & HF & Hr & HsR & Hno & Hbel)".
    iMod (os_shoot with "HF") as "#HFs".
    iDestruct (shotsF_snoc with "Hsk HFs") as "#Hsk'".
    iDestruct "Hno" as "(HSh & HL & HF' & HG' & Hpb)".
    iModIntro.
    iApply (node_obl_of (S k) (rd γp) N' (<[0%nat := rd γp]> ld0) szv FsImg.ROOTINO av
              ltac:(lia) Hpeq
              (ush_fd_lowest_insert0 ld0 (rd γp) ltac:(discriminate) Hnone)
              ltac:(exists rb2; rewrite list_lookup_insert_ne; [exact Hld2 | lia])
              with "Hfam [HSh HL HF' HG' Hbel Hr HsR] Hpb Hpid Hck Hjt").
    rewrite /ncred. iFrame "HSh HL HF' HG' Hbel". iSplitR.
    - rewrite /nknow. iFrame "Hsk'". rewrite seq_S big_sepL_app big_sepL_singleton /=.
      iFrame "Hinvs". iExists γp. iExact "Hinv".
    - rewrite /ninp /=. iFrame "Hinv Hr HsR".
  Qed.

  (* THE WHOLE RIGHT SPINE, PAID: sh's forked child running [runcmd] on
     [echo .. | cat | .. | cat], every process of the pipeline accounted
     for, pays the round's [Qtop] *)
  Theorem wp_pipes_round (rest : list (list uarg)) (a b : list uarg)
      (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile) (t szv : Z) (st0 : fdstate) (e : nat) :
    stgs = a :: b :: rest ->
    ukn_pay N = (fun _ : Z => Qfin) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld0 !! 0%nat = Some st0 -> st0 <> FdClosed ->
    FAM -∗ PLAW args0 -∗ UShCatPay.sh_cat_slot T -∗
    ncred 0 st0 -∗ pbundle (P 0) -∗ UkSh.ush_pid N -∗
    shk_code (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (ush_pipes a (b :: rest)) -∗
    usz (ukn_s N) szv -∗ UserFd.ustd (ukn_fd N) ld0 -∗
    ush_cldep (SG := uexecSG_xv6) (PS := uprogSG_free) st0 -∗
    UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ UserChildren.uch (ukn_ch N) ∅ -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h m (mword_of_int ShSyms.runcmd)
      (6 + (2 + (UkShDiag.ush_Dg + (6 * length rest + (6 + e))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hfin Hadmit Hcons Hext HlR Hsup Hfc Hkill HL31 Hld1 Hld2 Hlen Hline HLw Hnone Hplok Hst0 Hstc pnsRegG0 uartGhostG0 HRd_tl.
    pose proof nc_pos as Hn.
    intros Hstg Hpeq Ha0 Hl0 Hne0.
    iIntros "#Hfam #Hpl #Hcs Hcr Hpb Hpid #Hcode #Hjt #Hcmd Hsz Hstd #Hcd0 Hcwd Hch Hrun".
    pose proof ld0_len as Hl.
    iAssert (UserFd.ustd (ukn_fd N) (<[0%nat := st0]> ld0)) with "[Hstd]" as "Hstd".
    { rewrite (list_insert_id ld0 0%nat st0 Hl0). iExact "Hstd". }
    iApply (wp_kshr_runcmd_pipes_law_g (SG := uexecSG_xv6) (PS := uprogSG_free) (fun k H => H)
              stgs ld0 (FdOpen rb1 true (FdDevice ConsoleInv.CONSOLE)) szv FsImg.ROOTINO (6 + e)
              Qcf RcLf RcRf (fun _ _ _ _ => eq_refl) Hld1 ltac:(discriminate)
              ltac:(intros rb wb gp Hq; discriminate Hq) ltac:(lia)
              rest a b 0%nat N h m t st0 ∅ ltac:(rewrite Hstg; reflexivity) Ha0 Hne0
              with "[] [] [] Hcode Hjt Hcmd Hsz Hstd Hcd0 Hcwd Hch [Hcr Hpb Hpid] Hrun").
    - iModIntro. iApply (left_law_holds with "Hfam Hpl Hcs").
    - iModIntro. iApply (last_law_holds with "Hfam Hcs").
    - iModIntro. iApply (entry_law_holds with "Hfam").
    - iApply (node_obl_of 0 st0 N (<[0%nat := st0]> ld0) szv FsImg.ROOTINO
                (6 * length rest + (6 + e)) ltac:(lia) Hpeq
                (ush_fd_lowest_insert0 ld0 st0 Hne0 Hnone)
                ltac:(exists rb2; rewrite list_lookup_insert_ne; [exact Hld2 | lia])
                with "Hfam Hcr Hpb Hpid Hcode Hjt").
  Qed.

  (* ...AT THE ROUND'S ALLOCATION: the top node's credential assembled from
     the family's halves, the nodes' names and [Rtop] *)
  Theorem wp_pipes_round_alloc (rest : list (list uarg)) (a b : list uarg)
      (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile) (t szv : Z) (st0 : fdstate)
      (e : nat) :
    stgs = a :: b :: rest ->
    ukn_pay N = (fun _ : Z => Qfin) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld0 !! 0%nat = Some st0 -> st0 <> FdClosed ->
    FAM -∗ PLAW args0 -∗ UShCatPay.sh_cat_slot T -∗
    ([∗ list] w ∈ wsN, halvesN w) -∗
    ([∗ list] j ∈ seq 0 nc, osP (gF j) ∗ osP (gG j) ∗ pbundle (P j)) -∗
    Rtop -∗ Rd -∗ UkSh.ush_pid N -∗
    shk_code (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (ush_pipes a (b :: rest)) -∗
    usz (ukn_s N) szv -∗ UserFd.ustd (ukn_fd N) ld0 -∗
    ush_cldep (SG := uexecSG_xv6) (PS := uprogSG_free) st0 -∗
    UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ UserChildren.uch (ukn_ch N) ∅ -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h m (mword_of_int ShSyms.runcmd)
      (6 + (2 + (UkShDiag.ush_Dg + (6 * length rest + (6 + e))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hfin Hadmit Hcons Hext HlR Hsup Hfc Hkill HL31 Hld1 Hld2 Hlen Hline HLw Hnone Hplok Hst0 Hstc pnsRegG0 uartGhostG0 HRd_tl.
    intros Hstg Hpeq Ha0 Hl0 Hne0.
    iIntros "#Hfam #Hpl #Hcs Hh Ho HR HRd Hpid #Hcode #Hjt #Hcmd Hsz Hstd #Hcd0 Hcwd Hch Hrun".
    iDestruct (ncred0_of st0 nc_pos with "Hh Ho HR HRd") as "[Hcr Hpb]".
    iApply (wp_pipes_round rest a b N h m t szv st0 e Hstg Hpeq Ha0 Hl0 Hne0
              with "Hfam Hpl Hcs Hcr Hpb Hpid Hcode Hjt Hcmd Hsz Hstd Hcd0 Hcwd Hch Hrun").
  Qed.
  (* ---- THE PRODUCER'S LAW, per producer ---- *)
  Lemma plaw_echo `{!Persistent Rd} (ws : list (list (bv 8))) :
    pr = PrEcho ws -> line_ok ws -> echo_argv_bytes ws gs ->
    FAM -∗ UShEcho.sh_echo_slot T -∗ PLAW (UkShMain.ush_args s0 gs (echo_toks ws)).
  Proof using HL31 HLw Hadmit Hcons Hext HlR Hsup Hfc Hkill Hline Hplok pnsRegG0.
    intros Hpr Hok Hbytes. iIntros "#Hfam #Hes".
    iApply (stage_echo_law g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31 pr
              Rd γc γm P gF gG Hfire ws s0 gs Hpr Hok Hbytes
              ltac:(rewrite HLw Hpr; reflexivity) nc_pos with "Hfam Hes").
  Qed.

  (* [cat f] at the head: [UShCatFStage.stage_catf_law_holds], at the deed *)
End UShPipesNode.
