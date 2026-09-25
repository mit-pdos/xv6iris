(* ===================================================================== *)
(*  UShUPipes.v -- THE UNION ROUND'S PIPELINE BRANCH, AND THE ROUND LAW   *)
(*  WITH NO PREMISE (cut C9f2; design: claude-notes/design/union.md       *)
(*  section 3, 'The pipeline walk with cat f at stage 0', review B3).     *)
(*                                                                        *)
(*  [UShURound.sh_round_holds_union] took the pipeline lines as a premise *)
(*  ([ush_pipes_branch]).  This file discharges it at the union claim     *)
(*  [UnionOut.ucl], its view [UnionView.pview_unionU] and the widened     *)
(*  credential at the pipeline's shapes [UShURoundShapes.upterm_shape] /  *)
(*  [updone_shape]:                                                       *)
(*    - the CHILD LAWS: [echo ws | cat^n] ([PipesCut.pipes_lp]) and       *)
(*      [cat f | cat^n] ([PipesCut.pipes_lpc]) parse the line             *)
(*      ([UkShPipesRound.wp_kshm_child_pipes_g]), open the lend and the   *)
(*      deed, allocate the N-writer family at the round's state [sR]      *)
(*      (the deed's content, [UnionOut.pwc_blkU_entry]), and run the      *)
(*      right spine ([UShPipesNode.wp_pipes_round_alloc]) with the        *)
(*      producer's stage law: echo's [plaw_echo], [cat f]'s               *)
(*      [UShCatFStage.stage_catf_law_holds] at the deed;                  *)
(*    - THE DEED THROUGH NODE 0: for [cat f] node 0 keeps the ticket and  *)
(*      the tie ([Rtop]) and LENDS the deed's half [fdq r (1/2) s] as the *)
(*      producer's loan [Rd], which comes back in node 0's left report and *)
(*      the committed [Qtop]; for echo the whole deed stays in [Rtop].     *)
(*      The committed round hands the deed back at its PRE tie            *)
(*      ([UShURoundDefs.uWcu]'s index-0 arm); a TERMINAL round (a fork    *)
(*      failed) carries no deed (B3: the stray [cat f] may hold it);      *)
(*    - the BODY LAW at the pipeline lines: echo's through                *)
(*      [UkShPipeForkTwin.wp_kshm_body_pipe], [cat f]'s through the cat   *)
(*      body walk at any [ca] line ([UkShRedirBody.wp_kshm_body_ca_with]) *)
(*      at the pipe era's fork twin;                                      *)
(*    - [sh_round_holds_union_closed]: the round law with no premise.     *)
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
Require Import ProcGeom UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UserCwd UserChildren.
Require Import ChildTok.
Require Import FsCfg FsImg.
Require Import UexecSlot UexecRet UexecSG UexecExecInst UexecExecMint.
Require Import LineWords EchoDisc EchoOut AppEcho.
Require Import LineModel LineModelLinks GenOut.
Require Import FileDisc FileState.
Require Import AppCfg AppInv AppFile AppFileCons FileOpen FileOut FileLinksLine FileLinkGen.
Require Import PipeOut.
Require Import PipesDisc PipeBothNPure PipeBothN PipeOutN PipesView.
Require Import PipeNames PipeProto.
Require Import ProgTree.
Require Import CtxIdDefs.
Require Import UCodeShK UCodeShP.
Require Import UkSh UkShRun UkShMain UkShDiag UkShFork UkShMalloc.
Require Import UkShEcho UkShCat.
Require Import UkShPipe UkShPipeLex UkShPipesRound UkShPipesSeam UkShPipesLex UkShPipesCmd.
Require Import UShEcho UShCatPay.
Require Import UkPipesIface.
Require Import GenLinksLine LinkRec.
Require Import UShPipesDefs UShPipesStage UShPipesNode.
Require Import UkShPipesFork.
Require Import PipesUline PipesCut.
Require Import UkCatFIface UShCatFStage.
Require Import UnionDisc UnionView UnionOut UnionLinks UnionLinkInst UnionLinkInstAt.
Require Import UShLine UShURoundDefs UShURound UShURoundShapes.
Require Import UkShPipeForkTwin UkShCatForkTwin UkShRedirBody.
Require UShPipesLaw UShRest UInitSh SpecKexec ElfUser UkPipesEntries FileDeltas UkFileIface.
Require User.ShSyms.
Local Open Scope Z_scope.

Local Notation U := ulmU.

(* ===================================================================== *)
(*  S0  PURE: THE UNION READS A PIPELINE BODY AS ITS PIPELINE             *)
(* ===================================================================== *)

(* an admissible pipeline's body parses as that pipeline, at either
   producer *)
Lemma uline_of_u_pipe (p : producer) (n : nat) :
  FileDisc.uline_ok (FileDisc.LPipe p n) ->
  uline_of_u (FileDisc.line_body (FileDisc.LPipe p n)) = FileDisc.LPipe p n.
Proof using.
  intros Hok. pose proof Hok as (Hp & Hn & _).
  rewrite /uline_of_u.
  destruct (FileDisc.parse_line (FileDisc.line_body (FileDisc.LPipe p n))) as [l |] eqn:Hpl.
  - exfalso. pose proof (FileDisc.line_body_parse _ _ Hpl) as Hb.
    pose proof (FileDisc.parse_line_ok _ _ Hpl) as Hl.
    assert (Hw : wl_words (FileDisc.line_body l) = FileDisc.uline_ws (FileDisc.LPipe p n)).
    { rewrite -Hb. exact (FileDisc.uline_ws_pipe p n Hp). }
    pose proof (uline_pipes_words l p n Hl Hp Hn Hw) as ->.
    exact (FileDisc.parse_line_not_pipe _ p n Hpl).
  - rewrite (_ : FileDisc.LPipe p n = uline_of_pl (LPipes p n)); [| reflexivity].
    rewrite (line_body_of_pl_all (LPipes p n))
            (pl_parse_body (LPipes p n) (pl_ok_of_uline p n Hok)).
    reflexivity.
Qed.

(* ...AND THE ROUND'S LINE IS IT, off the fork's words *)
Lemma ul_pipe (I : list (bv 8)) (p : producer) (n : nat) :
  FileDisc.fline_ok (UkSh.ush_lastbody I) -> FileDisc.uline_ok (FileDisc.LPipe p n) ->
  last_ws I = FileDisc.uline_ws (FileDisc.LPipe p n) ->
  ul I = FileDisc.LPipe p n.
Proof using.
  intros Hfb Hok Hlws. pose proof Hok as (Hp & Hn & _).
  assert (Hb : UkSh.ush_lastbody I = FileDisc.line_body (FileDisc.LPipe p n)).
  { apply (fline_ok_pipes_words_p _ p n Hfb Hp Hn).
    rewrite /UkSh.ush_lastbody -last_ws_lastbody. exact Hlws. }
  rewrite ul_lastbody Hb. exact (uline_of_u_pipe p n Hok).
Qed.

Lemma upv_line_pipe (I : list (bv 8)) (p : producer) (n : nat) :
  ul I = FileDisc.LPipe p n ->
  pv_line pview_unionU (lineV U I) = Some (LPipes p n).
Proof using.
  intros Hul. change (pv_line pview_unionU (lineV U I)) with (uv_line (ul I)).
  rewrite Hul. reflexivity.
Qed.

(* at most sixteen cats fit a line, at either producer *)
Lemma upls_cats_le (p : producer) (n : nat) :
  FileDisc.uline_ok (FileDisc.LPipe p n) -> (n <= 16)%nat.
Proof using.
  intros (_ & _ & Hlm). rewrite line_bytes_pipe_length_p in Hlm.
  unfold EchoDisc.line_max in Hlm. lia.
Qed.

(* the input is not empty: its last line has words *)
Lemma unlines_pos (I : list (bv 8)) (p : producer) (n : nat) :
  FileDisc.prod_ok p ->
  last_ws I = FileDisc.uline_ws (FileDisc.LPipe p n) -> (1 <= nlines I)%nat.
Proof using.
  intros Hp Hlws. apply UShPipesLaw.nlines_pos_of_ws. rewrite Hlws.
  cbn [FileDisc.uline_ws]. pose proof (FileDisc.prod_words_ne p Hp) as Hne.
  intros Hq. apply Hne. destruct (FileDisc.prod_words p); [done | discriminate Hq].
Qed.

(* the [cat f] producer's content at the round's state *)
Lemma catf_content (sR : fstate) :
  prod_content (files_of sR) (PrCatF fname_f) = default [] sR.
Proof using. cbn [prod_content]. by rewrite files_of_f. Qed.

(* the reports a [cat f] producer may give: the write error only when
   [f] is there *)
Definition catf_ds (s : dst) : list (list (bv 8)) :=
  match s with Some _ => [[]; cat_dg_write] | None => [[]] end.

(* the deed's state is the round's, so [cat f] reads the producer's
   content -- or finds no [f] *)
Lemma catf_case (s : dst) :
  (snd <$> s = Some (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f))
   /\ pv_fc pview_unionU (dst_content s) fname_f
      = Some (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f))
   /\ catf_ds s = [[]; cat_dg_write])
  \/ (s = None /\ catf_ds s = [[]]).
Proof using.
  destruct s as [[i c] |]; [left | right; split; reflexivity].
  change (pv_fc pview_unionU) with files_of.
  cbn [prod_content]. rewrite files_of_f. split_and!; reflexivity.
Qed.

(* ...and that content is short, as the deed's typing says *)
Lemma catf_short (sR : fstate) :
  (forall c, sR = Some c -> (Z.of_nat (length c) < 2 ^ 31)%Z) ->
  pns_short (prod_content (pv_fc pview_unionU sR) (PrCatF fname_f)).
Proof using.
  intros H. change (pv_fc pview_unionU) with files_of. rewrite catf_content /pns_short.
  destruct sR as [c |]; cbn [default]; [exact (H c eq_refl) | by vm_compute].
Qed.

(* ===================================================================== *)
(*  S1  THE BRANCH                                                        *)
(* ===================================================================== *)
Section UShUPipes.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER ([UShRound]'s header): every walk is pinned
     at [Xv6Cameras.offbox_offG] *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{!pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ, !cifRegG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.
  #[local] Existing Instance eo_turn | 0.

  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl gf)) r).
  Context (s0 : fstate).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = ucl ug).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl gf)).

  Local Notation T := (file_taint (fgn_cl gf)).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PT := (upterm_shape ug).
  Local Notation PD := (updone_shape ug).
  Local Notation Wcu := (uWcu ug r s0 PT PD).
  Local Notation Wbu := (uWbf ug r s0).
  Local Notation pg := (ugn_pipe ug).
  Local Notation CPU := (ucparams ug).
  Local Notation WAU := (uwa ug).
  Local Notation DPRE := (ush_deed_at ug r upre_tie s0).

  #[local] Instance uup_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance uup_T_tl0 : Timeless T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.

  (* the application's supply answers out of the taint *)
  Lemma usup : ⊢ □ (T -∗ app_sup).
  Proof using Heq.
    iIntros "!> #Ht". rewrite /AppInv.app_sup Heq. cbn [app_pred app_run].
    iApply (file_sup_of_taint (fgn_cl gf) r with "Ht").
  Qed.

  Local Lemma uup_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* =================================================================== *)
  (*  S1a  WHAT THE TOP NODE PAYS, read into the child's exit payload     *)
  (* =================================================================== *)

  (* [Rk] is what node 0 keeps of the deed, [Rd] what it lends its left
     child; together they are the deed at its PRE tie.  A committed round
     gives both back (the round's shape and the deed); a terminal one
     drops [Rk] (B3) *)
  Lemma ufin (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline')
      (L : list (bv 8)) (pr : producer) (Rd Rk : iProp Σ)
      (P : nat -> pnames) (gF gG : nat -> gname) (γc γm : wid -> gname) :
    pv_line pview_unionU (lineV U I) = Some lR -> adm_u_f lR = true -> pl_ok lR ->
    (1 <= nlines I)%nat ->
    (Rk ∗ Rd ⊢ DPRE I) ->
    ((era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I ∗ Rk)
     ∗ blkN_inv (wids (lcats lR)) (runN (pv_fc pview_unionU sR) lR)
         (pwc_blkV pg U (gcPIN CPU) (gcW CPU) (gcT CPU) v I sR)
         termw (tokN (pv_fc pview_unionU sR) lR)
         (pdep U pview_unionU sR lR L pr P gF gG) pnsN (S gen_id) γc γm
     ∗ Qtop U CPU v I lR Rd γc γm
     ⊢ UkShFork.ushf_wq Wcu I).
  Proof using .
    intros HlR Ha Hl Hpos Hdeed.
    iIntros "((#Hpin & #Hlb & Hk) & #Hinv & Hq)".
    rewrite /UkShFork.ushf_wq. iRight.
    rewrite /Qtop. iDestruct "Hq" as "[#HT | [[Hall HRd] | Hter]]".
    - iApply (uWcu_taint ug r s0 PT PD I 0%nat v with "Hpin HT").
    - (* COMMITTED: every writer at its whole source, the loan back *)
      rewrite /uWcu. iRight. iRight. iSplitR; [done |].
      iSplitR "Hk HRd"; last first.
      { iApply Hdeed. iFrame "Hk HRd". }
      rewrite /updone_shape.
      iExists v, γc, γm, (pdep U pview_unionU sR lR L pr P gF gG), sR, lR.
      iSplitR.
      { iPureIntro. split_and!; [intros ??; apply pdep_timeless | exact HlR | exact Ha | exact Hl]. }
      iFrame "Hpin Hlb Hinv".
      iApply (big_sepL_mono with "Hall"). iIntros (k w _) "Hw".
      rewrite /wdone. iDestruct "Hw" as (s) "[Hw %Ht]".
      iEval (cbn [pns_wfin]) in "Hw". iDestruct "Hw" as "[Hc Hm]".
      iExists s. iFrame "Hc Hm". by iPureIntro.
    - (* TERMINAL: a fork failed at node [i]; no deed *)
      iDestruct "Hter" as (i) "(%Hi & Hter & Hws)".
      rewrite /terT. iDestruct "Hter" as "(Hc & Hm & #Htk)".
      iAssert ([∗ list] j ∈ seq 0 i, ∃ s : list (bv 8),
                 wcurN γc (WLeft j) (1/2) (length s) ∗ wmodeN γm (WLeft j) (1/2) (Some s))%I
        with "[Hws]" as "Hws".
      { iApply (big_sepL_mono with "Hws"). iIntros (k j _) "Hw".
        rewrite /wdone. iDestruct "Hw" as (s) "[Hw _]".
        iEval (cbn [pns_wfin]) in "Hw". iExists s. iExact "Hw". }
      iDestruct (big_sepL_exist_fun [] (seq 0 i) _ (NoDup_seq 0 i) with "Hws") as (sw) "Hws".
      rewrite /uWcu. iRight. iLeft. iSplitR; [iPureIntro; lia |].
      rewrite /upterm_shape.
      iExists v, γc, γm, (pdep U pview_unionU sR lR L pr P gF gG), i, sw, sR, lR.
      iSplitR.
      { iPureIntro. split_and!; [intros ??; apply pdep_timeless | exact HlR | exact Ha
                                | exact Hl | exact Hi | exact Hpos]. }
      iFrame "Hpin Hlb". rewrite /pwc_fork_exitN. iFrame "Hinv Hc Hm Htk".
      rewrite /heldN big_sepL_fmap. cbn [fst snd]. iExact "Hws".
  Qed.

  (* =================================================================== *)
  (*  S1b  THE LEND AND THE DEED, OPENED AT THE ROUND                     *)
  (* =================================================================== *)

  (* the deed's typing: a well-formed state, and a short content *)
  Lemma udeed_typed (s : dst) :
    f_typed (fgn_cl gf) s -∗
    ⌜fstate_ok (dst_content s)
     /\ forall c, dst_content s = Some c -> (Z.of_nat (length c) < 2 ^ 31)%Z⌝.
  Proof using .
    destruct s as [[i0 bs0] |]; last first.
    { iIntros "_". iPureIntro. split; [done | intros c Hc; discriminate Hc]. }
    rewrite /f_typed. iIntros "H". iDestruct "H" as (ls0) "[_ %Hbt]". iPureIntro.
    pose proof (FileDeltas.f_bytes_typed_short ls0 bs0 Hbt) as Hb.
    unfold EchoDisc.line_max in Hb.
    destruct Hbt as (ws0 & sel & _ & Hok0 & Hsel & ->). split.
    - exact (fcont_ok_subseq ws0 sel Hok0 Hsel).
    - intros c Hc. injection Hc as <-. lia.
  Qed.

  (* THE LEND AT THE LOOP'S LINE INDEX AND THE DEED AT ITS PRE TIE, as the
     family's allocation takes them: one choice list, one state -- or the
     taint *)
  Lemma uopen (I : list (bv 8)) :
    uWcl ug s0 I 3%nat -∗ ush_pre_at ug r s0 I -∗
    T ∨ ∃ (v : era_pins) (cs : list nat) (s : dst),
          ⌜upre_tie cs s0 I (dst_content s)⌝
          ∗ era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I ∗ cs_lb v cs
          ∗ f_typed (fgn_cl gf) s ∗ fown r s
          ∗ pwc_blkU ug v I (dst_content s) (S gen_id) [] false.
  Proof using .
    iIntros "Hc [Hpre _]".
    rewrite {1}/ush_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; last by iLeft.
    iDestruct "Hpre" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    rewrite /uWcl /lk_lcred. iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr]. rewrite /gwc_blk.
    iDestruct "Hc" as "[Hc | #HT]"; last by iLeft.
    iDestruct "Hc" as (ps cs sw P0) "(%Hw & Htn & #Hps & #Hcs & #HE & #HW)".
    cbn [gW union_params_at]. rewrite /f0w_at.
    iDestruct "HW" as "[Hf %Hs]". subst sw.
    iAssert (f0cw gf (S gen_id) s0) as "#Hcw".
    { rewrite /f0w. iDestruct "Hf" as "[_ Hf]". rewrite /f0cw. iExact "Hf". }
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
    pose proof Hw as [(Hpin0 & Hr & Hn & HP) Htail].
    pose proof Htie as [Hlen Hcon].
    iEval (cbn [lm_blkcs]) in "Hcs". iEval (rewrite Nat.add_0_r) in "Htn".
    iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    iRight. iExists v, cs, s.
    iSplitR; [iPureIntro; exact Htie |].
    rewrite Hcon /ust.
    iPoseProof (pwc_blkU_entry ug v I (S gen_id) ps cs s0 P0 Hw with "Hpin Hcw Htn Hps Hcs HE")
      as "HPW".
    iFrame "HPW Hd Hty Hpin' Hcs HE".
  Qed.

  (* =================================================================== *)
  (*  S1c  THE CHILD LAWS                                                 *)
  (* =================================================================== *)
  Local Notation pc0 pw := (Nat.add (length (wl_body pw)) 3).
  Local Notation RT pw n := (ushq_rtoks (pc0 pw) (replicate n ushq_cat)).
  (* the parser's stages, and the right spine's tail below the first cat *)
  Local Notation STG pw n len gb sa :=
    (map (UkShMain.ush_args sa (pcut pw n len gb)) (wl_toks pw :: RT pw n)).
  Local Notation REST pw n' len gb sa :=
    (map (UkShMain.ush_args sa (pcut pw (S n') len gb))
       (ushq_rtoks (pc0 pw + length ushq_cat + 3) (replicate n' ushq_cat))).

  (* the parse's last malloc token is the break *)
  Local Lemma uup_um_usz (N : uk_names Σ) (sz : Z) (m : nat) :
    ⊢ ushq_um (ghost_varG0 := offbox_offG) N sz (0 + 2 * m + 1)%nat -∗
      usz (ukn_s N) (sz + 65536).
  Proof using . rewrite Nat.add_0_l Nat.add_1_r. iApply ushq_um_usz. Qed.

  (* the stages as the parser cut them, at either producer *)
  Lemma ustg_len (pw : list (list (bv 8))) (n : nat) (len : nat) (gb : nat -> bv 8) (sa : Z) :
    length (STG pw n len gb sa) = S n.
  Proof using . rewrite length_map. cbn [length]. by rewrite rtoks_cats_length. Qed.

  Lemma ustg_cats (p : producer) (n : nat) (len : nat) (gb : nat -> bv 8) (sa : Z) :
    UkSh.ush_line_at (FileDisc.LPipe p n) gb 0 len ->
    forall k, (1 <= k <= n)%nat ->
      exists a b, STG (prod_words p) n len gb sa !! k
                    = Some (UkShMain.ush_args sa (pcut (prod_words p) n len gb) (UkShCat.cat_toks a b))
                  /\ UkShCat.cat_argv_bytes a b (pcut (prod_words p) n len gb).
  Proof using .
    intros Hlat k Hk. destruct k as [| k]; [lia |].
    exists (pc0 (prod_words p) + 6 * k)%nat, (pc0 (prod_words p) + 6 * k + 3)%nat. split.
    - rewrite map_lookup_fmap.
      rewrite (_ : (wl_toks (prod_words p) :: RT (prod_words p) n) !! S k
                   = RT (prod_words p) n !! k); [| reflexivity].
      rewrite rtoks_cats_lookup; [reflexivity | lia].
    - exact (pcut_cat_bytes_p p n gb len k Hlat ltac:(lia)).
  Qed.

  (* the taint's generic continuation, off the cat slot, at the child *)
  Local Lemma uup_genw (N' : uk_names Σ) (I : list (bv 8)) (v0 : era_pins) :
    ukn_pay N' = (fun _ : Z => UkShFork.ushf_wq Wcu I) ->
    UShCatPay.sh_cat_slot T -∗ era_pin (fgn_echo gf) (S gen_id) v0 -∗
    □ (∀ W : UexecSlot.uvis,
         T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
         UexecRet.uslot (SG := uexecSG_xv6) W).
  Proof using Hkill.
    intros Hpeq. iIntros "(_ & _ & #Hgen) #Hpin0".
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint ug r s0 PT PD I 0%nat v0 with "Hpin0").
      iApply (uHktaint' ug Hkill with "Hk"). }
    iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
    iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W with "HT' Hmy Hkillq").
  Qed.

  Local Lemma uup_pin0 (I : list (bv 8)) :
    uWcl ug s0 I 3%nat -∗ uWcl ug s0 I 3%nat ∗ ∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0.
  Proof using .
    rewrite /uWcl /lk_lcred. iIntros "H". iDestruct "H" as (v0) "[#Hp H]".
    iSplitL "H"; [iExists v0; iFrame "Hp H" | iExists v0].
    cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp".
  Qed.

  (* THE ECHO PIPELINE'S CHILD: [echo ws | cat^n], the whole deed kept by
     node 0 *)
  Lemma upipes_child_law_echo :
    ⊢ UShEcho.sh_echo_slot T -∗ UShCatPay.sh_cat_slot T -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) Wcu pipes_lp (68 + UkSh.ush_Dpipe).
  Proof using Hcons Hkill Heq pipeProtoG0 pnsRegG0 uartGhostG0.
    iIntros "#Hes #Hcs".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len wsf gb sz ld nn I)
      "%Hpeq %Hs1 %Hlp %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcp Hrun".
    destruct Hlp as (ws & n & Hwsf & Hlat).
    pose proof Hlat as (Hok_u & Hlen & Hby).
    pose proof Hok_u as (Hok & Hn & _).
    pose proof (upls_cats_le (PrEcho ws) n Hok_u) as Hn16.
    assert (Hlws' : last_ws I = FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) n))
      by (rewrite -Hlws; exact Hwsf).
    pose proof (ul_pipe I (PrEcho ws) n Hfbk Hok_u Hlws') as Hul.
    pose proof (unlines_pos I (PrEcho ws) n Hok Hlws') as Hpos.
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hcst.
    destruct Hrows as (Hfd0c & Hfd1p & Hfd2p).
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen3.
    pose proof (UShPipesLaw.pls_fd_lowest_none ld Hlen3 Hfd0c Hfd1p Hfd2p) as Hnone.
    destruct Hfd0c as [wr0 Hl0]. destruct Hfd1p as [rb1 Hl1]. destruct Hfd2p as [rb2 Hl2].
    destruct n as [| n']; [lia |].
    (* ---- the line is the lexer's ---- *)
    assert (Hbat : bat gb 0 (FileDisc.line_bytes (FileDisc.LPipe (PrEcho ws) (S n')))).
    { intros j Hj. apply Hby. rewrite Hlen. exact Hj. }
    pose proof (ushq_lines_bars ws (replicate (S n') ushq_cat) gb 0%nat len
                  (lines_of_pipe ws (S n') gb len Hok Hn Hbat Hlen)) as Hbars.
    (* ---- THE PARSE ---- *)
    assert (E1 : (68 + UkSh.ush_Dpipe + (8 + (UkShDiag.ush_Dg + nn)))%nat
                 = (68 + (length (RT ws (S n')) * 6 + (96 + nn - 6 * S n')))%nat)
      by (rewrite rtoks_cats_length; unfold UkSh.ush_Dpipe, UkShDiag.ush_Dg; lia).
    iEval (rewrite E1) in "Hrun".
    iApply (wp_kshm_child_pipes_g (SG := uexecSG_xv6) (PS := uprogSG_free)
              (ghost_varG0 := offbox_offG) N'
              (ushq_um (ghost_varG0 := offbox_offG) N' sz) 340
              (ushq_um_chain (ghost_varG0 := offbox_offG) N' (SG := uexecSG_xv6)
                 (PS := uprogSG_free) (fun k H => H) sz ltac:(lia) Hszal Hszok)
              h m dw dv sa len gb (wl_toks ws) (RT ws (S n'))
              0%nat (96 + nn - 6 * S n')%nat (Wcu I 3%nat)
              Hbars ltac:(rewrite rtoks_cats_length; lia) Hs1 Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hstr Hws Hsy HM Hcp [] Hrun").
    { iIntros "!> H". rewrite Hpeq. rewrite /UkShFork.ushf_wq. iLeft. iExact "H". }
    iIntros (h' m' q) "%Ha0' #Hcmd _ _ HM3 Hcp Hrun".
    iPoseProof (uup_um_usz N' sz _ with "HM3") as "Hsz".
    (* ---- THE LEND AND THE DEED, opened (or the taint) ---- *)
    iDestruct (uWcu_3 ug r s0 PT PD I with "Hcp") as "Hcp".
    rewrite uWcf_S3. iDestruct "Hcp" as "[Hc Hpre]".
    iDestruct (uup_pin0 I with "Hc") as "[Hc Hpin0]". iDestruct "Hpin0" as (v0) "#Hpin0".
    iPoseProof (uup_genw N' I v0 Hpeq with "Hcs Hpin0") as "#Hgenw".
    iDestruct (uopen I with "Hc Hpre") as "[#HT | Hop]".
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
                N' T h' m' (mword_of_int ShSyms.runcmd) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hop" as (v cs s) "(%Htie & #Hpin & #Hlb & #Hcsl & #Hty & Hown & HPW)".
    iDestruct (udeed_typed s with "Hty") as %[Hsok _].
    pose proof (upv_line_pipe I (PrEcho ws) (S n') Hul) as HlR.
    assert (Hfc : fc_ok (pv_fc pview_unionU (dst_content s)))
      by exact (pview_union_fc_ok adm_u_f (dst_content s) Hsok).
    assert (Hadmit : pns_admV pview_unionU (LPipes (PrEcho ws) (S n'))) by reflexivity.
    assert (Hplok : pl_ok (LPipes (PrEcho ws) (S n'))) by exact (pl_ok_of_uline _ _ Hok_u).
    (* ---- THE ROUND'S ALLOCATION, at the deed's state ---- *)
    iApply uup_fupd_mwp.
    iMod (UShPipesLaw.pls_nodes_alloc (lcats (LPipes (PrEcho ws) (S n')))) as (P gF gG) "Hnodes".
    iMod (pipesV_alloc pg U pview_unionU CPU v I (dst_content s) (LPipes (PrEcho ws) (S n'))
            Hplok ⊤ pnsN (S gen_id) termw
            (tokN (pv_fc pview_unionU (dst_content s)) (LPipes (PrEcho ws) (S n')))
            (pdep U pview_unionU (dst_content s) (LPipes (PrEcho ws) (S n'))
               (wl_line (drop 1 ws)) (PrEcho ws) P gF gG)
            with "HPW") as (γc γm) "[#Hfam Hh]".
    iModIntro.
    (* ---- THE STAGES, at the parser's cut ---- *)
    pose proof (ustg_cats (PrEcho ws) (S n') len gb sa Hlat) as Hstc.
    pose proof (pcut_echo_bytes ws (S n') gb len Hlat) as Hbytes.
    iPoseProof (ush_cldep_nonpipe (SG := uexecSG_xv6) (PS := uprogSG_free)
                  (ghost_varG0 := offbox_offG)
                  (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
                  ltac:(intros rb wb gp Hq; discriminate Hq)) as "#Hcd0".
    assert (E2 : (68 + (length (RT ws (S n')) * 6 + (96 + nn - 6 * S n')))%nat
                 = (6 + (2 + (UkShDiag.ush_Dg
                    + (6 * length (REST ws n' len gb sa)
                       + (6 + (32 + (96 + nn - 6 * S n')))))))%nat)
      by (rewrite length_map !rtoks_cats_length; unfold UkShDiag.ush_Dg; lia).
    iEval (rewrite E2) in "Hrun".
    (* THE PRODUCER'S LAW: echo's, the loan [True] *)
    iPoseProof (plaw_echo (ghost_varG0 := offbox_offG) pg U pview_unionU CPU None WAU
                  (uwa_ext ug) Hcons Hkill usup v I (dst_content s) (LPipes (PrEcho ws) (S n'))
                  HlR Hfc Hadmit Hplok (wl_line (drop 1 ws))
                  (UkPipesEntries.pe_line_len ws Hok) (PrEcho ws) True%I γc γm P gF gG
                  eq_refl eq_refl sa (pcut ws (S n') len gb) ws eq_refl Hok Hbytes
                  with "Hfam Hes") as "#Hpl".
    iApply (wp_pipes_round_alloc (ghost_varG0 := offbox_offG) pg U pview_unionU CPU None WAU
              (uwa_ext ug) Hcons Hkill usup v I (dst_content s) (LPipes (PrEcho ws) (S n'))
              HlR Hfc Hadmit Hplok (wl_line (drop 1 ws))
              (UkPipesEntries.pe_line_len ws Hok) (PrEcho ws) True%I γc γm P gF gG
              (UkShFork.ushf_wq Wcu I)
              (era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I ∗ DPRE I)%I
              (ufin v I (dst_content s) (LPipes (PrEcho ws) (S n')) (wl_line (drop 1 ws))
                 (PrEcho ws) True%I (DPRE I) P gF gG γc γm HlR eq_refl Hplok Hpos
                 ltac:(iIntros "[$ _]"))
              eq_refl eq_refl sa (pcut ws (S n') len gb)
              (STG ws (S n') len gb sa) (ustg_len ws (S n') len gb sa)
              (UkShMain.ush_args sa (pcut ws (S n') len gb) (wl_toks ws)) eq_refl Hstc
              ld rb1 rb2 Hl1 Hl2 Hnone
              (REST ws n' len gb sa)
              (UkShMain.ush_args sa (pcut ws (S n') len gb) (wl_toks ws))
              (UkShMain.ush_args sa (pcut ws (S n') len gb)
                 [(pc0 ws, pc0 ws + length ushq_cat)%nat])
              N' h' m' q (sz + 65536) (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
              (32 + (96 + nn - 6 * S n'))%nat
              eq_refl Hpeq Ha0' Hl0 ltac:(discriminate)
              with "Hfam Hpl Hcs Hh Hnodes [Hown] [//] Hpid Hcode Hjt Hcmd Hsz Hstd Hcd0
                    Hcwd Hch Hrun").
    iSplitR; [iExact "Hpin" |]. iSplitR; [iExact "Hlb" |].
    rewrite /ush_deed_at. iLeft. iExists cs, s, v.
    iFrame "Hown Hty Hpin Hcsl". by iPureIntro.
  Qed.

  Local Notation PWC := (prod_words (PrCatF fname_f)).

  (* THE [cat f] PIPELINE'S CHILD: [cat f | cat^n], node 0 LENDING the
     deed's half to the producer and keeping the ticket *)
  Lemma upipes_child_law_catf :
    ⊢ UShEcho.sh_echo_slot T -∗ UShCatPay.sh_cat_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) Wcu pipes_lpc (68 + UkSh.ush_Dpipe).
  Proof using Hcons Hkill Heq cifRegG0 pipeProtoG0 pnsRegG0 uartGhostG0.
    iIntros "#Hes #Hcs #Hmade".
    iPoseProof "Hcs" as "(#Hinv & _ & _)".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len wsf gb sz ld nn I)
      "%Hpeq %Hs1 %Hlp %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcp Hrun".
    destruct Hlp as (n & Hwsf & Hlat).
    pose proof Hlat as (Hok_u & Hlen & Hby).
    pose proof Hok_u as (Hok & Hn & _).
    pose proof (upls_cats_le (PrCatF fname_f) n Hok_u) as Hn16.
    assert (Hlws' : last_ws I = FileDisc.uline_ws (FileDisc.LPipe (PrCatF fname_f) n))
      by (rewrite -Hlws; exact Hwsf).
    pose proof (ul_pipe I (PrCatF fname_f) n Hfbk Hok_u Hlws') as Hul.
    pose proof (unlines_pos I (PrCatF fname_f) n Hok Hlws') as Hpos.
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hcst.
    destruct Hrows as (Hfd0c & Hfd1p & Hfd2p).
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen3.
    pose proof (UShPipesLaw.pls_fd_lowest_none ld Hlen3 Hfd0c Hfd1p Hfd2p) as Hnone.
    destruct Hfd0c as [wr0 Hl0]. destruct Hfd1p as [rb1 Hl1]. destruct Hfd2p as [rb2 Hl2].
    destruct n as [| n']; [lia |].
    (* ---- the line is the lexer's ---- *)
    assert (Hbat : bat gb 0 (FileDisc.line_bytes (FileDisc.LPipe (PrCatF fname_f) (S n')))).
    { intros j Hj. apply Hby. rewrite Hlen. exact Hj. }
    pose proof (ushq_lines_bars PWC (replicate (S n') ushq_cat) gb 0%nat len
                  (lines_of_pipe_p (PrCatF fname_f) (S n') gb len Hok Hn Hbat Hlen)) as Hbars.
    (* ---- THE PARSE ---- *)
    assert (E1 : (68 + UkSh.ush_Dpipe + (8 + (UkShDiag.ush_Dg + nn)))%nat
                 = (68 + (length (RT PWC (S n')) * 6 + (96 + nn - 6 * S n')))%nat)
      by (rewrite rtoks_cats_length; unfold UkSh.ush_Dpipe, UkShDiag.ush_Dg; lia).
    iEval (rewrite E1) in "Hrun".
    iApply (wp_kshm_child_pipes_g (SG := uexecSG_xv6) (PS := uprogSG_free)
              (ghost_varG0 := offbox_offG) N'
              (ushq_um (ghost_varG0 := offbox_offG) N' sz) 340
              (ushq_um_chain (ghost_varG0 := offbox_offG) N' (SG := uexecSG_xv6)
                 (PS := uprogSG_free) (fun k H => H) sz ltac:(lia) Hszal Hszok)
              h m dw dv sa len gb (wl_toks PWC) (RT PWC (S n'))
              0%nat (96 + nn - 6 * S n')%nat (Wcu I 3%nat)
              Hbars ltac:(rewrite rtoks_cats_length; lia) Hs1 Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hstr Hws Hsy HM Hcp [] Hrun").
    { iIntros "!> H". rewrite Hpeq. rewrite /UkShFork.ushf_wq. iLeft. iExact "H". }
    iIntros (h' m' q) "%Ha0' #Hcmd _ _ HM3 Hcp Hrun".
    iPoseProof (uup_um_usz N' sz _ with "HM3") as "Hsz".
    (* ---- THE LEND AND THE DEED, opened (or the taint) ---- *)
    iDestruct (uWcu_3 ug r s0 PT PD I with "Hcp") as "Hcp".
    rewrite uWcf_S3. iDestruct "Hcp" as "[Hc Hpre]".
    iDestruct (uup_pin0 I with "Hc") as "[Hc Hpin0]". iDestruct "Hpin0" as (v0) "#Hpin0".
    iPoseProof (uup_genw N' I v0 Hpeq with "Hcs Hpin0") as "#Hgenw".
    iDestruct (uopen I with "Hc Hpre") as "[#HT | Hop]".
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
                N' T h' m' (mword_of_int ShSyms.runcmd) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hop" as (v cs s) "(%Htie & #Hpin & #Hlb & #Hcsl & #Hty & Hown & HPW)".
    iDestruct (udeed_typed s with "Hty") as %[Hsok Hshort].
    (* THE DEED, split: node 0 keeps the ticket, the producer borrows the
       deed's half *)
    rewrite /fown. iDestruct "Hown" as "[Hdq Htk]".
    assert (Hdeed : (ftkt r s ∗ f_typed (fgn_cl gf) s ∗ era_pin (fgn_echo gf) (S gen_id) v
                     ∗ cs_lb v cs) ∗ fdq r (1/2)%Qp s ⊢ DPRE I).
    { iIntros "[(Htk & #Hty' & #Hpin' & #Hcs') Hdq]". rewrite /ush_deed_at. iLeft.
      iExists cs, s, v. rewrite /fown /fdeed /FileOpen.fdq.
      iFrame "Hdq Htk Hty' Hpin' Hcs'". by iPureIntro. }
    pose proof (upv_line_pipe I (PrCatF fname_f) (S n') Hul) as HlR.
    assert (Hfc : fc_ok (pv_fc pview_unionU (dst_content s)))
      by exact (pview_union_fc_ok adm_u_f (dst_content s) Hsok).
    assert (Hadmit : pns_admV pview_unionU (LPipes (PrCatF fname_f) (S n'))).
    { rewrite /pns_admV. cbn [pv_adm pview_unionU pview_union adm_u_f].
      by apply bool_decide_eq_true_2. }
    assert (Hplok : pl_ok (LPipes (PrCatF fname_f) (S n'))) by exact (pl_ok_of_uline _ _ Hok_u).
    pose proof (catf_short (dst_content s) Hshort) as HL31.
    (* ---- THE ROUND'S ALLOCATION, at the deed's state ---- *)
    iApply uup_fupd_mwp.
    iMod (UShPipesLaw.pls_nodes_alloc (lcats (LPipes (PrCatF fname_f) (S n')))) as (P gF gG) "Hnodes".
    iMod (pipesV_alloc pg U pview_unionU CPU v I (dst_content s) (LPipes (PrCatF fname_f) (S n'))
            Hplok ⊤ pnsN (S gen_id) termw
            (tokN (pv_fc pview_unionU (dst_content s)) (LPipes (PrCatF fname_f) (S n')))
            (pdep U pview_unionU (dst_content s) (LPipes (PrCatF fname_f) (S n'))
               (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f))
               (PrCatF fname_f) P gF gG)
            with "HPW") as (γc γm) "[#Hfam Hh]".
    iModIntro.
    (* ---- THE STAGES, at the parser's cut ---- *)
    pose proof (ustg_cats (PrCatF fname_f) (S n') len gb sa Hlat) as Hstc.
    pose proof (pcut_echo_bytes_p (PrCatF fname_f) (S n') gb len Hlat) as Hbytes.
    iPoseProof (ush_cldep_nonpipe (SG := uexecSG_xv6) (PS := uprogSG_free)
                  (ghost_varG0 := offbox_offG)
                  (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
                  ltac:(intros rb wb gp Hq; discriminate Hq)) as "#Hcd0".
    assert (E2 : (68 + (length (RT PWC (S n')) * 6 + (96 + nn - 6 * S n')))%nat
                 = (6 + (2 + (UkShDiag.ush_Dg
                    + (6 * length (REST PWC n' len gb sa)
                       + (6 + (32 + (96 + nn - 6 * S n')))))))%nat)
      by (rewrite length_map !rtoks_cats_length; unfold UkShDiag.ush_Dg; lia).
    iEval (rewrite E2) in "Hrun".
    (* THE PRODUCER'S LAW: [cat f]'s, at the deed *)
    iPoseProof (stage_catf_law_holds (ghost_varG0 := offbox_offG) (fgn_cl gf) r Heq pg U
                  pview_unionU CPU None WAU (uwa_ext ug) Hcons Hkill usup v I (dst_content s)
                  (LPipes (PrCatF fname_f) (S n')) HlR Hfc Hadmit Hplok
                  (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f)) HL31
                  (PrCatF fname_f) γc γm P gF gG
                  (Hfire U pview_unionU I (dst_content s) (LPipes (PrCatF fname_f) (S n'))
                     HlR Hadmit Hplok
                     (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f))
                     (PrCatF fname_f) eq_refl eq_refl)
                  fname_f sa (pcut PWC (S n') len gb) (1/2)%Qp s (catf_ds s)
                  eq_refl eq_refl catf_ws_exec_ok Hbytes ltac:(cbn [lcats]; lia) (catf_case s)
                  with "Hfam Hcs [] [] Hinv Hmade") as "#Hpl".
    { iIntros "!> H". rewrite Hkill. iExact "H". }
    { iIntros "!> H". rewrite Hkill. iExact "H". }
    iApply (wp_pipes_round_alloc (ghost_varG0 := offbox_offG) pg U pview_unionU CPU None WAU
              (uwa_ext ug) Hcons Hkill usup v I (dst_content s) (LPipes (PrCatF fname_f) (S n'))
              HlR Hfc Hadmit Hplok
              (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f)) HL31
              (PrCatF fname_f) (fdq r (1/2)%Qp s) γc γm P gF gG
              (UkShFork.ushf_wq Wcu I)
              (era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I
               ∗ (ftkt r s ∗ f_typed (fgn_cl gf) s ∗ era_pin (fgn_echo gf) (S gen_id) v
                  ∗ cs_lb v cs))%I
              (ufin v I (dst_content s) (LPipes (PrCatF fname_f) (S n'))
                 (prod_content (pv_fc pview_unionU (dst_content s)) (PrCatF fname_f))
                 (PrCatF fname_f) (fdq r (1/2)%Qp s) _ P gF gG γc γm HlR
                 ltac:(cbn; by apply bool_decide_eq_true_2) Hplok Hpos Hdeed)
              eq_refl eq_refl sa (pcut PWC (S n') len gb)
              (STG PWC (S n') len gb sa) (ustg_len PWC (S n') len gb sa)
              (UkShMain.ush_args sa (pcut PWC (S n') len gb) (wl_toks PWC)) eq_refl Hstc
              ld rb1 rb2 Hl1 Hl2 Hnone
              (REST PWC n' len gb sa)
              (UkShMain.ush_args sa (pcut PWC (S n') len gb) (wl_toks PWC))
              (UkShMain.ush_args sa (pcut PWC (S n') len gb)
                 [(pc0 PWC, pc0 PWC + length ushq_cat)%nat])
              N' h' m' q (sz + 65536) (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
              (32 + (96 + nn - 6 * S n'))%nat
              eq_refl Hpeq Ha0' Hl0 ltac:(discriminate)
              with "Hfam Hpl Hcs Hh Hnodes [Htk] Hdq Hpid Hcode Hjt Hcmd Hsz Hstd Hcd0
                    Hcwd Hch Hrun").
    iSplitR; [iExact "Hpin" |]. iSplitR; [iExact "Hlb" |].
    iFrame "Htk Hty Hpin Hcsl".
  Qed.

  (* =================================================================== *)
  (*  S1d  THE BODY LAW AT THE PIPELINE LINES, AND THE ROUND              *)
  (* =================================================================== *)
  Context (γp : gname).
  Local Notation Pm := (UShLine.ush_mid_at (lk_rres FI) (fgn_echo gf) γp).

  (* the body walk at an admitted pipeline: echo's line begins with [e],
     [cat f]'s with [ca], and each forks its own child law *)
  Lemma ushq_body_law_upipes (N : uk_names Σ) `{Hp : !ukn_const N} (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) Wcu pipes_lp (68 + UkSh.ush_Dpipe) -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) Wcu pipes_lpc (68 + UkSh.ush_Dpipe) -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm ush_line_upipe sz.
  Proof using .
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hche #Hchc #Hplaw".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct Hd as (p & np & -> & Ha & Hplok).
    iDestruct (UkSh.ush_jtab_ro (ukn_t N) with "Hjt") as "#Hro".
    destruct p as [ws | g].
    - (* [echo ws | cat^n] -- the pipe era's body walk *)
      iApply (UkShPipeForkTwin.wp_kshm_body_pipe (PS := uprogSG_free)
                (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm
                (fun k0 H => H) pipes_lp (68 + UkSh.ush_Dpipe) h m f k len
                (FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) np)) sz l n
                ltac:(lia) pipes_lp0
                Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (pipes_lp_of_at ws np f k len Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb (uHwbl_u ug r s0 PT PD)
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hche Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp (ukn_t N) with "Hcode").
      + exact Hfd0.
    - (* [cat f | cat^n] -- the cat body walk at the pipeline's line *)
      cbn [adm_u_f] in Ha. apply bool_decide_eq_true_1 in Ha. subst g.
      destruct (pipes_lpc_bytes _ f k len (ex_intro _ np (conj eq_refl Hlat)))
        as (Hb0 & Hb1 & Hl2).
      iApply (UkShRedirBody.wp_kshm_body_ca_with (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm
                (UkShCatForkTwin.kshf_fork_law_pipe (PS := uprogSG_free) (SG := uexecSG_xv6)
                   (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k0 H => H))
                pipes_lpc (68 + UkSh.ush_Dpipe) h m f k len
                (FileDisc.uline_ws (FileDisc.LPipe (PrCatF fname_f) np)) sz l n
                ltac:(lia) Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (pipes_lpc_of_at np f k len Hlat) Hb0 Hb1 Hl2
                Hszlo Hszal Hszok Hpm1 Hpmwb (uHwbl_u ug r s0 PT PD)
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchc Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp (ukn_t N) with "Hcode").
      + exact Hfd0.
  Qed.

  (* THE PIPELINE BRANCH, DISCHARGED at a pay-constant name bundle *)
  Lemma ush_pipes_branch_holds (N : uk_names Σ) `{Hp : !ukn_const N} :
    ⊢ union_links ug -∗
      UShEcho.sh_echo_slot T -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v) -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      ush_pipes_branch ug r s0 PT PD γp N.
  Proof using Hcons Hkill Heq cifRegG0 pipeProtoG0 pnsRegG0.
    iIntros "#Hlk #Hslot #Hcat #Hpin #Hmade".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (ush_kill_law_u ug r s0 PT PD Hkill v with "Hp") as "#Hkl".
    iPoseProof (uHpanic ug r s0 PT PD with "Hlk") as "#Hplaw".
    iPoseProof (upipes_child_law_echo with "Hslot Hcat") as "#Hche".
    iPoseProof (upipes_child_law_catf with "Hslot Hcat Hmade") as "#Hchc".
    rewrite /ush_pipes_branch.
    iApply (ushq_body_law_upipes N (SpecKexec.kexec_sz ElfUser.sh_elf)
              UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
              with "Hkl Hche Hchc Hplaw").
  Qed.

  (* THE ROUND LAW WITH NO PREMISE: the command loop's body obligation at
     the union's families, at every line the union admits -- the file
     shapes and echo ([UShURound]), the pipelines at either producer
     (above), at the pipeline's own terminal and committed shapes *)
  Lemma sh_round_holds_union_closed (N : uk_names Σ) :
    ⊢ union_links ug -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v) -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkSh.ush_rest_l_at (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
        N γp T Wcu Wbu Pm ush_line_union
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using Hcons Hkill Heq HfifR cifRegG0 pipeProtoG0 pnsRegG0.
    iIntros "#Hlk #Hdep #Hslot #Hcat #Hpin #Hmade".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (ush_kill_law_u ug r s0 PT PD Hkill v with "Hp") as "#Hkl".
    iPoseProof (ush_child_law_union ug r Heq s0 Hcons Hkill PT PD
                  with "Hlk Hdep Hslot Hmade") as "#Hchl".
    iPoseProof (uHchild_redir ug r Heq s0 Hkill PT PD with "Hlk Hdep Hslot Hmade") as "#Hred".
    iPoseProof (uHchild_cat ug r Heq s0 Hcons Hkill PT PD with "Hlk Hdep Hcat Hmade") as "#Hcatl".
    iPoseProof (uHpanic ug r s0 PT PD with "Hlk") as "#Hplaw".
    iPoseProof (upipes_child_law_echo with "Hslot Hcat") as "#Hche".
    iPoseProof (upipes_child_law_catf with "Hslot Hcat Hmade") as "#Hchc".
    iIntros "!>" (l) "%Hc".
    iPoseProof (ushq_body_law_upipes N (Hp := Hc) (SpecKexec.kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  with "Hkl Hche Hchc Hplaw") as "#Hpipes".
    iPoseProof (ushq_body_law_union ug r s0 PT PD γp N (Hp := Hc)
                  (SpecKexec.kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  with "Hkl Hchl Hred Hcatl Hplaw Hpipes") as "#Hbody".
    iPoseProof (UkShPipeForkTwin.ushf_rest_of_body_at_pipe
                  (PS := uprogSG_free) (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
                  (Hpay := Hc) N γp T Wcu Wbu Pm (fun k H => H) ush_line_union
                  (SpecKexec.kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  (uHwbl_u ug r s0 PT PD) with "Hbody") as "Hb".
    rewrite /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [exact Hc | iExact "Hb'"].
  Qed.
End UShUPipes.
