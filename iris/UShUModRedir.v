(* ===================================================================== *)
(*  UShUModRedir.v -- THE [echo ws > f] LINE'S SHAPE MODULE (shape-       *)
(*  modules S1, step 3; design: claude-notes/design/shape-modules.md     *)
(*  sections 2 and 5).                                                    *)
(*                                                                        *)
(*  Everything the round needs of the [echo ws > f] line, in one file:    *)
(*  the redirect child's exits, exec supply and law at the union's        *)
(*  credential [uHchild_redir] (moved from [UShURound]'s S3, with its     *)
(*  local diagnostics [uab_redir_alts]), the module [mod_redir]           *)
(*  ([UkShShape.shape_mod]: the family [LEchoF _ _], the line predicate   *)
(*  [UkShRedirBody.ushs_lp], first byte 'e', room 68) and the body law at *)
(*  the redirect line [uredir_body_law], the generic                      *)
(*  [UkShShape.ushf_body_law_of_mod]'s instance after the child law's     *)
(*  bound-name form is converted ([UkShRedirBody.                         *)
(*  ushf_child_law_at_of_redir]).  The line predicate's two facts stay in *)
(*  [UkShRedirBody] ([ushs_lp0], [ushs_lp_of_at]).  The out-of-memory law *)
(*  with the deed opened is [UShURoundDefs.uoom_law_deed].                *)
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
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserChildren.
Require Import UexecRet.
Require Import ExecEntry.
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import FsImg.
Require Import FsEchoPin.
Require Import AppCfg.
Require Import AppFileCons.
Require Import UserPerm.
Require Import UserPtTree.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import UNameBytes.        (* the diagnostic windows *)
Require Import FileOut.
Require Import FileOpen.
Require Import FileWrite.
Require Import UEchoFile.
Require Import UkShRedirBody.
Require Import UkShRedirChild.
Require Import ExecWords.
Require Import UserOff.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UkFileOpen.
Require Import LinkRec.
Require Import FileLinksLine.
Require Import FileHooks.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UShPanic.
Require Import UShEcho.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UkUnionEntries.
Require Import UShURoundDefs.
Require UkFileIface.
Require UShFileRedir.
Require UShExecPin.
Require Import CtxIdDefs.
Require Import UShUModBase.       (* the pure preamble, shared with the shape modules *)
Require Import UkShShape.
Require Import UShUModCat.       (* the cat child's shared helpers: uoom_law_deed, urpos_of_halves, uexecfail_law_at_conv, ur_fupd_mwp *)
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ---- THE MODULE: the redirect line as the round sees it ---- *)
Lemma uredir_lp_at (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat) :
  (exists (ws : list (list (bv 8))) (nm : list (bv 8)), lu = LEchoF ws nm) ->
  UkSh.ush_line_at lu f k len ->
  UkShRedirBody.ushs_lp (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using . intros (ws & nm & ->) H. exact (UkShRedirBody.ushs_lp_of_at ws nm f k len H). Qed.

Lemma uredir_Dc_le : (68 <= 68 + UkSh.ush_Dpipe)%nat.
Proof using . lia. Qed.

Definition mod_redir : shape_mod :=
  {| sm_D := fun l => exists (ws : list (list (bv 8))) (nm : list (bv 8)), l = LEchoF ws nm;
     sm_Lp := UkShRedirBody.ushs_lp; sm_head := HeadE; sm_Dc := 68%nat;
     sm_Dc_le := uredir_Dc_le; sm_lp0 := UkShRedirBody.ushs_lp0; sm_lp_at := uredir_lp_at |}.

Section UShUModRedir.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER ([UShRound]'s header): the redirect child's
     pins name [Xv6Cameras.offbox_offG] *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl gf)) r).
  Context (s0 : fstate).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = ucl ug).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl gf)).
  (* the era credential at the union IS the era's wild token ([union_ifc]),
     and the reader-side one is the open premise (seccomp design 10.12) *)
  Context (Hwild : @riscv_wild Σ (@riscv_fixedGS Σ _) = usecc_tok ug).
  Context (Hrdw : ush_rdwild_of_shape ug).
  (* THE RECORD'S SYNC-HOOK FAMILY IS THE UNION'S (sync SY3-A4): the seam
     through which /sync's lend carries the hook sh mints *)
  Context (Hhk : @riscv_sync_hook Σ (@riscv_fixedGS Σ _) = union_hk file_pred (fgn_cl gf)).

  Local Notation T := (file_taint (fgn_cl gf)).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PA := (union_params_at ug s0).

  (* the pipeline's two shapes: parameters until C9f2 names them *)
  Context (PT : list (bv 8) -> nat -> iProp Σ) (PD : list (bv 8) -> iProp Σ).

  Local Notation Wcl := (uWcl ug s0).
  Local Notation Wcf := (uWcf ug r s0).
  Local Notation Wcu := (uWcu ug r s0 PT PD).
  Local Notation Wbu := (uWbf ug r s0).
  Local Notation PRE := (ush_pre_at ug r s0).
  Local Notation DONE := (ush_done_at ug r s0).

  #[local] Instance usr_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance usr_links_pers0 : Persistent (union_links ug) | 0
    := union_links_persistent ug.

  Local Notation uHktaint' := (UShURoundDefs.uHktaint ug Hkill).
  Local Notation uWcu_taint' := (UShURoundDefs.uWcu_taint ug r s0 PT PD).
  Local Notation uoom_law_deed := (UShUModCat.uoom_law_deed ug r s0 PT PD).
  Local Notation urpos_of_halves := (UShUModCat.urpos_of_halves ug r).
  Local Notation uexecfail_law_at_conv := (UShUModCat.uexecfail_law_at_conv).
  Local Notation ur_fupd_mwp := (UShUModCat.ur_fupd_mwp).

  (* =================================================================== *)
  (*  S3  THE REDIRECT CHILD                                              *)
  (* =================================================================== *)

  (* echo RAN: nothing on the console (fd 1 is [f]); the block is still
     owed whole and the deed is PEND at [RFRan sel] *)
  Lemma uredir_ran_exit (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (i : Z)
      (sel : list nat) (v' : era_pins) (cs : list nat) (sp : dst)
      (vf : file_era) (np : nat) :
    FileDisc.uname nm ->
    ul I = LEchoF ws nm -> upre_tie cs s0 I (dst_content sp) ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    (np <= length (fe_base vf) + nlines I)%nat ->
    Wcl I 3%nat -∗ fposq r np -∗ file_era_pin gf (S gen_id) vf -∗
    run_reg (fgn_cl gf) (S gen_id) (fn_pos r) (fn_deed r) -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    f_typed (fgn_cl gf) sp -∗
    FileWrite.file_wq (fgn_cl gf) r nm sp i ws sel
      (length (subseq (echo_chunks ws) sel)) -∗
    Wcf I 0%nat.
  Proof using .
    intros Hu Hul Htp Hlen Hpos Hnp. iIntros "Hc Hwq #Hvf #Hrr #Hpin #Hcs #Htyp Hq".
    rewrite /FileWrite.file_wq. iDestruct "Hq" as "[Hq | #HT]"; last first.
    { iApply (uWcf_taint ug r s0 I 0%nat v' with "Hpin HT"). }
    iDestruct "Hq" as (ls) "(Hd & _ & %Hok & %Hsel & #Hlb & %Hlst & Hposn)".
    pose proof (fl_redirs_last ls ws nm Hlst) as Hin.
    iPoseProof (urpos_of_halves I vf _ np Hnp with "Hvf Hposn Hwq Hrr") as "Hup".
    rewrite uWcf_0. iRight. iFrame "Hc".
    iSplitL; [| iRight; iLeft; iPureIntro; rewrite Hul; discriminate].
    rewrite /ush_pend_at /ush_deed_at. iLeft.
    iExists cs, (<[nm := (i, subseq (echo_chunks ws) sel)]> sp), v'.
    iFrame "Hd Hpin Hcs Hup". iSplit.
    - iPureIntro. exists (ualt_code (UR (RFRan sel))).
      rewrite /upend_tie_at ulm_term_R ulm_cont_R ulm_step_R Hul.
      split_and!; [exact Hlen | exact Hpos | | reflexivity | reflexivity |].
      2: { rewrite -(proj2 Htp). cbn [fsm]. rewrite dst_content_insert. reflexivity. }
      apply (ulm_ok_R _ (LEchoF ws nm) (RFRan sel) (uline_nopipe_echof ws nm)). exact Hsel.
    - iSplitL; [| iPureIntro; rewrite Hul; reflexivity].
      iApply (f_typed_some (fgn_cl gf) sp ls nm ws sel i
                Hu Hin Hok Hsel with "Htyp Hlb").
  Qed.

  (* the exec FAILED after the open truncated: the diagnostic is written,
     [f] is empty *)
  Lemma uredir_execfail_exit (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (i : Z)
      (v v' : era_pins) (cs : list nat) (sp : dst) :
    ul I = LEchoF ws nm -> upre_tie cs s0 I (dst_content sp) ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ualt_code (UR RFExec)) -∗
    fown r (<[nm := (i, [])]> sp) -∗ urpos ug r I -∗
    f_typed (fgn_cl gf) (<[nm := (i, [])]> sp) -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul Htp Hlen Hpos. iIntros "#Hp Hblk Hd Hup #Hty #Hpin' #Hcs".
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    assert (Hst : dst_content (<[nm := (i, [])]> sp)
                  = lm_step U (ust cs s0 I) (ul I) (lm_dec U (ualt_code (UR RFExec)))).
    { rewrite ulm_step_R Hul -(proj2 Htp). cbn [fsm].
      rewrite dst_content_insert. reflexivity. }
    iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RFExec)) v v' cs
              (<[nm := (i, [])]> sp)
              (ulm_apr_R I RFExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos Hst
              with "Hp Hblk Hd Hup Hty Hpin' Hcs").
  Qed.

  (* the open FAILED: [f] as the round found it ([RFOpenU]), or the create
     had fired and left it empty ([RFOpenM], at an absent [f] only) *)
  Lemma uredir_openfail_exit_u (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (s : dst)
      (v v' : era_pins) (cs : list nat) :
    ul I = LEchoF ws nm ->
    upre_tie cs s0 I (dst_content s) -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ualt_code (UR RFOpenU)) -∗
    fown r s -∗ urpos ug r I -∗ f_typed (fgn_cl gf) s -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul [Hlen Hc] Hpos. iIntros "#Hp Hblk Hd Hup #Hty #Hpin' #Hcs".
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RFOpenU)) v v' cs s
              (ulm_apr_R I RFOpenU Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos ltac:(rewrite ulm_step_R Hul; exact Hc)
              with "Hp Hblk Hd Hup Hty Hpin' Hcs").
  Qed.

  Lemma uredir_openfail_exit_m (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (i : Z)
      (v v' : era_pins) (cs : list nat) (sp : dst) :
    ul I = LEchoF ws nm ->
    upre_tie cs s0 I (dst_content sp) -> sp !! nm = None ->
    (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ualt_code (UR RFOpenM)) -∗
    fown r (<[nm := (i, [])]> sp) -∗ urpos ug r I -∗
    f_typed (fgn_cl gf) (<[nm := (i, [])]> sp) -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul [Hlen Hc] HsN Hpos. iIntros "#Hp Hblk Hd Hup #Hty #Hpin' #Hcs".
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    assert (HcN : dst_content sp !! nm = None)
      by (rewrite dst_content_lookup HsN; reflexivity).
    assert (Hst : dst_content (<[nm := (i, [])]> sp)
                  = lm_step U (ust cs s0 I) (ul I) (lm_dec U (ualt_code (UR RFOpenM)))).
    { rewrite ulm_step_R Hul -Hc. cbn [fsm].
      rewrite HcN dst_content_insert. reflexivity. }
    iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RFOpenM)) v v' cs
              (<[nm := (i, [])]> sp)
              (ulm_apr_R I RFOpenM Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos Hst
              with "Hp Hblk Hd Hup Hty Hpin' Hcs").
  Qed.

  (* THE REDIRECT CHILD'S EXEC SUPPLY: [exec /echo] with fd 1 on [f], at
     the union's redirect entry *)
  Lemma uredir_exec_sup (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (v' : era_pins)
      (cs : list nat) (ls : list fl_line) (sp : dst) (vf : file_era) :
    FileDisc.uname nm ->
    ul I = LEchoF ws nm -> upre_tie cs s0 I (dst_content sp) ->
    EchoDisc.line_ok ws -> stdpp.list_basics.list.last ls = Some (FileDisc.LEchoF ws nm) ->
    (length ls <= length (fe_base vf) + nlines I)%nat ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
      fl_lb (fgn_cl gf) ls -∗ f_typed (fgn_cl gf) sp -∗
      file_era_pin gf (S gen_id) vf -∗
      run_reg (fgn_cl gf) (S gen_id) (fn_pos r) (fn_deed r) -∗
      ∀ ty : fdtype,
        UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
          (ghost_varG0 := offbox_offG)
          (UkShRedirBody.ushs_fd1f ty) ws
          (fun _ : Z => UkShFork.ushf_wq Wcu I)
          ((Wcl I 3%nat ∗ fposq r (length ls))
           ∗ UShFileRedir.redir_K' gf r nm sp (length ls) ty).
  Proof using Heq Hkill HfifR.
    intros Hu Hul Htp Hokws Hlst Hnp Hlen Hpos.
    iIntros "#Hdep #Hslot #Hpin' #Hcs #Hlb #Htyp #Hvf #Hrr" (ty).
    iPoseProof "Hslot" as "(#Hinv & #Hcl & #Hgen)".
    assert (Hhead : ws !!! 0%nat = UShEcho.echo_pl).
    { rewrite (list_lookup_total_correct ws 0%nat EchoDisc.cmd_echo
                 (EchoDisc.line_ok_head ws Hokws)).
      vm_compute. reflexivity. }
    pose proof (ExecWords.line_ok_exec_ok ws Hokws) as Hxok.
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkt".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v' with "Hpin'"). iApply uHktaint'.
      iExact "Hk". }
    iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all
               (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
    { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp Hkt"). }
    iApply (UShExecPin.sh_exec_sup_x_of_entry (ghost_varG0 := offbox_offG)
              (UkShRedirBody.ushs_fd1f ty) ws UShEcho.echo_pl FsEchoPin.era0_echo_pins
              [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO ElfUser.echo_elf T
              (UkShFork.ushf_wq Wcu I)
              ((Wcl I 3%nat ∗ fposq r (length ls))
               ∗ UShFileRedir.redir_K' gf r nm sp (length ls) ty)%I
              Hxok Hhead UShEcho.echo_elf_loadable UShEcho.sh_echo_pin_resolves
              with "[] Hkt [Hslot]");
      [| iApply (UShExecPin.sh_pin_slot_echo with "Hslot")].
    iIntros "!>" (M sa t gb fdv chs pidv) "%Himg %Hbytes %Hflen %Hrows #Hnp0".
    rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hscw %Hch0 %Hpid0 %Hargs Hmp
                               (Hc & HK & Hino)".
    (* a tainted receipt buys the generic slot *)
    iDestruct "Hino" as "[Hino | #HT]"; last first.
    { iApply ("Hgen'" $! (UexecSlot.uvis_fd W') W' with "HT [//] [%] Hmp"); exact Hscw. }
    iDestruct "Hino" as (i γo) "(%Hty & %Hi)".
    destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6 & Hi7).
    rewrite /UShFileRedir.redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
    iDestruct "HK" as "[HK | #HT]"; last first.
    { iApply ("Hgen'" $! (UexecSlot.uvis_fd W') W' with "HT [//] [%] Hmp"); exact Hscw. }
    iDestruct "HK" as (i1 γo1) "(%Hty1 & Hd & Hposn & Hpub)".
    rewrite Hty in Hty1. injection Hty1 as <- <-.
    iDestruct (UserOff.foff_pub_of_held with "Hpub") as "Hu".
    assert (Hl1 : take NSTD fdv !! 1%nat = Some (FdOpen false true (FdInode i γo OffHeld))).
    { rewrite -Hty. exact Hrows. }
    (* the entry, at what is left of the lend *)
    iPoseProof (uefile_image_entry (PS := uprogSG_free)
                  ug s0 nm ws M sa t gb fdv FsImg.ROOTINO chs pidv
                  r sp (Wcl I 3%nat ∗ fposq r (length ls))%I
                  i γo false
                  (fun _ : Z => UkShFork.ushf_wq Wcu I)
                  (fun _ _ => eq_refl) Heq Hokws Himg Hbytes Hflen
                  eq_refl Hl1 Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hi7
                  with "[] [] [] [] Hinv Hnp0 Hdep") as "#He".
    { (* echo RAN: the exit pays the round's payload *)
      iIntros "!> [Hc Hex]". iDestruct "Hex" as (sel) "Hcur".
      rewrite /UkShFork.ushf_wq.
      rewrite /UEchoFile.efq /FileWrite.file_cur.
      iDestruct "Hcur" as "[[Hq _] | [#HT _]]".
      - iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iDestruct "Hc" as "[Hc Hwq]".
        iApply (uredir_ran_exit I ws nm i sel v' cs sp vf (length ls) Hu Hul Htp Hlen
                  Hpos Hnp with "Hc Hwq Hvf Hrr Hpin' Hcs Htyp Hq").
      - iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp
                                          [Hc Hd Hposn Hu]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hscw | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /UEchoFile.ef_pay /UEchoFile.efq. iFrame "Hc".
    iApply (FileWrite.file_cur_fired (fgn_cl gf) r nm sp i ws [] γo
              with "[Hd Hposn] Hu").
    rewrite /FileWrite.file_wq. iLeft. iExists ls. iFrame "Hd Hlb Hposn".
    iPureIntro. split_and!;
      [ reflexivity | exact Hokws | exact (sel_ok_nil _) | exact Hlst ].
  Qed.

  Local Lemma uexecfail_law_at_wand (dg : list (bv 8)) (n : nat)
      (Cr Cd Cd' : iProp Σ) :
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr Cd -∗
    □ (Cd -∗ Cd') -∗
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr Cd'.
  Proof using .
    iIntros "#Hl #Hw". rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hl" $! N l with "[%] Hc") as (Pf) "(H0 & #Hs & #He)";
      [exact Hfd |].
    iExists Pf. iFrame "H0 Hs". iIntros "!> Hp". iApply "Hw". iApply "He".
    iExact "Hp".
  Qed.

  (* the redirect line's three diagnostics, at the union's codes *)
  Local Lemma uab_redir_alts (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) :
    ul I = LEchoF ws nm ->
    lk_ab FI I (ualt_code (UR RFExec)) = alt_execfail
    /\ lk_ab FI I (ualt_code (UR RFOpenU)) = alt_openfailN nm
    /\ lk_ab FI I (ualt_code (UR RFOpenM)) = alt_openfailN nm.
  Proof using .
    intro Hul.
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    change (lk_ab FI I) with (lm_ab U K I).
    split_and!;
      (rewrite ulm_ab_R; [rewrite Hul; reflexivity | exact Hnp
                         | rewrite Hul; exact Logic.I | reflexivity]).
  Qed.

  (* ---- THE REDIRECT CHILD'S LAW ---- *)
  Lemma uHchild_redir :
    ⊢ union_links ug -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShRedirBody.sh_redir_child_law (PS := uprogSG_free)
        (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) T Wcu.
  Proof using Heq Hkill HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShRedirBody.sh_redir_child_law.
    iIntros "!>" (N' h m dw dv sa len ws file fb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch Hpid HM Hcr
       Hrun".
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch". iClear "Hpid".
    iDestruct (UkSh.ush_std_ustd with "Hstd") as "Hstd".
    pose proof (proj1 Hline) as Hokws.
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [| lia]. exfalso.
      rewrite /last_ws in Hlws. rewrite /nlines in Hn.
      apply nil_length_inv in Hn. rewrite Hn in Hlws. cbn in Hlws.
      destruct ws; discriminate Hlws. }
    assert (Hlb : last_ws I = wl_words (UkSh.ush_lastbody I)).
    { rewrite (last_ws_lastbody I). reflexivity. }
    destruct (FileDisc.fline_ok_redir_words (UkSh.ush_lastbody I) ws file
                Hfok Hokws ltac:(rewrite -Hlb; symmetry; exact Hlws))
      as [Hfl Hfile].
    assert (Hul : ul I = LEchoF ws file).
    { rewrite ul_lastbody. apply uline_of_u_eq; [exact Hfl | discriminate]. }
    change (uline_of (UkSh.ush_lastbody I)) with (fline I) in Hfl.
    destruct (uab_redir_alts I ws file Hul) as (Hax & Hau & Ham).
    (* ---- the lend, opened ---- *)
    iDestruct (uWcu_3_nw ug r s0 PT PD I ltac:(rewrite Hul; reflexivity) with "Hcr")
      as "Hcr".
    rewrite uWcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /uWcl /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v0 with "Hpin0"). iApply uHktaint'.
      iExact "Hk". }
    iAssert (□ (∀ W : UexecSlot.uvis,
                  T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
                  UexecRet.uslot (SG := uexecSG_xv6) W))%I
      as "#Hgenw".
    { iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W with "HT' Hmy Hkillq"). }
    rewrite {1}/ush_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs & %Hnw & Hup)".
    pose proof Htie as [Hlen Hcon].
    rewrite /uline_wit. iDestruct "Hwit" as "[Hwit | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    (* ---- THE LINE'S WITNESS (sync SY3-A3bc): the era's base and the
       input's lines, ending at this round's line ---- *)
    rewrite /FileLinksLine.flw. iDestruct "Hwit" as (vf) "[#Hvf #Hfl]".
    set (ls := (fe_base vf ++ UnionAdm.ulines_in I)%list).
    assert (Hlst : stdpp.list_basics.list.last ls = Some (FileDisc.LEchoF ws file)).
    { rewrite /ls last_app (ulines_in_last I Hpos) Hul. reflexivity. }
    pose proof (fl_redirs_last ls ws file Hlst) as Hin.
    assert (Hnp : (length ls <= length (fe_base vf) + nlines I)%nat).
    { rewrite /ls length_app UnionAdm.ulines_in_length. lia. }
    (* ---- THE ROUND POSITION, advanced to the line's count ---- *)
    iDestruct "Hup" as (vf0 n0) "(#Hvf0 & Hposh & %Hn0 & #Hrr)".
    iDestruct (file_era_pin_agree with "Hvf0 Hvf") as %->.
    iApply ur_fupd_mwp.
    iMod (file_pos_advance _ (fgn_cl gf) r n0 (length ls) ⊤ ltac:(solve_ndisj)
            Heq ltac:(rewrite /ls length_app UnionAdm.ulines_in_length; lia)
            with "Hinv Hposh") as "[Hposh | #HT]"; last first.
    { iModIntro.
      iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iModIntro. iDestruct "Hposh" as "[Hposn Hwq]".
    iAssert (∀ i : Z, f_typed (fgn_cl gf) (<[file := (i, [])]> s))%I
      as "#Hty0".
    { iIntros (i). rewrite -(subseq_nil (echo_chunks ws)).
      iApply (f_typed_some (fgn_cl gf) s ls file ws [] i
                Hfile Hin Hokws (sel_ok_nil _) with "Hty Hfl"). }
    (* ---- the fd rows ---- *)
    destruct Hrows as ([wr0 Hr0] & [rb1 Hr1] & Hfd2).
    (* ---- THE WALK ---- *)
    iApply (UkShRedirChild.wp_kshm_child_file_redir (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) (A := unit) N'
              (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len ws file fb sz ld
              _ n
              (fun _ : Z => UkShFork.ushf_wq Wcu I)
              (UShFileRedir.redir_K gf r file s (length ls))
              (UShFileRedir.redir_K' gf r file s (length ls))
              (fun _ => fown r s ∗ fpos r (length ls))%I
              (fun _ => UShFileRedir.redir_Kf gf r file s (length ls)) tt
              (Wcl I 3%nat ∗ (fown r s ∗ fposh r (length ls)))%I
              (Wcl I 3%nat ∗ fposq r (length ls))%I
              (Wcu I 0%nat) (Wcu I 0%nat)
              Hpeq Hs1 Hline Hfile Hsa Hs64 Hs38 Hszlo Hszal
              Hszok Hr1 ltac:(discriminate)
              ltac:(intros ? ? ?; discriminate) Hfd2
              ltac:(destruct ld as [| y0 [| y1 l2]];
                    [ discriminate Hr0 | discriminate Hr1 | ];
                    cbn in Hr0; injection Hr0 as ->; reflexivity)
              with "Hcode Hjt Hpcode Hpro Hstr Hwsp Hsy Hstd Hcwd Hch HM
                    [] [] [] [] [] [] [] [] [] [Hc Hd Hposn Hwq] Hrun").
    - (* the open *)
      iApply (UShFileRedir.Hopen_hand gf r Heq N' _ _ s (length ls) ls ws jo file Hfile
                Hlst eq_refl Hokws with "Hinv Hmade Hfl").
    - (* the receipt, read *)
      iIntros "!>" (ty) "HK".
      iMod (UShFileRedir.redir_K_inum gf r Heq file s (length ls) ty ⊤ ltac:(set_solver)
              with "Hinv HK") as "[HK Hi]".
      iModIntro. rewrite /UShFileRedir.redir_K'. iFrame "HK Hi".
    - (* exec /echo at the file *)
      iApply (uredir_exec_sup I ws file v' cs ls s vf Hfile Hul Htie Hokws Hlst Hnp Hlen Hpos
                with "Hdep Hslot Hpin' Hcs Hfl Hty Hvf Hrr").
    - (* exec failed *)
      iIntros (ty).
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG) FI
                    (fposq r (length ls) ∗ UShFileRedir.redir_K' gf r file s (length ls) ty)
                    I (ualt_code (UR RFExec)) with "[] [] []") as "#Hx".
      { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
      { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
      { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
      iEval (rewrite Hax) in "Hx".
      iApply (uexecfail_law_at_conv with "Hx []").
      { iIntros "!> [[Hc Hq] HK]". iFrame "Hc Hq HK". }
      iIntros "!> H". iDestruct "H" as (v) "(#Hp & Hblk & Hwq & [HK _])".
      rewrite /UShFileRedir.redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
      iDestruct "HK" as "[HK | #HT]"; last first.
      { iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
      iDestruct "HK" as (i γo) "(_ & Hd & Hposn & _)".
      iPoseProof (urpos_of_halves I vf _ (length ls) Hnp with "Hvf Hposn Hwq Hrr") as "Hup".
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iApply (uredir_execfail_exit I ws file i v v' cs s Hul Htie Hlen Hpos
                with "Hp Hblk Hd Hup Hty0 Hpin' Hcs").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iExact "H".
    - (* open failed *)
      rewrite /UkShDiag.ush_execfail_law_at.
      iIntros "!>" (N l) "%Hfd [HK [Hc Hwq]]".
      iAssert (union_links ug -∗ lk_links FI)%I as "Hlkw".
      { cbn [lk_links union_link_inst_at gen_link_inst]. iIntros "$". }
      iDestruct ("Hlkw" with "Hlk") as "#Hlk'".
      rewrite /UShFileRedir.redir_Kf.
      iDestruct "HK" as "[[Hd Hposn] | [[%HsN Hd] | #HT]]".
      + iPoseProof (urpos_of_halves I vf _ (length ls) Hnp with "Hvf Hposn Hwq Hrr") as "Hup".
        iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r s ∗ urpos ug r I) I (ualt_code (UR RFOpenU))
                      with "[] [] Hlk'") as "#Hx".
        { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
        { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
        iEval (rewrite Hau alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd Hup]") as (Pf) "(H0 & #Hs & #He)";
          [exact Hfd | iFrame "Hc Hd Hup" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd & Hup)".
        iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iApply (uredir_openfail_exit_u I ws file s v v' cs Hul Htie Hpos
                  with "Hp' Hblk Hd Hup Hty Hpin' Hcs").
      + iDestruct "Hd" as (i) "[Hd Hposn]".
        iPoseProof (urpos_of_halves I vf _ (length ls) Hnp with "Hvf Hposn Hwq Hrr") as "Hup".
        iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r (<[file := (i, [])]> s) ∗ urpos ug r I) I
                      (ualt_code (UR RFOpenM))
                      with "[] [] Hlk'") as "#Hx".
        { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
        { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
        iEval (rewrite Ham alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd Hup]") as (Pf) "(H0 & #Hs & #He)";
          [exact Hfd | iFrame "Hc Hd Hup" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd & Hup)".
        iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iApply (uredir_openfail_exit_m I ws file i v v' cs s Hul Htie HsN Hpos
                  with "Hp' Hblk Hd Hup Hty0 Hpin' Hcs").
      + iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI emp%I I (ualt_code (UR RFOpenU)) with "[] [] Hlk'") as "#Hx".
        { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
        { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
        iEval (rewrite Hau alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hs & _)";
          [exact Hfd | iFrame "Hc" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> _".
        iApply (uWcu_taint' I 0%nat v' with "Hpin' HT").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iExact "H".
    - (* the parse ran out of memory: "out of memory", the deed as found
         (the parse precedes the open) *)
      pose proof (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl)) as Hcst.
      iApply (UkShEcho.ushp_oom_of_diag (PS := uprogSG_free)
                (ghost_varG0 := offbox_offG) N'
                (Wcl I 3%nat ∗ (fown r s ∗ fposh r (length ls))) (Wcu I 0%nat) ld
                (4 + (UkShDiag.ush_Dg + n) - 2)%nat ltac:(unfold UkShDiag.ush_Dg; lia)
                Hfd2 with "[] [] Hcode []").
      + iApply (uoom_law_deed I cs s v' (fposh r (length ls))
                  ltac:(rewrite Hul; reflexivity) Htie Hpos with "Hlk Hty Hpin' Hcs []").
        iIntros "!> Hposh". iExists vf, (length ls). iFrame "Hvf Hposh Hrr".
        iPureIntro. exact Hnp.
      + iIntros "!> H". rewrite Hpeq /UkShFork.ushf_wq. iExact "H".
      + iApply (UkSh.ush_jtab_ro with "Hjt").
    - iIntros "(Hc & Hd & Hposn & Hwq)". iFrame "Hc Hd Hposn Hwq".
    - iFrame "Hc Hd Hposn Hwq".
  Qed.

  (* THE BODY LAW at the redirect line, from its child law (the file name
     bound outside, converted to the line-predicate form): the generic
     wrapper's instance *)
  Lemma uredir_body_law (N : uk_names Σ) `{Hp : !ukn_const N} (γp : gname)
      (Pm : list (bv 8) -> iProp Σ) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShRedirBody.sh_redir_child_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) T Wcu -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (sm_D mod_redir) sz.
  Proof using .
    intros Hszlo Hszal Hszok. iIntros "#Hkl #Hred #Hplaw".
    iPoseProof (UkShRedirBody.ushf_child_law_at_of_redir (PS := uprogSG_free)
                  (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) T Wcu
                  with "Hred") as "#Hchl".
    iApply (UkShShape.ushf_body_law_of_mod (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k H => H)
              mod_redir sz Hszlo Hszal Hszok with "Hkl [] Hplaw").
    rewrite /UkShShape.sm_law. cbn [sm_Lp sm_Dc mod_redir]. iExact "Hchl".
  Qed.

End UShUModRedir.
