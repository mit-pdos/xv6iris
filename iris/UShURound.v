(* ===================================================================== *)
(*  UShURound.v -- SH'S ROUND AT THE UNION, AT THE FILE-APPLICATION LINE  *)
(*  SHAPES (cut C9f1; design: claude-notes/design/union.md section 3,     *)
(*  'The credential the main loop carries' and 'Dispatch', review S6,     *)
(*  seam (d)).                                                            *)
(*                                                                        *)
(*  [UShRound]'s children and round at the union claim [UnionOut.ucl],    *)
(*  the record at the round's boot state ([UnionLinkInstAt]) and the      *)
(*  widened credential [UShURoundDefs.uWcu]:                              *)
(*    - [echo ws]: the file's TREE-ROUTE supply ([UShRound.               *)
(*      echo_exec_sup_file]'s body, NOT [UShEchoPay]) at the union's       *)
(*      console entry [UkUnionEntries.uecho_cons_image_entry];            *)
(*    - [echo ws > f]: [UShRound.redir_exec_sup]'s body at               *)
(*      [UkUnionEntries.uefile_image_entry], the open, its receipt and    *)
(*      the diagnostics at the union's codes;                             *)
(*    - [cat f]: [UShRound.cat_exec_sup]'s body at                        *)
(*      [UkUnionEntries.ucat_image_entry] -- the exit folds at the post   *)
(*      the drained console names, no [UCatOut.cch] detour.               *)
(*  The DISPATCH goes through [UkShPipeForkTwin] (the widened credential  *)
(*  is not timeless): [echo] by [ushf_body_law_echo_pipe], [echo > f] by  *)
(*  [wp_kshm_body_pipe] at [UkShRedirBody.ushs_lp], [cat f] by the cat    *)
(*  body twin [UkShCatForkTwin.ushf_body_law_cat_pipe].                    *)
(*                                                                        *)
(*  THE PIPELINE LINES are [ush_pipes_branch] (the body law at them),     *)
(*  discharged in [UShUPipes] (C9f2), whose [sh_round_holds_union_closed] *)
(*  is the round law: [ushq_body_law_union] below at the pipeline branch. *)
(*  Nothing switches the application.                                     *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserChildren.
Require Import UmodeAbi.
Require Import ProcGeom.
Require Import UexecRet.
Require Import ExecEntry.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import WpUart.
Require Import FsCfg.
Require Import FsImg.
Require Import FsImgCheck.
Require Import FsEchoPin.
Require Import FsCatPin.
Require Import FsGrepPin.
Require Import FsInitPin FsShPin.
Require Import AppCfg.
Require Import AppInv.
Require Import AppFileCons.
Require Import FileOutPure.
Require Import SysOpenDefs.
Require Import UkRunLeaf.
Require Import UserPerm.
Require Import UserPtTree.
Require SpecKexec.
Require Import UShLine.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require UNamePath.                (* the path/argv facts off the class laws *)
Require Import UNameBytes.        (* [uname_word], the diagnostic windows *)
Require Import FileOut.
Require Import FileOpen.
Require Import FileWrite.
Require Import UEchoFile.
Require Import FsAbsDefs.
Require Import ExecRun.
Require Import UkShRedirBody.
Require Import UkShRedirChild.
Require Import ExecWords.
Require Import UkShDiagAt.
Require Import UShCat.
Require Import UShCatPay.
Require Import UserOff.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShLoop.
Require Import UCodeShK.
Require Import UkShRedirAns.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UkFileOpen.
Require Import LinkRec.
Require Import FileLinksLine.
Require Import FileLinkGen.
Require Import FileHooks.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UShPanic.
Require Import UShEcho.
Require Import UShKernel.
Require Import UInitSh.
Require Import UkShPipeForkTwin.
Require Import UkShCatForkTwin.
Require Import UkConsOut.
Require Import PipeOut.
Require Import PipesDisc.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import UnionLinkInstAt.
Require Import UkUnionEntries.
Require Import UShURoundDefs.
Require UkFileIface.
Require UkFileEntries.
Require FileDeltas.
Require UShFileRedir.
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ===================================================================== *)
(*  S0  THE UNION'S CODES AT A FILE LINE, READ BACK AS THE FILE'S         *)
(* ===================================================================== *)
Lemma ulm_ok_R (s : fstate) (l : uline) (a : ralt) :
  uline_nopipe l -> lm_ok U s l (lm_dec U (ualt_code (UR a))) <-> ralt_ok l a.
Proof using.
  intros Hnp. change (lm_ok ulmG) with (uok adm_u_g). change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code.
  destruct l as [ws | ws Nf | Nf | p n]; [cbn [uok]; reflexivity | cbn [uok]; reflexivity
                                   | cbn [uok]; reflexivity |].
  exfalso. exact (Hnp p n eq_refl).
Qed.

Lemma ulm_cont_R (s : fstate) (l : uline) (a : ralt) :
  lm_cont U s l (lm_dec U (ualt_code (UR a))) = cont s l a.
Proof using.
  change (lm_cont ulmG) with ucont. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_step_R (s : fstate) (l : uline) (a : ralt) :
  lm_step U s l (lm_dec U (ualt_code (UR a))) = fsm s l a.
Proof using.
  change (lm_step ulmG) with ustep. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_term_R (a : ralt) : lm_term U (lm_dec U (ualt_code (UR a))) = false.
Proof using.
  change (lm_term ulmG) with uterm. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_panic_R (a : ralt) : lm_panic U (lm_dec U (ualt_code (UR a))) = ralt_panic a.
Proof using.
  change (lm_panic ulmG) with upanic. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_free_R (a : ralt) : lmh_free K (lm_dec U (ualt_code (UR a))) = fstate_free a.
Proof using.
  change (lmh_free ulmG_hooks) with ufree. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

(* a state-free file alternative of the round's line is the record's own *)
Lemma ulm_apr_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> fstate_free a = true ->
  ralt_panic a = false -> lm_apr U K I (ualt_code (UR a)).
Proof using.
  intros Hnp Hok Hfr Hp. rewrite /lm_apr. split_and!.
  - apply (ulm_ok_R _ (ul I) a Hnp). exact Hok.
  - rewrite ulm_free_R. exact Hfr.
  - rewrite ulm_panic_R. exact Hp.
Qed.

Lemma ulm_aprs_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> ralt_panic a = false ->
  lm_aprs U I (ualt_code (UR a)).
Proof using.
  intros Hnp Hok Hp. rewrite /lm_aprs. split_and!.
  - intros s. apply (ulm_ok_R s (ul I) a Hnp). exact Hok.
  - rewrite ulm_panic_R. exact Hp.
  - exact (ulm_term_R a).
Qed.

Lemma ulm_ab_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> fstate_free a = true ->
  lm_ab U K I (ualt_code (UR a)) = cont ∅ (ul I) a.
Proof using.
  intros Hnp Hok Hfr. rewrite /lm_ab decide_True.
  - exact (ulm_cont_R ∅ (ul I) a).
  - split; [apply (ulm_ok_R ∅ (ul I) a Hnp); exact Hok | rewrite ulm_free_R; exact Hfr].
Qed.

(* the union's parse agrees with the file's wherever the file parsed *)
Lemma uline_of_u_eq (b : list (bv 8)) (l0 : uline) :
  uline_of b = l0 -> l0 <> LEcho [] -> uline_of_u b = l0.
Proof using.
  rewrite /uline_of /uline_of_u. destruct (parse_line b) as [l |]; cbn.
  - intros H _. exact H.
  - intros Heq Hne. exfalso. apply Hne. rewrite -Heq. reflexivity.
Qed.

Lemma ul_lastbody (I : list (bv 8)) : ul I = uline_of_u (UkSh.ush_lastbody I).
Proof using. reflexivity. Qed.

(* ---- cat's argument words at the line's name, positionally over its
        length (seam (d); cut W3) ---- *)
Definition ucat_ws (nm : list (bv 8)) : list (list (bv 8)) := FileDisc.uline_ws (LCat nm).

Lemma ucat_ws_exec_ok (nm : list (bv 8)) : FileDisc.uname nm -> exec_ok (ucat_ws nm).
Proof using. exact (UNamePath.cat_words_exec_ok nm). Qed.
Lemma ucat_ws_len (nm : list (bv 8)) : length (ucat_ws nm) = 2%nat.
Proof using. reflexivity. Qed.
Lemma ucat_ws_alen (nm : list (bv 8)) : UkShEcho.echo_alen (ucat_ws nm) 1%nat = length nm.
Proof using. reflexivity. Qed.
Lemma ucat_ws_fname (nm : list (bv 8)) (j : nat) :
  (j < length nm)%nat ->
  LineWords.wl_line (ucat_ws nm) !!! (UkShEcho.echo_off (ucat_ws nm) 1%nat + j)%nat
  = nm !!! j.
Proof using.
  intro Hj. unfold UkShEcho.echo_off.
  exact (LineWords.wl_line_word (ucat_ws nm) 1%nat nm j eq_refl Hj).
Qed.
Lemma ucat_ws_head (nm : list (bv 8)) : ucat_ws nm !!! 0%nat = UShCatPay.cat_pl.
Proof using. exact (UNamePath.cat_words_head nm). Qed.
Lemma ucat_ws_line (nm : list (bv 8)) :
  LineWords.wl_line (ucat_ws nm) = FileDisc.line_bytes (LCat nm).
Proof using. reflexivity. Qed.

Lemma ucat_xline (nm : list (bv 8)) (gb : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (LCat nm) gb 0%nat len ->
  UkShEcho.ush_xline_is (ucat_ws nm) gb 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). split; [exact (ucat_ws_exec_ok nm Hu) |].
  rewrite ucat_ws_line. exact (conj Hlen Hby).
Qed.

(* cat's exec-failed alternative, around its name (the command word, not
   the file's: the same at every name) *)
Lemma ucat_execfail_bytes0 :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execcat UShCatPay.cat_pl.
Proof using.
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros p Hp.
    assert (Hl : (p < length FileDisc.alt_execcat)%nat)
      by (vm_compute in Hp |- *; lia).
    exact (list_lookup_lookup_total_lt FileDisc.alt_execcat p Hl).
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
             (fun q : nat => FileDisc.alt_execcat !!! q) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj3 : (j < 3)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| j]]]; try lia; vm_compute; reflexivity.
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
             (fun q : nat => FileDisc.alt_execcat !!! (q + 1)%nat)
             7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Lemma ucat_execfail_bytes (nm : list (bv 8)) :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execcat (ucat_ws nm !!! 0%nat).
Proof using. rewrite ucat_ws_head. exact ucat_execfail_bytes0. Qed.

(* the union's admitted line shapes: the file's three, and the pipelines
   the union's admission lets through *)
Definition ush_line_pipeU (p : producer) (n : list filt) : Prop :=
  adm_u_g (LPipes p n) = true /\ pl_ok (LPipes p n).

Definition ush_line_union (l : uline) : Prop :=
  match l with LPipe p n => ush_line_pipeU p n | _ => True end.

Definition ush_line_upipe (l : uline) : Prop :=
  exists (p : producer) (n : list filt), l = LPipe p n /\ ush_line_pipeU p n.

(* the echo child's guard: an admissible echo line, at the union's parse *)
Definition union_D (I : list (bv 8)) : Prop :=
  EchoDisc.line_ok (last_ws I) /\ ul I = LEcho (last_ws I).

Lemma union_D_of_line (I : list (bv 8)) (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> ws = last_ws I ->
  FileDisc.fline_ok (UkSh.ush_lastbody I) -> union_D I.
Proof using .
  intros Hok Hwseq Hfb. subst ws. split; [exact Hok |].
  rewrite ul_lastbody. apply uline_of_u_eq.
  - rewrite /UkSh.ush_lastbody. rewrite (last_ws_lastbody I) in Hok |- *.
    exact (FileDisc.fline_ok_echo _ Hfb Hok).
  - intros Hq. injection Hq as Hq. rewrite Hq in Hok.
    pose proof (line_ok_ge2 [] Hok) as H2. cbn in H2. lia.
Qed.

Lemma union_D_nopipe (I : list (bv 8)) : union_D I -> uline_nopipe (ul I).
Proof using . intros [_ Hl]. rewrite Hl. exact (uline_nopipe_echo _). Qed.

Section UShURound.
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

  Lemma uHktaint' : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  (* the lend's credential, at the round's family and at the widened one *)
  Lemma uWcu_taint' (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ T -∗ Wcu I p.
  Proof using .
    iIntros "#Hpin #HT". iApply (uWcu_of ug r s0 PT PD I p).
    iApply (uWcf_taint ug r s0 I p v with "Hpin HT").
  Qed.

  (* =================================================================== *)
  (*  S1  THE ECHO CHILD                                                  *)
  (* =================================================================== *)
  Lemma union_D_exfb (I : list (bv 8)) :
    union_D I ->
    lk_exfb FI I = EchoDisc.alt_execfail
    /\ (length (lk_exfb FI I) - 2)%nat = 17%nat.
  Proof using .
    intros [_ Hl].
    assert (Hx : lk_exfb FI I = uexfb (ul I)) by reflexivity.
    rewrite Hx Hl. cbn [uexfb fexfb].
    split; [reflexivity |]. rewrite UShPanic.alt_execfail_len. reflexivity.
  Qed.

  (* the exec-failed diagnostic's law at the widened credential, under the
     echo guard *)
  Lemma uHexecfail_D :
    ⊢ union_links ug -∗
      UkShEcho.ush_execfail_law_wq_at_D (PS := uprogSG_free) union_D
        (lk_exfb FI)
        (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat)
        Wcu.
  Proof using .
    iIntros "#Hlk". rewrite /UkShEcho.ush_execfail_law_wq_at_D.
    iIntros "!>" (I) "%HD".
    iPoseProof (UShPanic.ush_execfail_law_hold_at (PS := uprogSG_free) FI PRE I
                  with "[]") as "#Hx".
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct (uWcu_3 ug r s0 PT PD I with "Hc") as "Hc". rewrite uWcf_S3.
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [exact Hfd | rewrite /uWcl; iExact "Hc" |].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iDestruct ("Hend" with "Hp") as "[Hc Hh]".
    iApply (uWcu_of ug r s0 PT PD I 0%nat).
    pose proof (union_D_nopipe I HD) as Hnp. destruct HD as [_ Hl].
    iApply (uWcf0_of_pre_line_id ug r s0 I Hnp
              ltac:(intros s a; rewrite Hl; exact (ustep_id_echo s _ a))
              with "[Hc] Hh").
    rewrite /uWcl. iExact "Hc".
  Qed.

  (* the four [Wc] readings the supply spends *)
  Local Lemma uwc3 (I0 : list (bv 8)) :
    ⊢ Wcu I0 3%nat -∗ ∃ v : era_pins,
        lk_pin FI (S gen_id) v ∗ lk_lpr FI (S gen_id) v I0 3%nat ∗ PRE I0.
  Proof using .
    iIntros "H". iDestruct (uWcu_3 ug r s0 PT PD I0 with "H") as "H".
    rewrite uWcf_S3 /uWcl /lk_lcred.
    iDestruct "H" as "[H HR]". iDestruct "H" as (v) "[#Hp Hc]".
    iExists v. iSplitR "Hc HR"; [iExact "Hp" |].
    iSplitL "Hc"; [iExact "Hc" | iExact "HR"].
  Qed.

  Local Lemma uwc3b (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin FI (S gen_id) v0 -∗ lk_lpr FI (S gen_id) v0 I0 3%nat -∗
      PRE I0 -∗ Wcu I0 3%nat.
  Proof using .
    iIntros "#Hp Hc HR". iApply (uWcu_of ug r s0 PT PD I0 3%nat). rewrite uWcf_S3.
    iSplitR "HR"; [| iExact "HR"].
    rewrite /uWcl /lk_lcred. iExists v0.
    iSplitR; [iExact "Hp" | iExact "Hc"].
  Qed.

  Local Lemma uwc0 (I0 : list (bv 8)) (v0 : era_pins) :
    union_D I0 ->
    ⊢ lk_pin FI (S gen_id) v0 -∗ gwc_post U PA (S gen_id) v0 I0 0%nat -∗
      PRE I0 -∗ Wcu I0 0%nat.
  Proof using .
    intro HD. iIntros "#Hp Hc HR".
    pose proof (union_D_nopipe I0 HD) as Hnp. destruct HD as [Hok Hl].
    iApply (uWcu_of ug r s0 PT PD I0 0%nat).
    iApply (uWcf0_of_pre_line_id ug r s0 I0 Hnp
              ltac:(intros s a; rewrite Hl; exact (ustep_id_echo s _ a))
              with "[Hc] HR").
    assert (Haprs : lm_aprs U I0 0%nat).
    { change 0%nat with (ualt_code (UR (REcho 0%nat))).
      apply (ulm_aprs_R I0 (REcho 0%nat) Hnp);
        [rewrite Hl; cbn [ralt_ok]; lia | reflexivity]. }
    rewrite /uWcl /lk_lcred. iExists v0. iSplitR; [iExact "Hp" |].
    cbn [lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    iApply (gwc_line_of_posts U PA (union_X_at ug s0) (S gen_id) v0 I0 0%nat Haprs
              with "Hc").
  Qed.

  (* THE ECHO CHILD'S EXEC SUPPLY AT THE CONSOLE, FROM THE TREE ROUTE *)
  Lemma uecho_exec_sup (jo : option Z) :
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      file_cons_cred (fgn_cl gf) r jo -∗
      UkShEcho.sh_exec_sup_echo_wq_at union_D Wcu.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hmade".
    rewrite /UkShEcho.sh_exec_sup_echo_wq_at. iIntros "!>" (I) "%HDI".
    pose proof HDI as [Hokws Hul].
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    iDestruct (uwc3 I with "Hcr") as (v) "(#Hpin & Hcr & HR)".
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint' I 0%nat v with "Hpin"). iApply uHktaint'. iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld
               ∗ lk_lpr FI (S gen_id) v I 3%nat ∗ PRE I)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr HR]").
    { iIntros "!> ($ & Hc & HR)". iApply (uwc3b I v with "Hpin Hc HR"). }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img (last_ws I) M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd (last_ws I) _ _ _ M pm sz sa t gb
                Hokws with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    destruct Hfd1 as [rb Hl1].
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr HR".
    { iPureIntro.
      exact (UShEcho.sh_echo_path_of_holds (last_ws I) Hokws M sa t gb
               Himg Hbytes). }
    iSplitR "Hstd Hcr HR".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr HR"; [| iFrame "Hstd Hcr HR"].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (_ & Hc & HR)".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    rewrite /ush_pre_at. iDestruct "HR" as "[Hdeed #Hwit]".
    rewrite {1}/ush_deed_at. iDestruct "Hdeed" as "[Hdeed | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hdeed" as (cs s v') "(Hown & %Htie & #Hty & #Hpin' & #Hcs)".
    rewrite /fown /fdeed. iDestruct "Hown" as "[Hdq Htk]".
    iPoseProof (uecho_cons_image_entry (PS := uprogSG_free)
                  ug Hcons (last_ws I) M sa t gb fdv FsImg.ROOTINO chs pidv
                  v s0 I r (1/2)%Qp s rb jo
                  (fun _ : Z => UkShFork.ushf_wq Wcu I) (ftkt r s)
                  (fun _ _ => eq_refl) Heq Hokws Himg Hbytes Hflen
                  eq_refl ltac:(rewrite Hl; exact Hl1) Hul
                  (UShFileRedir.ush_line_len (last_ws I) Hokws)
                  with "[] [] [] [] Hmade Hinv Hpin Hnp0 Hdep") as "#He".
    { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { (* THE BLOCK'S END PAYS THE EXIT: the deed comes back and PRE with it *)
      iIntros "!> Hpost Hdq Htk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uwc0 I v HDI with "Hpin Hpost [Hdq Htk]").
      rewrite /ush_pre_at /ush_deed_at. iSplitL; [| iExact "Hwit"].
      iLeft. iExists cs, s, v'. rewrite /fown /fdeed /FileOpen.fdq.
      iFrame "Hty Hpin' Hcs".
      iSplitL "Hdq Htk"; [iFrame "Hdq Htk" | by iPureIntro]. }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint' I 0%nat v with "Hpin HT"). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Hc Hdq Htk]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /FileOpen.fdq. iFrame "Hc Hdq Htk".
  Qed.

  Lemma uHchild_echo :
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShEcho.sh_exec_sup_echo_wq_at union_D Wcu.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iApply (uecho_exec_sup jo with "Hdep Hslot Hmade").
  Qed.

  (* THE ECHO CHILD'S LAW at the widened credential *)
  Lemma ush_child_law_union :
    ⊢ union_links ug -∗ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wcu.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade".
    iPoseProof (uHexecfail_D with "Hlk") as "#Hxl".
    iPoseProof (uHchild_echo with "Hdep Hslot Hmade") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) union_D (lk_exfb FI)
              (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat) Wcu
              union_D_of_line union_D_exfb with "Hxl Hsup").
  Qed.

  (* =================================================================== *)
  (*  S2  THE cat CHILD                                                   *)
  (* =================================================================== *)
  Definition ucat_rows (ld : list fdstate) : Prop :=
    UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld.

  (* ---- THE EXEC SUPPLY: [exec /cat] at the union's cat entry ---- *)
  Lemma ucat_exec_sup (I : list (bv 8)) (nm : list (bv 8)) (s : dst) (v' : era_pins)
      (cs' : list nat) (jo : option Z) :
    FileDisc.uname nm ->
    ul I = LCat nm ->
    upre_tie cs' s0 I (dst_content s) -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      file_cons_cred (fgn_cl gf) r jo -∗
      era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs' -∗
      f_typed (fgn_cl gf) s -∗
      UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG)
        ucat_rows (ucat_ws nm)
        (fun _ : Z => UkShFork.ushf_wq Wcu I)
        (Wcl I 3%nat ∗ fown r s).
  Proof using Heq Hkill Hcons HfifR.
    intros Hu Hul Htie Hpos. pose proof Htie as [Hlen Hcon].
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_cat nm)).
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hmade #Hpin' #Hcs' #Hty".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hrows Hstd #Hcmd Hcr".
    iAssert (□ (T -∗ UkShFork.ushf_wq Wcu I))%I as "#HQt".
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp []").
      iIntros "!> #Hk". iApply "HQt". iApply uHktaint'. iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShCatPay.cat_pl ElfUser.cat_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat ∗ fown r s)%I
              _ UShCat.cat_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img (ucat_ws nm) M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd_x (ucat_ws nm) _ _ _ M pm sz sa t gb
                (ucat_ws_exec_ok nm Hu) with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro. rewrite -(ucat_ws_head nm).
      exact (UShEcho.sh_exec_path_of_x_holds (ucat_ws nm) (ucat_ws_exec_ok nm Hu)
               M sa t gb Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsCatPin.era0_cat_pins T FsImg.ROOTINO
                UShCatPay.cat_pl [FsImg.ROOTINO; FsCatPin.CAT_INO]
                FsCatPin.CAT_INO
                (MkAnode (AFile ElfUser.cat_elf) 1%nat)
                UShCatPay.sh_cat_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [| iFrame "Hstd Hcr"].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (_ & Hc & Hd)".
    (* ---- the lend, OPENED into the round's cursor ---- *)
    rewrite {1}/uWcl /lk_lcred.
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    rewrite /gwc_blk.
    iDestruct "Hc" as "[Hc | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hc" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #HW)".
    iAssert (⌜sw = s0⌝)%I as %->.
    { cbn [gW union_params_at]. rewrite /f0w_at. iDestruct "HW" as "[_ %Hs]". done. }
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    pose proof Hw as [(Hpin0 & Hr & Hn & HP) Htail].
    iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    destruct Hrows as ([wr0 Hr0] & [rb1 Hr1] & [rb2 Hr2]).
    (* the content's C-int bound, off the claim's typing of it *)
    iAssert (⌜forall (i : Z) (bs : list (bv 8)), s !! nm = Some (i, bs) ->
               (Z.of_nat (length bs) < 2 ^ 31)%Z⌝)%I as %Hshort.
    { iIntros (i bs Hs).
      iDestruct (f_typed_lookup (fgn_cl gf) s nm i bs Hs with "Hty") as (ls0) "[_ %Hbt]".
      iPureIntro. pose proof (FileDeltas.f_bytes_typed_short ls0 nm bs Hbt) as Hb.
      unfold EchoDisc.line_max in Hb. lia. }
    iPoseProof (ucat_image_entry (PS := uprogSG_free)
                  ug Hcons nm (ucat_ws nm) M sa t gb fdv
                  FsImg.ROOTINO chs pidv v ps cs s0 I P r
                  (1/2)%Qp s rb1 rb2 jo
                  (fun _ : Z => UkShFork.ushf_wq Wcu I) (ftkt r s)
                  (fun _ _ => eq_refl) Heq Hw Hu Hul (eq_sym Hcon) Hshort
                  (ucat_ws_exec_ok nm Hu) Himg Hbytes Hflen
                  (ucat_ws_len nm) (ucat_ws_alen nm) (ucat_ws_fname nm) eq_refl
                  ltac:(rewrite Hl; exact Hr1) ltac:(rewrite Hl; exact Hr2)
                  with "[] [] [] HQt Hmade Hinv Hpin Hnp0 Hdep") as "#He".
    { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { (* WHAT cat PRODUCES, AND THE TICKET, PAY THE ROUND *)
      iIntros "!>" (a) "%Ha Hpost Hdq Htk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iAssert (fown r s) with "[Hdq Htk]" as "Hown".
      { rewrite /fown /fdeed /FileOpen.fdq. iFrame "Hdq Htk". }
      assert (Hc' : dst_content s = lm_step U (ust cs s0 I) (ul I) (lm_dec U a))
        by (rewrite Hul (ustep_id_cat _ nm); exact Hcon).
      apply elem_of_cons in Ha as [-> | Ha]; [| apply elem_of_list_singleton in Ha as ->].
      - iApply (uWcf0_of_posts_alt ug r s0 I (ualt_code (UR RCRan)) v v cs s
                  (ulm_aprs_R I RCRan Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl)
                  Hlen Hpos Hc' with "[] Hpost Hown Hty Hpin Hcs").
        cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hpin".
      - iApply (uWcf0_of_posts_alt ug r s0 I (ualt_code (UR RCNoOpen)) v v cs s
                  (ulm_aprs_R I RCNoOpen Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl)
                  Hlen Hpos Hc' with "[] Hpost Hown Hty Hpin Hcs").
        cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hpin". }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Htn Hd]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /fown /fdeed /FileOpen.fdq.
    iDestruct "Hd" as "[Hdq Htk]". iFrame "Hdq Htk".
    rewrite /cons_cur. iFrame "Htn Hps Hcs HE HW".
  Qed.

  (* ---- THE cat CHILD'S LAW ---- *)
  Lemma uHchild_cat :
    ⊢ union_links ug -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) Wcu UkShRedirBody.ushs_lp_cat 68.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len ws gb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch _ HM Hcr
       Hrun".
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch".
    destruct Hline as (nm & -> & Hlat).
    pose proof (proj1 Hlat) as Hu.
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [| lia]. exfalso.
      rewrite /last_ws in Hlws. rewrite /nlines in Hn.
      apply nil_length_inv in Hn. rewrite Hn in Hlws. cbn in Hlws.
      revert Hlws. vm_compute. discriminate. }
    assert (Hfl : fline I = LCat nm).
    { apply (FileDisc.fline_ok_cat_words (UkSh.ush_lastbody I) nm Hfok).
      rewrite -(last_ws_lastbody I). symmetry. exact Hlws. }
    assert (Hul : ul I = LCat nm).
    { rewrite ul_lastbody. apply uline_of_u_eq; [exact Hfl | discriminate]. }
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_cat nm)).
    (* ---- the lend, opened ---- *)
    iDestruct (uWcu_3 ug r s0 PT PD I with "Hcr") as "Hcr".
    rewrite uWcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /uWcl /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
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
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs)".
    pose proof Htie as [Hlen Hcon].
    (* ---- THE WALK, at 8 more steps of budget than it needs ---- *)
    assert (Hbud : (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
                   = (60 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat) by lia.
    rewrite Hbud.
    iApply (UkShEcho.wp_kshm_child_x_holds (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) ucat_rows (ucat_ws nm) FileDisc.alt_execcat
              (fun _ : Z => UkShFork.ushf_wq Wcu I)
              (Wcl I 3%nat ∗ fown r s)%I
              (∃ v : era_pins,
                 lk_pin FI (S gen_id) v
                 ∗ lk_post FI (S gen_id) v I (ualt_code (UR RCExec)) ∗ fown r s)%I
              N' (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len gb sz ld (n + 8)%nat
              Hpeq Hs1 (ucat_xline nm gb len Hlat) (ucat_execfail_bytes nm)
              Hsa Hs64 Hs38 Hszlo Hszal Hszok Hrows (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hstr Hwsp Hsy Hstd Hcwd
                    Hch HM [Hc Hd] Hrun").
    - (* exec /cat *)
      iApply (ucat_exec_sup I nm s v' cs jo Hu Hul Htie Hpos
                with "Hdep Hslot Hmade Hpin' Hcs Hty").
    - (* the child died before the exec: the lend, whole *)
      iIntros "!> [Hc Hd]". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iApply (uHwbl_f ug r s0 I). rewrite uWcf_S3. iFrame "Hc".
      rewrite /ush_pre_at /ush_deed_at. iFrame "Hwit".
      iLeft. iExists cs, s, v'. iFrame "Hd Hty Hpin' Hcs". by iPureIntro.
    - (* exec failed: the diagnostic at [RCExec] *)
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                    (ghost_varG0 := offbox_offG) FI (fown r s) I
                    (ualt_code (UR RCExec)) with "[]") as "#Hx".
      { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
      assert (Hab : lk_ab FI I (ualt_code (UR RCExec)) = FileDisc.alt_execcat).
      { change (lk_ab FI I (ualt_code (UR RCExec))) with (lm_ab U K I (ualt_code (UR RCExec))).
        rewrite (ulm_ab_R I RCExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl) Hul.
        reflexivity. }
      rewrite Hab. iExact "Hx".
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iDestruct "H" as (v) "(#Hp & Hblk & Hd)".
      iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RCExec)) v v' cs s
                (ulm_apr_R I RCExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
                Hlen Hpos ltac:(rewrite ulm_step_R Hul; exact Hcon)
                with "Hp Hblk Hd Hty Hpin' Hcs").
    - iFrame "Hc Hd".
  Qed.

  (* =================================================================== *)
  (*  S3  THE REDIRECT CHILD                                              *)
  (* =================================================================== *)

  (* echo RAN: nothing on the console (fd 1 is [f]); the block is still
     owed whole and the deed is PEND at [RFRan sel] *)
  Lemma uredir_ran_exit (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (i : Z)
      (sel : list nat) (v' : era_pins) (cs : list nat) (sp : dst) :
    FileDisc.uname nm ->
    ul I = LEchoF ws nm -> upre_tie cs s0 I (dst_content sp) ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    Wcl I 3%nat -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    f_typed (fgn_cl gf) sp -∗
    FileWrite.file_wq (fgn_cl gf) r nm sp i ws sel
      (length (subseq (echo_chunks ws) sel)) -∗
    Wcf I 0%nat.
  Proof using .
    intros Hu Hul Htp Hlen Hpos. iIntros "Hc #Hpin #Hcs #Htyp Hq".
    rewrite /FileWrite.file_wq. iDestruct "Hq" as "[Hq | #HT]"; last first.
    { iApply (uWcf_taint ug r s0 I 0%nat v' with "Hpin HT"). }
    iDestruct "Hq" as (ls) "(Hd & _ & %Hok & %Hsel & #Hlb & %Hin)".
    rewrite uWcf_0. iRight. iFrame "Hc".
    rewrite /ush_pend_at /ush_deed_at. iLeft.
    iExists cs, (<[nm := (i, subseq (echo_chunks ws) sel)]> sp), v'.
    iFrame "Hd Hpin Hcs". iSplit.
    - iPureIntro. exists (ualt_code (UR (RFRan sel))).
      rewrite /upend_tie_at ulm_term_R ulm_cont_R ulm_step_R Hul.
      split_and!; [exact Hlen | exact Hpos | | reflexivity | reflexivity |].
      2: { rewrite -(proj2 Htp). cbn [fsm]. rewrite dst_content_insert. reflexivity. }
      apply (ulm_ok_R _ (LEchoF ws nm) (RFRan sel) (uline_nopipe_echof ws nm)). exact Hsel.
    - iApply (f_typed_some (fgn_cl gf) sp ls nm ws sel i
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
    fown r (<[nm := (i, [])]> sp) -∗
    f_typed (fgn_cl gf) (<[nm := (i, [])]> sp) -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul Htp Hlen Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    assert (Hst : dst_content (<[nm := (i, [])]> sp)
                  = lm_step U (ust cs s0 I) (ul I) (lm_dec U (ualt_code (UR RFExec)))).
    { rewrite ulm_step_R Hul -(proj2 Htp). cbn [fsm].
      rewrite dst_content_insert. reflexivity. }
    iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RFExec)) v v' cs
              (<[nm := (i, [])]> sp)
              (ulm_apr_R I RFExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              Hlen Hpos Hst
              with "Hp Hblk Hd Hty Hpin' Hcs").
  Qed.

  (* the open FAILED: [f] as the round found it ([RFOpenU]), or the create
     had fired and left it empty ([RFOpenM], at an absent [f] only) *)
  Lemma uredir_openfail_exit_u (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (s : dst)
      (v v' : era_pins) (cs : list nat) :
    ul I = LEchoF ws nm ->
    upre_tie cs s0 I (dst_content s) -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ualt_code (UR RFOpenU)) -∗
    fown r s -∗ f_typed (fgn_cl gf) s -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul [Hlen Hc] Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_echof ws nm)).
    iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RFOpenU)) v v' cs s
              (ulm_apr_R I RFOpenU Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              Hlen Hpos ltac:(rewrite ulm_step_R Hul; exact Hc)
              with "Hp Hblk Hd Hty Hpin' Hcs").
  Qed.

  Lemma uredir_openfail_exit_m (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (i : Z)
      (v v' : era_pins) (cs : list nat) (sp : dst) :
    ul I = LEchoF ws nm ->
    upre_tie cs s0 I (dst_content sp) -> sp !! nm = None ->
    (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ualt_code (UR RFOpenM)) -∗
    fown r (<[nm := (i, [])]> sp) -∗
    f_typed (fgn_cl gf) (<[nm := (i, [])]> sp) -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hul [Hlen Hc] HsN Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
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
              Hlen Hpos Hst
              with "Hp Hblk Hd Hty Hpin' Hcs").
  Qed.

  (* THE REDIRECT CHILD'S EXEC SUPPLY: [exec /echo] with fd 1 on [f], at
     the union's redirect entry *)
  Lemma uredir_exec_sup (I : list (bv 8)) (ws : wordline) (nm : list (bv 8)) (v' : era_pins)
      (cs : list nat) (ls : list fwline) (sp : dst) :
    FileDisc.uname nm ->
    ul I = LEchoF ws nm -> upre_tie cs s0 I (dst_content sp) ->
    EchoDisc.line_ok ws -> (nm, ws) ∈ ls ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
      fl_lb (fgn_cl gf) ls -∗ f_typed (fgn_cl gf) sp -∗
      ∀ ty : fdtype,
        UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
          (ghost_varG0 := offbox_offG)
          (UkShRedirBody.ushs_fd1f ty) ws
          (fun _ : Z => UkShFork.ushf_wq Wcu I)
          (Wcl I 3%nat ∗ UShFileRedir.redir_K' gf r nm sp ty).
  Proof using Heq Hkill HfifR.
    intros Hu Hul Htp Hokws Hin Hlen Hpos.
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hpin' #Hcs #Hlb #Htyp" (ty).
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint' I 0%nat v' with "Hpin'"). iApply uHktaint'.
      iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat ∗ UShFileRedir.redir_K' gf r nm sp ty)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img ws M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd ws _ _ _ M pm sz sa t gb Hokws
                with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (UShEcho.sh_echo_path_of_holds ws Hokws M sa t gb Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [| iFrame "Hstd Hcr"].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (Hstd & Hc & HK & Hino)".
    (* a tainted receipt buys the generic slot *)
    iDestruct "Hino" as "[Hino | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hino" as (i γo) "(%Hty & %Hi)".
    destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
    rewrite /UShFileRedir.redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
    iDestruct "HK" as "[HK | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "HK" as (i1 γo1) "(%Hty1 & Hd & Hpub)".
    rewrite Hty in Hty1. injection Hty1 as <- <-.
    iDestruct (UserOff.foff_pub_of_held with "Hpub") as "Hu".
    (* the entry, at what is left of the lend *)
    iPoseProof (uefile_image_entry (PS := uprogSG_free)
                  ug s0 nm ws M sa t gb fdv FsImg.ROOTINO chs pidv
                  r sp (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat)%I
                  i γo false
                  (fun _ : Z => UkShFork.ushf_wq Wcu I)
                  (fun _ _ => eq_refl) Heq Hokws Himg Hbytes Hflen
                  eq_refl
                  ltac:(rewrite Hl -Hty; exact Hfd1) Hi1 Hi2 Hi3 Hi4 Hi5
                  with "[] [] [] [] Hinv Hnp0 Hdep") as "#He".
    { (* echo RAN: the exit pays the round's payload *)
      iIntros "!> [[_ Hc] Hex]". iDestruct "Hex" as (sel) "Hcur".
      rewrite /UkShFork.ushf_wq. iRight.
      rewrite /UEchoFile.efq /FileWrite.file_cur.
      iDestruct "Hcur" as "[[Hq _] | [#HT _]]".
      - iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iApply (uredir_ran_exit I ws nm i sel v' cs sp Hu Hul Htp Hlen Hpos
                  with "Hc Hpin' Hcs Htyp Hq").
      - iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Hstd Hc Hd Hu]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /UEchoFile.ef_pay /UEchoFile.efq. iFrame "Hstd Hc".
    iApply (FileWrite.file_cur_fired (fgn_cl gf) r nm sp i ws [] γo
              with "[Hd] Hu").
    rewrite /FileWrite.file_wq. iLeft. iExists ls. iFrame "Hd Hlb".
    iPureIntro. split_and!;
      [ reflexivity | exact Hokws | exact (sel_ok_nil _) | exact Hin ].
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
        (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) Wcu.
  Proof using Heq Hkill HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShRedirBody.sh_redir_child_law.
    iIntros "!>" (N' h m dw dv sa len ws file fb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch Hpid HM Hcr
       Hrun".
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch". iClear "Hpid".
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
    iDestruct (uWcu_3 ug r s0 PT PD I with "Hcr") as "Hcr".
    rewrite uWcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /uWcl /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
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
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs)".
    pose proof Htie as [Hlen Hcon].
    rewrite /uline_wit. iDestruct "Hwit" as "[Hwit | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    pose proof (fline_echof_in I ws file Hpos Hfl) as Hinl.
    rewrite /FileLinksLine.flw. iDestruct "Hwit" as "[%Hnil | Hwit]".
    { exfalso. rewrite Hnil in Hinl. by apply elem_of_nil in Hinl. }
    iDestruct "Hwit" as (ls) "[#Hfl %Hall]".
    pose proof (Hall _ Hinl) as Hin. cbn in Hin.
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
              (UShFileRedir.redir_K gf r file s) (UShFileRedir.redir_K' gf r file s)
              (fun _ => fown r s) (fun _ => UShFileRedir.redir_Kf gf r file s) tt
              (Wcl I 3%nat ∗ fown r s)%I (Wcl I 3%nat)
              (Wcu I 0%nat) (Wcu I 0%nat)
              Hpeq Hs1 Hline Hfile Hsa Hs64 Hs38 Hszlo Hszal
              Hszok Hr1 ltac:(discriminate)
              ltac:(intros ? ? ?; discriminate) Hfd2
              ltac:(destruct ld as [| y0 [| y1 l2]];
                    [ discriminate Hr0 | discriminate Hr1 | ];
                    cbn in Hr0; injection Hr0 as ->; reflexivity)
              with "Hcode Hjt Hpcode Hpro Hstr Hwsp Hsy Hstd Hcwd Hch HM
                    [] [] [] [] [] [] [] [] [] [Hc Hd] Hrun").
    - (* the open *)
      iApply (UShFileRedir.Hopen_hand gf r Heq N' _ _ s ls ws jo file Hfile Hin Hokws
                with "Hinv Hmade Hfl").
    - (* the receipt, read *)
      iIntros "!>" (ty) "HK".
      iMod (UShFileRedir.redir_K_inum gf r Heq file s ty ⊤ ltac:(set_solver) with "Hinv HK")
        as "[HK Hi]".
      iModIntro. rewrite /UShFileRedir.redir_K'. iFrame "HK Hi".
    - (* exec /echo at the file *)
      iApply (uredir_exec_sup I ws file v' cs ls s Hfile Hul Htie Hokws Hin Hlen Hpos
                with "Hdep Hslot Hpin' Hcs Hfl Hty").
    - (* exec failed *)
      iIntros (ty).
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG) FI
                    (UShFileRedir.redir_K' gf r file s ty) I (ualt_code (UR RFExec)) with "[]") as "#Hx".
      { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
      iEval (rewrite Hax) in "Hx".
      iApply (uexecfail_law_at_wand with "Hx").
      iIntros "!> H". iDestruct "H" as (v) "(#Hp & Hblk & [HK _])".
      rewrite /UShFileRedir.redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
      iDestruct "HK" as "[HK | #HT]"; last first.
      { iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
      iDestruct "HK" as (i γo) "(_ & Hd & _)".
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iApply (uredir_execfail_exit I ws file i v v' cs s Hul Htie Hlen Hpos
                with "Hp Hblk Hd Hty0 Hpin' Hcs").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight. iExact "H".
    - (* open failed *)
      rewrite /UkShDiag.ush_execfail_law_at.
      iIntros "!>" (N l) "%Hfd [HK Hc]".
      iAssert (union_links ug -∗ lk_links FI)%I as "Hlkw".
      { cbn [lk_links union_link_inst_at gen_link_inst]. iIntros "$". }
      iDestruct ("Hlkw" with "Hlk") as "#Hlk'".
      rewrite /UShFileRedir.redir_Kf. iDestruct "HK" as "[Hd | [[%HsN Hd] | #HT]]".
      + iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r s) I (ualt_code (UR RFOpenU)) with "Hlk'") as "#Hx".
        iEval (rewrite Hau alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd]") as (Pf) "(H0 & #Hs & #He)";
          [exact Hfd | iFrame "Hc Hd" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd)".
        iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iApply (uredir_openfail_exit_u I ws file s v v' cs Hul Htie Hpos
                  with "Hp' Hblk Hd Hty Hpin' Hcs").
      + iDestruct "Hd" as (i) "Hd".
        iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r (<[file := (i, [])]> s)) I
                      (ualt_code (UR RFOpenM))
                      with "Hlk'") as "#Hx".
        iEval (rewrite Ham alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd]") as (Pf) "(H0 & #Hs & #He)";
          [exact Hfd | iFrame "Hc Hd" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd)".
        iApply (uWcu_of ug r s0 PT PD I 0%nat).
        iApply (uredir_openfail_exit_m I ws file i v v' cs s Hul Htie HsN Hpos
                  with "Hp' Hblk Hd Hty0 Hpin' Hcs").
      + iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI emp%I I (ualt_code (UR RFOpenU)) with "Hlk'") as "#Hx".
        iEval (rewrite Hau alt_openfailN_nlen) in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hs & _)";
          [exact Hfd | iFrame "Hc" |].
        iExists Pf. iFrame "H0 Hs". iIntros "!> _".
        iApply (uWcu_taint' I 0%nat v' with "Hpin' HT").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight. iExact "H".
    - (* the child died before the open: the lend, whole *)
      iIntros "!> [Hc Hd]". rewrite /UkShFork.ushf_wq. iRight.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iApply (uHwbl_f ug r s0 I). rewrite uWcf_S3. iFrame "Hc".
      rewrite /ush_pre_at /ush_deed_at /uline_wit. iSplitL.
      + iLeft. iExists cs, s, v'. iFrame "Hd Hty Hpin' Hcs". by iPureIntro.
      + iLeft. rewrite /FileLinksLine.flw. iRight. iExists ls.
        iFrame "Hfl". by iPureIntro.
    - iIntros "[$ $]".
    - iFrame "Hc Hd".
  Qed.

  (* =================================================================== *)
  (*  S4  THE DISPATCH, AND THE ROUND                                     *)
  (* =================================================================== *)
  Context (γp : gname).
  Local Notation Pm := (UShLine.ush_mid_at (lk_rres FI) (fgn_echo gf) γp).

  (* THE PIPELINE SHAPES' BRANCH ([UShUPipes.ush_pipes_branch_holds]): the
     body law at the pipeline lines the union admits *)
  Definition ush_pipes_branch (N : uk_names Σ) : iProp Σ :=
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      N γp T Wcu Wbu Pm ush_line_upipe (SpecKexec.kexec_sz ElfUser.sh_elf).

  Lemma ushq_body_law_union (N : uk_names Σ) `{Hp : !ukn_const N} (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wcu -∗
    UkShRedirBody.sh_redir_child_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) Wcu -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) Wcu UkShRedirBody.ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      N γp T Wcu Wbu Pm ush_line_upipe sz -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      N γp T Wcu Wbu Pm ush_line_union sz.
  Proof using .
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hred #Hcatl #Hplaw #Hpipes".
    iPoseProof (UkShPipeForkTwin.ushf_body_law_echo_pipe (PS := uprogSG_free)
                  (SG := uexecSG_xv6) N γp T Wcu Wbu Pm
                  (fun k H => H) sz Hszlo Hszal Hszok (uHwbl_u ug r s0 PT PD)
                  with "Hkl Hchl Hplaw") as "#Hecho".
    iPoseProof (UkShCatForkTwin.ushf_body_law_cat_pipe (PS := uprogSG_free)
                  (SG := uexecSG_xv6) N γp T Wcu Wbu Pm
                  (fun k H => H) sz Hszlo Hszal Hszok (uHwbl_u ug r s0 PT PD)
                  with "Hkl Hcatl Hplaw") as "#Hcat".
    iPoseProof (UkShRedirBody.ushf_child_law_at_of_redir (PS := uprogSG_free)
                  (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) Wcu
                  with "Hred") as "#Hchr".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct lu as [ws | ws Nf | Nf | p np].
    - (* [echo ws] -- the landed walk, at the fork twin *)
      iApply ("Hecho" $! (LEcho ws) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists ws | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* [echo ws > nm] -- the same walk at the redirect child's law *)
      pose proof (proj1 (proj2 (proj1 Hlat))) as Hu.
      iDestruct (UkSh.ush_jtab_ro (ukn_t N) with "Hjt") as "#Hro".
      iApply (UkShPipeForkTwin.wp_kshm_body_pipe (PS := uprogSG_free)
                (SG := uexecSG_xv6) N γp T Wcu Wbu Pm (fun k0 H => H)
                UkShRedirBody.ushs_lp 68 h m f k len
                (FileDisc.uline_ws (LEchoF ws Nf)) sz l n
                ltac:(lia) UkShRedirBody.ushs_lp0
                Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (UkShRedirBody.ushs_lp_of_at ws Nf f k len (uname_word Nf Hu) Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb (uHwbl_u ug r s0 PT PD)
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchr Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp (ukn_t N) with "Hcode").
      + exact Hfd0.
    - (* [cat nm] -- the 'c' arm at the cat body twin *)
      iApply ("Hcat" $! (LCat Nf) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists Nf | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* a pipeline -- the premise *)
      iApply ("Hpipes" $! (LPipe p np) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ exists p, np; split; [reflexivity | exact Hd] | exact Hlat
        | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
  Qed.

End UShURound.
