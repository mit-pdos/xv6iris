(* ===================================================================== *)
(*  UShUModEcho.v -- THE [echo ws] LINE'S SHAPE MODULE (shape-modules S1, *)
(*  step 3; design: claude-notes/design/shape-modules.md sections 2 and  *)
(*  5).                                                                   *)
(*                                                                        *)
(*  Everything the round needs of the [echo ws] line, in one file: the    *)
(*  echo child's guard [union_D] (moved from [UShUModBase]), its exec     *)
(*  supply at the console and its law at the union's credential           *)
(*  [ush_child_law_union] (moved from [UShURound]'s S1), the module       *)
(*  [mod_echo] ([UkShShape.shape_mod]: the family [LEcho _], the line     *)
(*  predicate [UkSh.ush_line_is], first byte 'e', room 60) and the body   *)
(*  law at the echo line [uecho_body_law], the generic                    *)
(*  [UkShShape.ushf_body_law_of_mod]'s instance ([UkShFork.ushf_child_law] *)
(*  IS [ushf_child_law_at UkSh.ush_line_is 60]).                          *)
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
Require Import FileOut.
Require Import FileOpen.
Require Import ExecWords.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import LinkRec.
Require Import FileHooks.
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
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

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

Lemma union_D_nw (I : list (bv 8)) : union_D I -> uwild (ul I) = false.
Proof using . intros [_ Hl]. rewrite Hl. reflexivity. Qed.

Lemma union_D_nopipe (I : list (bv 8)) : union_D I -> uline_nopipe (ul I).
Proof using . intros [_ Hl]. rewrite Hl. exact (uline_nopipe_echo _). Qed.

Lemma union_D_pos (I : list (bv 8)) : union_D I -> (0 < nlines I)%nat.
Proof using .
  intros [Hok _]. pose proof (line_ok_ge2 _ Hok) as H2.
  assert (Hne : last_ws I <> []) by (intros Hq; rewrite Hq in H2; cbn in H2; lia).
  rewrite /last_ws /nlines in Hne |- *. destruct (bodies_of I) as [| b bs]; cbn [length].
  - exfalso. apply Hne. reflexivity.
  - lia.
Qed.

(* ---- THE MODULE: the echo line as the round sees it ---- *)
Lemma uecho_lp_at (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_echo lu -> UkSh.ush_line_at lu f k len ->
  UkSh.ush_line_is (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using .
  intros [ws ->] H. apply UkSh.ush_line_at_echo in H as (Hok & Hlen & Hby).
  split_and!; [exact Hok | exact Hlen |]. intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

Lemma uecho_Dc_le : (60 <= 68 + UkSh.ush_Dpipe)%nat.
Proof using . lia. Qed.

Definition mod_echo : shape_mod :=
  {| sm_D := UkSh.ush_line_echo; sm_Lp := UkSh.ush_line_is; sm_head := HeadE;
     sm_Dc := 60%nat; sm_Dc_le := uecho_Dc_le; sm_lp0 := UkShFork.ushf_lp0_echo;
     sm_lp_at := uecho_lp_at |}.

Section UShUModEcho.
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
                  (ush_pre_nw ug r s0 s0 I) with "[]") as "#Hx".
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct (uWcu_3_nw ug r s0 PT PD I (union_D_nw I HD) with "Hc") as "Hc".
    rewrite uWcf_S3.
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [exact Hfd | rewrite /uWcl; iExact "Hc" |].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iDestruct ("Hend" with "Hp") as "[Hc Hh]".
    iApply (uWcu_of ug r s0 PT PD I 0%nat).
    pose proof (union_D_nopipe I HD) as Hnp. destruct HD as [_ Hl].
    iApply (uWcf0_of_pre_line_id ug r s0 I Hnp ltac:(rewrite Hl; discriminate)
              ltac:(intros s a; rewrite Hl; exact (ustep_id_echo s _ a))
              with "[Hc] Hh").
    rewrite /uWcl. iExact "Hc".
  Qed.

  (* the four [Wc] readings the supply spends *)
  Local Lemma uwc3 (I0 : list (bv 8)) :
    uwild (ul I0) = false ->
    ⊢ Wcu I0 3%nat -∗ ∃ v : era_pins,
        lk_pin FI (S gen_id) v ∗ lk_lpr FI (S gen_id) v I0 3%nat ∗ PRE I0.
  Proof using .
    intros Hnw. iIntros "H". iDestruct (uWcu_3_nw ug r s0 PT PD I0 Hnw with "H") as "H".
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
    iApply (uWcf0_of_pre_line_id ug r s0 I0 Hnp ltac:(rewrite Hl; discriminate)
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
    iIntros "#Hdep #Hslot #Hmade".
    iPoseProof "Hslot" as "(#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_wq_at. iIntros "!>" (I) "%HDI".
    pose proof HDI as [Hokws Hul].
    assert (Hhead : last_ws I !!! 0%nat = UShEcho.echo_pl).
    { rewrite (list_lookup_total_correct (last_ws I) 0%nat EchoDisc.cmd_echo
                 (EchoDisc.line_ok_head (last_ws I) Hokws)).
      vm_compute. reflexivity. }
    pose proof (ExecWords.line_ok_exec_ok (last_ws I) Hokws) as Hxok.
    (* the supply at the console row, at any taint continuation: the lend
       as the entry sees it is [Wcu I 3] OPENED at its pin *)
    iAssert (□ (□ (app_taint -∗ UkShFork.ushf_wq Wcu I) -∗
             UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
               (ghost_varG0 := offbox_offG) UkSh.ush_fd1p (last_ws I)
               (fun _ : Z => UkShFork.ushf_wq Wcu I) (Wcu I 3%nat)))%I as "#Hsup".
    { iIntros "!> #Hkt".
      iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all
                 (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
      { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
        iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp Hkt"). }
      iApply (UShExecPin.sh_exec_sup_x_of_entry_r (ghost_varG0 := offbox_offG)
                UkSh.ush_fd1p (last_ws I) UShEcho.echo_pl FsEchoPin.era0_echo_pins
                [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO ElfUser.echo_elf T
                (UkShFork.ushf_wq Wcu I) (Wcu I 3%nat)
                (∃ v : era_pins, lk_pin FI (S gen_id) v
                   ∗ lk_lpr FI (S gen_id) v I 3%nat ∗ PRE I)%I
                Hxok Hhead UShEcho.echo_elf_loadable UShEcho.sh_echo_pin_resolves
                with "[] [] [] Hkt [Hslot]").
      - iIntros "!>" (M sa t gb fdv chs pidv) "%Himg %Hbytes %Hflen %Hrows #Hnp0".
        destruct Hrows as [rb Hl1].
        rewrite /image_entry. iModIntro.
        iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hscw %Hch0 %Hpid0 %Hargs Hmp HR".
        iDestruct "HR" as (v) "(#Hpin & Hc & HR)".
        cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
        rewrite /ush_pre_at. iDestruct "HR" as "[Hdeed #Hwit]".
        rewrite {1}/ush_deed_at. iDestruct "Hdeed" as "[Hdeed | #HT]"; last first.
        { iApply ("Hgen'" $! (UexecSlot.uvis_fd W') W' with "HT [//] [%] Hmp"); exact Hscw. }
        iDestruct "Hdeed" as (cs s v') "(Hown & %Htie & #Hty & #Hpin' & #Hcs & %Hnw & Hup)".
        rewrite /fown /fdeed. iDestruct "Hown" as "[Hdq Htk]".
        iPoseProof (uecho_cons_image_entry (PS := uprogSG_free)
                      ug Hcons (last_ws I) M sa t gb fdv FsImg.ROOTINO chs pidv
                      v s0 I r (1/2)%Qp s rb jo
                      (fun _ : Z => UkShFork.ushf_wq Wcu I) (ftkt r s ∗ urpos ug r I)%I
                      (fun _ _ => eq_refl) Heq Hokws Himg Hbytes Hflen
                      eq_refl Hl1 Hul
                      (UShFileRedir.ush_line_len (last_ws I) Hokws)
                      with "[] [] [] [] Hmade Hinv Hpin Hnp0 Hdep") as "#He".
        { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
        { iIntros "!> HT". rewrite Hkill. iExact "HT". }
        { (* THE BLOCK'S END PAYS THE EXIT: the deed comes back and PRE with it *)
          iIntros "!> Hpost Hdq [Htk Hup]". rewrite /UkShFork.ushf_wq.
          iApply (uwc0 I v HDI with "Hpin Hpost [Hdq Htk Hup]").
          rewrite /ush_pre_at /ush_deed_at. iSplitL; [| iExact "Hwit"].
          iLeft. iExists cs, s, v'. rewrite /fown /fdeed /FileOpen.fdq.
          iFrame "Hty Hpin' Hcs Hup".
          iSplitL "Hdq Htk"; [iFrame "Hdq Htk" | by iPureIntro]. }
        { iIntros "!> #HT". rewrite /UkShFork.ushf_wq.
          iApply (uWcu_taint' I 0%nat v with "Hpin HT"). }
        rewrite /image_entry.
        iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp
                                              [Hc Hdq Htk Hup]");
          [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hscw | exact Hch0 | exact Hpid0
          | exact Hargs | ].
        rewrite /FileOpen.fdq. iFrame "Hc Hdq Htk Hup".
      - iIntros "!> Hc". iApply (uwc3 I (union_D_nw I HDI) with "Hc").
      - iIntros "!> HR". iDestruct "HR" as (v) "(#Hp & Hc & HR)".
        iApply (uwc3b I v with "Hp Hc HR").
      - iApply (UShExecPin.sh_pin_slot_echo with "Hslot"). }
    (* ...at the pin the lend names, and the console row is echo's own *)
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    iDestruct (uwc3 I (union_D_nw I HDI) with "Hcr") as (v) "(#Hpin & Hc & HR)".
    iPoseProof (uwc3b I v with "Hpin Hc HR") as "Hcr".
    iPoseProof ("Hsup" with "[]") as "#Hsup'".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v with "Hpin"). iApply uHktaint'. iExact "Hk". }
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iApply ("Hsup'" $! N' m pc sa t gb ld with "[%] [%] [%] [%] [%] Hstd Hcmd Hcr");
      [ exact Hpeq | exact Ha0 | exact Ha1 | exact Hbytes | exact Hfd1 ].
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
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) T Wcu.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade".
    iPoseProof (uHexecfail_D with "Hlk") as "#Hxl".
    iPoseProof (uHchild_echo with "Hdep Hslot Hmade") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) union_D (lk_exfb FI)
              (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat) T Wcu
              union_D_of_line union_D_exfb with "Hxl Hsup []").
    (* the out-of-memory death, at the widened credential *)
    rewrite /UkShEcho.ush_oom_law_wq_at_D. iIntros "!>" (I) "%HD".
    iApply (uHoom ug r s0 PT PD I (union_D_nw I HD) (union_D_pos I HD) with "Hlk").
  Qed.

  (* THE BODY LAW at the echo line, from its child law: the generic
     wrapper's instance *)
  Lemma uecho_body_law (N : uk_names Σ) `{Hp : !ukn_const N} (γp : gname)
      (Pm : list (bv 8) -> iProp Σ) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) T Wcu -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (sm_D mod_echo) sz.
  Proof using .
    intros Hszlo Hszal Hszok. iIntros "#Hkl #Hchl #Hplaw".
    rewrite /UkShFork.ushf_child_law.
    iApply (UkShShape.ushf_body_law_of_mod (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k H => H)
              mod_echo sz Hszlo Hszal Hszok with "Hkl [] Hplaw").
    rewrite /UkShShape.sm_law. cbn [sm_Lp sm_Dc mod_echo]. iExact "Hchl".
  Qed.

End UShUModEcho.
