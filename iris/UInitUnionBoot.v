(* ===================================================================== *)
(*  UInitUnionBoot.v -- /init's EXEC BUNDLE AT THE UNION RECORD (cut C9g; *)
(*  design: claude-notes/design/union.md section 4).                      *)
(*                                                                        *)
(*  [UInitFileBoot.file_Hinit_boot_at] line for line at the union: the   *)
(*  claim's readings on the file-system view are the file application's   *)
(*  (the union's [app_pred] IS [AppFile.file_pred]), the console record   *)
(*  is the union's ([UnionOut.ucl] / [utag]), the credential is           *)
(*  [UInitUnionCC.union_cc] at the WIDENED family, the prompt law is      *)
(*  [UShURoundLaws.ush_prompt_law_u], and the shell's tail is the closed  *)
(*  union round law [UShUPipes.sh_round_holds_union_closed].              *)
(*                                                                        *)
(*  THE BOOT STATE IS FILED HERE (the file's RULING F0-BOOT): the deed's  *)
(*  typed witness names the era's boot state [s0], /init files it, and    *)
(*  everything below is at the record indexed by that [s0]               *)
(*  ([UnionLinkInstAt.union_link_inst_at ug s0]).  The pipeline era's    *)
(*  founding ([UnionOut.union_era_split]) happened in the ledger's power  *)
(*  step, which hands /init [fturn] and the claim [ucl] at the era's head. *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.
Require Import UexecSG.
Require Import PathElems.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import ConsoleInv.
Require Import SpecKexec.
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PinnedExec.
Require Import UexecExecInst.
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecMint.
Require Import UkWriteClosed.
Require Import UInitKernel.
Require Import LineWords.
Require Import EchoLinks.
Require Import UInitDiag.
Require Import UInitBanner.
Require Import UInitCons.
Require Import UInitConsK.
Require Import UInitSh.
Require Import UShPanic.
Require Import UShEcho.
Require Import UShCatPay.
Require Import UShLine.
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import UserFd.
Require Import LinkUserinit.
Require Import UkSh.
Require Import UShConsK.
Require Import KexecDefs.
Require Import PageGeom.
Require Import InitBoot.
Require Import ElfUser.
Require Import ElfLoadable.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import UInitBoot.          (* [init_boot_bundle_of_pinned] *)
Require Import LinkRec.
Require Import FileDisc.
Require Import FileState.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import FileOut.
Require Import AppFile.
Require Import AppFileCons.        (* [file_cons_cred] *)
Require Import FileLinksLine.
Require Import FileLinkGen.
Require Import GenLinksLine.
Require Import PipeOut.
Require Import PipeProto.
Require Import UkPipesIface.       (* [pipesNG], [pnsRegG] *)
Require Import UkCatFIface.        (* [cifRegG] *)
Require Import UnionDisc.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UnionReadInstAt.    (* [union_tag_law_holds] *)
Require Import UShURoundDefs.
Require Import UShURoundShapes.
Require Import UShURoundLaws.      (* [ush_prompt_law_u] *)
Require Import UShURound.          (* [ush_line_union] *)
Require Import UShUPipes.          (* the round law *)
Require UShExecPin.                (* [sh_grep_slot] *)
Require Import UInitFileLeaves.    (* the claim's readings, the boot filing, [kinit_banner_pay_frame] *)
Require Import UInitConsFile.      (* the console dance's file leaves *)
Require Import UInitUnionCC.       (* [union_cc], its laws, the supply *)
Require Import AppUnionRec.        (* [union_ifc] *)
Require UkFileIface.               (* [fifRegG]: the binder below needs it in scope *)
Require FsImg.
Require InodeInv.

Local Open Scope Z_scope.

Section UnionInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!fileAppG Σ, !fileOutG Σ, !pipeOutG Σ}.
  (* THE ROUND'S GHOSTS: the pipe protocol, the per-process registry, the
     N-writer family's modes, the producer registry and the file handler's
     registry -- the round's child laws allocate them *)
  Context `{!pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ, !cifRegG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  (* SEALED, as [UInitFileBoot.v]: a [Persistent]/[IntoWand] search on
     [sh_pay_at] descends into [ush_rest_l_at]'s wand tower. *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.
  #[local] Typeclasses Opaque UkSh.ush_rest_l_at.

  (* A SLOT ABSORBS A [◇], because it ends in a [WP] *)
  Lemma uslot_except_0_u (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (W : uvis) :
    ◇ (uslot (SG := uexecSG_xv6) W : iProp Σ) -∗ uslot (SG := uexecSG_xv6) W.
  Proof using .
    rewrite !(uslot_unfold (SG := uexecSG_xv6) W).
    iIntros "H" (h xi C pt Rfd Rut HRut) "%Hl %Hp %Hlz Hb".
    rewrite /wp_triv. iMod "H".
    iApply ("H" $! h xi C pt Rfd Rut HRut with "[//] [//] [//] Hb").
  Qed.

  Lemma union_Hinit_boot_at
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) :
    @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl (ugn_file ug))) r ->
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = union_ifc ug ->
    ⊢ app_inv fsc_fs -∗ file_boot (fgn_cl (ugn_file ug)) (S gen_id) r -∗
      fturn (ugn_file ug) (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0.
  Proof using HU HfifR cifRegG0 pipeProtoG0 pnsRegG0 pipesNG0.
    intros Heq Hiface.
    (* the four projections, off the one equation *)
    assert (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = utag ug)
      by (rewrite /riscv_rx_tag Hiface; by cbn [union_ifc ai_tag union_tag]).
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR)
                    = file_taint (fgn_cl (ugn_file ug)))
      by (rewrite /app_taint Hiface; by cbn [union_ifc ai_kill union_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = ucl ug)
      by (rewrite /riscv_cons_res Hiface; by cbn [union_ifc ai_cons union_cons]).
    assert (Hrdwild : @riscv_rdwild Σ (@riscv_fixedGS Σ HR) = wild_none)
      by (rewrite /riscv_rdwild Hiface; by cbn [union_ifc ai_rdwild]).
    assert (Hktaint : ⊢ app_taint -∗ file_taint (fgn_cl (ugn_file ug))).
    { rewrite Hkill. iIntros "#H". iExact "H". }
    iIntros "#Hinv Hb Hturn".
    (* ---- THE DEED, AND THE BOOT STATE IT NAMES ---- *)
    rewrite /file_boot. iDestruct "Hb" as "[Hcb Hd]".
    iDestruct "Hd" as (s) "[Hd Hty]". rewrite bi.later_or.
    iAssert (∃ s0 : fstate, ▷ boot_at (ugn_file ug) s0 s)%I with "[Hty]" as (s0) "#Hbt".
    { iDestruct "Hty" as "[#Hty | #HT]".
      - iExists (dst_content s). iNext. rewrite /boot_at. iLeft. by iFrame "Hty".
      - iExists ∅. iNext. rewrite /boot_at. iRight. by iFrame "HT". }
    iMod (file_f0bw_of_boot (ugn_file ug) s0 with "Hturn") as "[Hturn #Hbw]".
    iAssert (▷ f0pre_at (ugn_file ug) s0)%I as "#Hpre".
    { iNext. iApply (file_f0pre_at_of_bw (ugn_file ug) s0 s with "Hbw Hbt"). }
    (* ---- THE ERA'S PIN, out of the (filed) turn ---- *)
    iAssert (∃ v : era_pins, era_pin (fgn_echo (ugn_file ug)) (S gen_id) v)%I as "#Hpine".
    { rewrite /fturn_core. iDestruct "Hturn" as (v vf) "(#Hp0 & _)".
      iExists v. iExact "Hp0". }
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iDestruct (file_sup_of_taint_at (ugn_file ug) r Heq) as "#Hsup".
    iDestruct (file_gen_mint (ugn_file ug) r Heq Hkill) as "#Hmint".
    (* ---- the pins law, and /init's own row out of it ---- *)
    iDestruct (file_fs_pure_law (ugn_file ug) r Heq) as "#Hfs".
    iDestruct (file_era0_pins_law (ugn_file ug) r Heq) as "#Hcl".
    (* ---- /init's three deposits ---- *)
    iDestruct (file_init_deps (ugn_file ug) r Heq Hkill) as "#Hdp".
    iAssert (□ (file_taint (fgn_cl (ugn_file ug)) -∗ UkSh.sh_deps (PS := uprogSG_free)))%I
      as "#Hshdp".
    { iModIntro. iIntros "#HT". rewrite /UkSh.sh_deps.
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      - iApply ("Hsup" with "HT").
      - rewrite Hkill. iExact "HT". }
    (* ---- the tag's reading, at the UNION discipline ---- *)
    iDestruct (union_tag_law_holds ug Htag) as "#Htg".
    (* THE LINKS, ONCE *)
    iAssert (union_links ug) as "#Hlks"; [iApply (union_links_holds ug Hcons) |].
    assert (Hlkp : ⊢ union_links ug) by (iApply (union_links_holds ug Hcons)).
    (* ---- /echo's and /cat's PINNED ENTRIES, off the same claim law ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜EchoFsPure.echo_fs_pure v⌝ ∨ file_taint (fgn_cl (ugn_file ug)))))%I
      as "#Hefs".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (FileFsPure.file_fs_pure_echo v Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    iAssert (UShEcho.sh_echo_slot (file_taint (fgn_cl (ugn_file ug)))) as "#Hslot".
    { iApply UShEcho.sh_echo_slot_of_fs_pure_holds.
      rewrite /UShEcho.sh_echo_slot_of_fs_pure.
      iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hefs" | iExact "Hmint"]. }
    iAssert (UShCatPay.sh_cat_slot (file_taint (fgn_cl (ugn_file ug)))) as "#Hcat".
    { iApply UShCatPay.sh_cat_slot_of_fs_pure_holds.
      rewrite /UShCatPay.sh_cat_slot_of_fs_pure.
      iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hfs" | iExact "Hmint"]. }
    (* ---- /grep's, off the same claim law: the fixed part pins grep too
           ([FileFsPure.file_fs_pure_grep], cut G6) ---- *)
    iAssert (UShExecPin.sh_grep_slot (file_taint (fgn_cl (ugn_file ug)))) as "#Hgrep".
    { iApply UShExecPin.sh_grep_slot_of_fs_pure_holds.
      rewrite /UShCatPay.sh_cat_slot_of_fs_pure.
      iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hfs" | iExact "Hmint"]. }
    (* ---- the shell's slot, UNDER THE CONSOLE'S FLAG: the state payload,
           the TAIL at the union's round, the tag ---- *)
    iAssert (□ (∀ jo : option Z,
                  file_cons_cred (fgn_cl (ugn_file ug)) r jo -∗
                  UInitSh.init_sh_slot (file_taint (fgn_cl (ugn_file ug)))
                    (UInitSh.sh_pay_at ush_line_union
                       (file_taint (fgn_cl (ugn_file ug))) (union_cc HR GEN ug r s0)
                       UInitSh.sh_Rsh 0%nat)))%I with "[]" as "#Hsh".
    { iIntros "!>" (jo) "#Hcred".
      rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hefs" |].
      iSplitR; [iExact "Hmint" |].
      iApply (UInitSh.sh_pay_of_parts_at ush_line_union
                (file_taint (fgn_cl (ugn_file ug))) (union_cc HR GEN ug r s0)
                UInitSh.sh_Rsh 0%nat
                with "[] [] Htg");
        [iApply UInitSh.sh_pay_state_holds |].
      iIntros (γp N).
      iApply (sh_round_holds_union_closed ug r Heq s0 Hcons Hkill γp N
                with "Hlks [] Hslot Hcat Hgrep Hpine []").
      - iApply (udep_free).
      - iExists jo. iExact "Hcred". }
    (* ---- THE PROMPT'S LAW at every line boundary, at the widened
           credential ---- *)
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free)
               (uWcu ug r s0 (upterm_shape ug) (updone_shape ug)))%I as "#Hplaw".
    { iApply (ush_prompt_law_u ug r s0 Hcons with "Hlks"). }
    (* ---- the supply as a wand from the console credential ---- *)
    iAssert (UkInit.init_cons_sup fsc_cons (file_taint (fgn_cl (ugn_file ug)))
               (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r)) init_cons_fd
               (union_cc HR GEN ug r s0))%I as "#Hxs".
    { iApply (union_cons_sup_of_sh_slot HR GEN ug r s0 Heq Hcons Htag Hrdwild
                init_cons_fd 0%nat (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity) Hlkp
                with "[] Hshdp Hplaw Hsh").
      iApply (udep_free). }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (file_taint (fgn_cl (ugn_file ug)))
               (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r))
               init_cons_fd)%I with "[Hcb]" as "Hdn".
    { rewrite /echo_boot. iDestruct "Hcb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (file_taint (fgn_cl (ugn_file ug)))
                  (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r))
                  (cons_key (fn_cons r)) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_file_of_leg (ugn_file ug) r Heq with "[] Hinv").
        iApply (file_cons_create_leg_holds (ugn_file ug) r).
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (file_taint (fgn_cl (ugn_file ug)))
                  (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r))
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_file_of_leg (ugn_file ug) r i Heq with "[] Hm Hinv").
          iApply (file_cons_create_leg_holds (ugn_file ug) r).
        + iApply (init_cons_cred_made_file (ugn_file ug) r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  ⌜uvis_secc W' = ProcDefs.secc_all⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (file_taint (fgn_cl (ugn_file ug)))
                    (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r))
                    fsc_cons init_cons_fd
                    (union_cc HR GEN ug r s0)
                    -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
                (file_taint (fgn_cl (ugn_file ug)))
                (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r)) init_cons_fd
                (union_cc HR GEN ug r s0)
                fsc_cons
                1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
                init_cons_fd_ne
                (UkInit.init_kill_law_of_taint _ _ _ _ Hktaint)
                (init_boot_room 0%nat
                                   ltac:(vm_compute; discriminate))
                fdt0_length eq_refl (fdv_nopipe_closed _)
                (fun k H => H)
                with "[] [] Hxs").
      - iModIntro. iExact "Hdp".
      - iApply (udep_free). }
    (* ---- THE LINEAR PAYLOAD'S TWO WITNESS-PAID PIECES, ONE STEP LATER ---- *)
    iAssert (▷ (UserConsole.cc_rd (union_cc HR GEN ug r s0) 0%nat
                ∗ UserConsole.cc_wbn (union_cc HR GEN ug r s0) 0%nat))%I
      with "[Hturn Hd]" as "Hp1".
    { iNext.
      iDestruct (union_rres_at_of_boot ug s0 with "Hturn Hpre")
        as "[Hturn Hres0]".
      iDestruct "Hres0" as (v0) "[#Hpin0 #Hres0]".
      iDestruct (union_Wbf_at_of_boot ug r s0 s with "Hturn Hpre Hd Hbt")
        as "[Hdl Hbn]".
      iSplitL "Hdl".
      { rewrite /union_cc /=. rewrite /UShLine.ush_rd_pin_at.
        iDestruct "Hdl" as (v) "(#Hpin & Hdl & #HE)".
        iDestruct (era_pin_agree with "Hpin0 Hpin") as %<-.
        iExists v0, []. iSplitR;
          [ iPureIntro; split; [ reflexivity | exact rest_of_nil ] | ].
        iFrame "Hpin0 Hdl HE". iExact "Hres0". }
      rewrite /UserConsole.cc_wbn /union_cc /=. iExists []. by iFrame "Hbn". }
    (* ---- THE THREE LAWS, at the record, and the bundle's payload ---- *)
    iDestruct (UInitDiag.kinit_banner_law_pro_holds_at
                 (union_link_inst_at ug s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hblaw".
    iDestruct (UInitDiag.kinit_execfail_law_holds_at
                 (union_link_inst_at ug s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hxlaw".
    iDestruct (UInitDiag.kinit_forkfail_law_holds_at
                 (union_link_inst_at ug s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hflaw".
    set (Pay0 := (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
                    (file_taint (fgn_cl (ugn_file ug)))
                    (init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r))
                    init_cons_fd
                  ∗ ucons_reader fsc_cons 0%nat
                  ∗ □ (∀ (n : nat) (N' : uk_names Σ),
                        UserConsole.cc_wbn (union_cc HR GEN ug r s0) n -∗
                        UkInitMain.kinit_banner0 (PS := uprogSG_free) N' init_cons_fd
                          (UserConsole.cc_wp (union_cc HR GEN ug r s0) n))
                  ∗ UkInitMain.kinit_diag_law (PS := uprogSG_free) init_cons_fd
                      (UserConsole.cc_wp (union_cc HR GEN ug r s0))
                      (UserConsole.cc_wbn (union_cc HR GEN ug r s0)))%I).
    set (Pay1 := (UserConsole.cc_rd (union_cc HR GEN ug r s0) 0%nat
                  ∗ UserConsole.cc_wbn (union_cc HR GEN ug r s0) 0%nat)%I).
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  ⌜uvis_secc W' = ProcDefs.secc_all⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  (Pay0 ∗ ▷ Pay1) -∗ uslot W'))%I as "#Hcon'".
    { iIntros "!>" (W') "%Hok %Hcw %Hlz %Hsc Hp [HP0 HP1]".
      iApply uslot_except_0_u. rewrite /Pay1. iMod "HP1" as "[Hrd0 Hwb0]".
      iModIntro.
      iApply ("Hcon" $! W' with "[%] [%] [%] [%] Hp [HP0 Hrd0 Hwb0]");
        [ exact Hok | exact Hcw | exact Hlz | exact Hsc | ].
      rewrite /UInitKernel.init_boot_pay /Pay0.
      iDestruct "HP0" as "(Hdn & Hrd & #Hbl & #Hdg)".
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ iExact "Hrd" | ].
      iSplitL "Hrd0"; [ iExact "Hrd0" | ].
      iSplitL "Hwb0"; [ iExact "Hwb0" | ].
      iSplitR; [ iExact "Hbl" | iExact "Hdg" ]. }
    iApply (init_boot_bundle_of_pinned (file_taint (fgn_cl (ugn_file ug))) (Pay0 ∗ ▷ Pay1)
              with "Hcl Hinv Hcon' [] [Hdn Hp1]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp []").
      iModIntro. iIntros "_". done.
    - iIntros "Hrd". iSplitR "Hp1"; [ | iExact "Hp1" ]. rewrite /Pay0.
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ rewrite ucons_reader_eq; iExact "Hrd" | ].
      iSplitR.
      { iIntros "!>" (n N') "Hb".
        iDestruct (union_wbn_to HR GEN ug r s0 n with "Hb") as "[[Hb Hh] | #Hw]".
        - iApply (UInitBanner.kinit_banner0_mono_at (PS := uprogSG_free) N'
                    (UInitDiag.kinit_pro_at (union_link_inst_at ug s0) n
                     ∗ union_H HR GEN ug r s0 n)%I
                    with "[] [Hb Hh]").
          { iIntros "H". rewrite /union_cc /=. by iLeft. }
          iApply (kinit_banner_pay_frame HR GEN N' _ _ _ _ _ with "[Hb] Hh").
          iApply ("Hblaw" $! n N' with "Hb").
        - (* THE WILD HOLD: the banner through the era's licence, and the
             hold lent on (seccomp design 10.5) *)
          rewrite /UkInitMain.kinit_banner0.
          iApply (union_wild_pay HR GEN ug Hcons N' n with "Hw").
          iIntros "_". rewrite /union_cc /=. by iRight. }
      rewrite /UkInitMain.kinit_diag_law.
      iSplitR; last first.
      { iIntros "!>" (n N') "Hp". rewrite /union_cc /=.
        iDestruct "Hp" as "[[Hp _] | #Hw]".
        - iApply ("Hflaw" $! n N' with "Hp").
        - iApply (union_wild_pay HR GEN ug Hcons N' n with "Hw"). by iIntros "_". }
      iIntros "!>" (n N') "Hp". rewrite {1}/union_cc /=.
      iDestruct "Hp" as "[[Hp Hh] | #Hw]"; last first.
      { iApply (union_wild_pay HR GEN ug Hcons N' n with "Hw"). iIntros "_".
        iApply (union_wbn_of_wild HR GEN ug r s0 n with "Hw"). }
      iPoseProof ("Hxlaw" $! n N' with "Hp") as "H".
      iDestruct (kinit_banner_pay_frame HR GEN N' _ _ _ _ _ with "H Hh") as "H".
      rewrite /UkInit.kinit_banner_pay.
      iIntros "Hl". iDestruct ("H" with "Hl") as (Ch) "(#Hst & H0 & Hfin)".
      iExists Ch. iFrame "Hst H0".
      iIntros "HC". iDestruct ("Hfin" with "HC") as "[$ Hrt]".
      iDestruct "Hrt" as "[Hb Hh]".
      iApply (union_wbn_of HR GEN ug r s0 n with "Hb Hh").
  Qed.

End UnionInitBoot.
