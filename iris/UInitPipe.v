(* ===================================================================== *)
(*  UInitPipe.v -- THE PIPELINE APPLICATION'S [al_programs] AT THE        *)
(*  N-STAGE MODEL (cut C8): [UInitBoot.echo_Hinit_boot]'s twin at         *)
(*  [AppPipe.app_pipe], whose claim is born at [PipesDisc.pipes_lmE].     *)
(*                                                                       *)
(*  WHAT IS HERE, in the order the assembly needs it:                     *)
(*                                                                       *)
(*   S1  the era's readings of its own credential families --             *)
(*       [ush_wc_inp] / [ush_wb_inp] at [PipesLinkInst]'s pair, the lend's *)
(*       conversion at the shell's entry, and the read law at the widened *)
(*       credential [UkShPipesFork.pterm_wcN].                            *)
(*   S2  [pipe_cons_in_of_Cns] and [pipe_cons_sup_of_sh_slot] --          *)
(*       [UInitBoot]'s two era-specific seam lemmas at the pipe claim and *)
(*       at [UInitSh]'s [_at] forms.                                      *)
(*   S3  [pipes_cc] -- the era's [UserConsole.cons_cred] -- and            *)
(*       [pipes_cc_holds], its ten laws, at the discipline                 *)
(*       [lm_disc_input pipes_lmE] and the line constructor                *)
(*       [PipesUline.ush_line_pipes].                                     *)
(*   S4  [pipes_Hinit_boot]: /init's exec bundle at the pipeline record,  *)
(*       with NO premise: the round's child law is proved                  *)
(*       ([UShPipesLaw.pipes_child_law], spent by                          *)
(*       [UShPipesRound.sh_round_holds_pipes]).                            *)
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
Require Import EchoLinksPro.
Require Import EchoLinksLine.
Require Import EchoLinksBan.
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
Require Import UInitBoot.          (* [init_deps_of_laws] / [init_boot_bundle_of_pinned] *)
(* ---- the pipeline era's own layers ---- *)
Require Import LinkRec.
Require Import ReadRec.
Require Import LineModel.
Require Import LineModelLinks.
Require Import PipesDisc.
Require Import PipeOut.
Require Import PipeOutN PipeOutNEv PipesOut.
Require Import PipesLinks.
Require Import GenLinksLine.
Require Import PipesLinkInst.
Require Import PipesStageInst.
Require Import PipesUline.
Require Import AppPipeClaim.
Require Import AppPipeCons.
Require Import UInitConsPipe.
Require Import PipeProto.
Require Import UkPipesIface.
Require Import UkShPipesFork.
Require Import UShPipesRound.
Require Import UShPipeCatSlot.  (* [pipe_sh_cat_slot] -- the /cat pin, off
                                   the era equation (lane SH-PIPE-ROUND-6) *)
Require Import AppPipe.
Require FsImg.
Require InodeInv.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1/S2  THE ERA'S SEAM, at [UInitBoot]'s Section-1 binder list          *)
(*         VERBATIM plus the pipeline classes.                             *)
(* ===================================================================== *)

Section UInitPipeSeam.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!pipeOutG Σ, !pipesNG Σ}.

  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Local Notation T := (echo_taint γ).
  Local Notation PI := (pipes_link_inst_at g).
  Local Notation GP := (pipes_params g).

  #[local] Instance pis_T_pers0 : Persistent T | 0 := echo_taint_persistent γ.

  (* =================================================================== *)
  (*  S1  THE READINGS OF THE FAMILIES' INPUT                             *)
  (*                                                                     *)
  (*  Every arm of every family of the generic record at [pipes_lmE]      *)
  (*  carries the input's lower bound ([gcur], or the block family's      *)
  (*  fourth conjunct, or the filed round's [pwc_blkN]), or the taint;    *)
  (*  the head arm is [False] at this record.  The reading is persistent, *)
  (*  so the credential comes back whole ([bi.persistent_entails_r]).     *)
  (* =================================================================== *)
  Local Lemma pis_lpr_inp (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat) :
    gwc_lpr pipes_lmE GP (pipes_X g) k v I p ⊢ inp_lb v I ∨ T.
  Proof using .
    destruct p as [| [| [| p']]]; cbn [gwc_lpr].
    - rewrite /gwc_line /gwc_pro /gwc_post /gcur /pipes_X /pwc_blkN.
      cbn [gH gT pipes_params]. rewrite /pipes_H.
      iIntros "[[Hl | [[] | #HT]] | [Hq | Hx]]".
      + iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
      + by iRight.
      + iDestruct "Hq" as (a) "[_ [Hl | #HT]]"; [| by iRight].
        iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
      + iDestruct "Hx" as (pre) "[_ [Hl | #HT]]"; [| by iRight].
        iDestruct "Hl" as (ps cs P) "(_ & _ & _ & _ & _ & _ & #HE)". by iLeft.
    - rewrite /gwc_sp_t /gcur. cbn [gT pipes_params].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
    - rewrite /gwc_open_t /gcur. cbn [gT pipes_params].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
    - rewrite /gwc_blk. cbn [gT pipes_params].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
  Qed.

  (* [UShLine.ush_wc_inp_lcred]'s twin at the record *)
  Lemma pipes_wc_inp : UShLine.ush_wc_inp γ T (pipes_Wcl_at g).
  Proof using .
    intros I p. iIntros "H".
    iApply (bi.persistent_entails_r with "H").
    rewrite /pipes_Wcl_at (pipes_inst_lcred g (S gen_id) I p).
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    iDestruct (pis_lpr_inp (S gen_id) v I p with "Hc") as "[#HE | #HT]".
    - iLeft. iExists v. by iFrame "Hpin HE".
    - by iRight.
  Qed.

  (* [UShLine.ush_wb_inp_ban]'s twin, off the record's own field *)
  Lemma pipes_wb_inp : UShLine.ush_wb_inp γ T (pipes_Wbl_at g).
  Proof using .
    intros I. rewrite /pipes_Wbl_at.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hb]".
    iDestruct (lk_ban_inp PI (S gen_id) v I with "Hb") as "[Hb Hi]".
    iSplitL "Hb"; [ iExists v; iFrame "Hpin Hb" | ].
    iDestruct "Hi" as "[[#HE %Hr] | #HT]"; last first.
    { iRight. iExact "HT". }
    iLeft. iSplitR; [ | by iPureIntro ]. iExists v. iFrame "Hpin HE".
  Qed.

  (* a prologue credential at the record is a boundary credential: at an
     ABSTRACT record, so that nothing reduces the projections *)
  Local Lemma pis_lcred_of_pban (L : LinkRec Σ) (k : nat) (v : era_pins)
      (I : list (bv 8)) :
    lk_pin L k v -∗ lk_pban L k v I -∗ lk_lcred L k I 0%nat.
  Proof using .
    iIntros "#Hpin Hc". rewrite /lk_lcred. iExists v. iFrame "Hpin".
    rewrite (lk_lpr_0 L).
    iApply (lk_line_of_pro L k v I). iApply (lk_pro_of_pban L k v I with "Hc").
  Qed.

  (* THE LEND'S CONVERSION AT THE SHELL'S ENTRY (the tenth law) *)
  Lemma pipes_wp_line (n : nat) :
    ⊢ UInitDiag.kinit_pro_at PI n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝ ∗ pipes_Wcl_at g I 0%nat.
  Proof using .
    iIntros "H". rewrite /UInitDiag.kinit_pro_at.
    iDestruct "H" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists I. iSplitR; [ by iPureIntro | ].
    rewrite /pipes_Wcl_at.
    iApply (pis_lcred_of_pban PI (S gen_id) v I with "Hpin Hc").
  Qed.

  Lemma pipes_ep_refl (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_epin PI (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma pipes_pin_refl (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_pin PI (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  (* ...AND THE READ LAW AT THE WIDENED CREDENTIAL: a delivered line
     refutes the terminal arm ([UShPipesRound.pipes_pterm_read_law]) *)
  Lemma pipes_wc_read_t (γp : gname) :
    forall I l : list (bv 8), wl_nl ∉ l ->
      ⊢ UShLine.ush_mid_at (lk_rres PI) γ γp (I ++ l ++ [wl_nl])%list -∗
        pterm_wcN g I 2%nat ={⊤}=∗
        UShLine.ush_mid_at (lk_rres PI) γ γp (I ++ l ++ [wl_nl])%list
        ∗ pterm_wcN g (I ++ l ++ [wl_nl])%list 3%nat.
  Proof using .
    apply (pterm_wcN_read_of g (UShLine.ush_mid_at (lk_rres PI) γ γp)
             (pipes_pterm_read_law g γp)).
    intros I l Hnl. iIntros "Hm Hc". iModIntro.
    iApply (UShLine.ush_mid_wc_read_t_at PI γ γp (S gen_id) I l Hnl
              pipes_ep_refl with "Hm Hc").
  Qed.

  (* =================================================================== *)
  (*  S2  THE SEAM SH-OPEN CONSUMES, and the supply as a wand              *)
  (*      ([UInitBoot.ush_cons_in_of_Cns] / [init_cons_sup_of_sh_slot] at  *)
  (*      the pipe claim; the second at [UInitSh]'s [_at] forms).          *)
  (* =================================================================== *)
  Context (r : echo_names).

  Lemma pipe_cons_in_of_Cns :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    app_inv fsc_fs -∗ init_cons_cred T r -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T
               (cons_never r))
        ∗ cons_never r)
     ∨ T).
  Proof using .
    intros Heq. iIntros "#Hinv #Hc".
    rewrite /init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (sh_cons_absent_pipe γ r (cons_never r)
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /UShConsK.sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (pipe_cons_never_law γ r).
    - iLeft. iApply (sh_cons_console_pipe γ r i Heq with "Hm Hinv").
    - iRight. iRight. iExact "HT".
  Qed.

  (* NAME EVERY [Persistent] THE INTRO BELOW RAISES, AT PRIORITY 0.
     [pipe_cons_sup_of_sh_slot]'s [iIntros "#Hdep #Hdp #Hplaw #Hcore"] is
     [UInitSh.init_exec_sup_of_sh_slot_at]'s own, character for
     character, and it WEDGES here (measured: [Set Default Timeout 300]
     fires on that one sentence) where it is structural there.  What
     differs is this file's Require set: the hint net now carries the
     whole pipeline tier, and [sh_prompt_law] / [sh_pay_at] /
     [init_sh_slot] are transparent definitions over VARIABLE predicates
     ([Dl], [Cr]) -- durable-notes' "fourth silent hang".  The four
     instances exist; the search does not reach them. *)
  #[local] Instance pipe_udep_pers0 :
    Persistent (udep (PS := uprogSG_free)) | 0 := udep_persistent.
  #[local] Instance pipe_prompt_law_pers0
      (Wc : list (bv 8) -> nat -> iProp Σ) :
    Persistent (UShKernel.sh_prompt_law (PS := uprogSG_free) Wc) | 0
    := UShKernel.sh_prompt_law_persistent Wc.
  #[local] Instance pipe_sh_pay_at_pers0 (Dl : FileDisc.uline -> Prop)
      (T0 : iProp Σ) (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    Persistent (UInitSh.sh_pay_at Dl T0 Cr Rsh n0) | 0
    := UInitSh.sh_pay_at_persistent Dl T0 Cr Rsh n0.
  #[local] Instance pipe_init_sh_slot_pers0 (T0 Pay : iProp Σ)
      `{!Persistent Pay} :
    Persistent (UInitSh.init_sh_slot T0 Pay) | 0
    := UInitSh.init_sh_slot_persistent T0 Pay.

  (* ...AND THE TWO THE ASSEMBLY BELOW RAISES, NAMED HERE AND NOT THERE.
     [UShEcho.sh_echo_slot] and [UkInit.init_cons_sup] need [riscvGS],
     [GenId] and the five slot classes to even ELABORATE, and the
     assembly's section binds none of them ([UInitBoot]'s [EchoInitBoot]
     takes [HR]/[GEN] as LEMMA binders) -- an [Instance] declared there
     wedges in its own STATEMENT, before any proof.  Declared here, the
     section discharge generalises them and the assembly instantiates
     them at its own [HR]/[GEN]. *)
  #[local] Instance pipe_sh_echo_slot_pers0 (T0 : iProp Σ) :
    Persistent (UShEcho.sh_echo_slot T0) | 0
    := UShEcho.sh_echo_slot_persistent T0.
  #[local] Instance pipe_init_cons_sup_pers0 (cn : cons_names)
      (T0 Cns : iProp Σ) (st : fdstate) (Cr : cons_cred Σ) :
    Persistent (UkInit.init_cons_sup cn T0 Cns st Cr) | 0
    := UkInit.init_cons_sup_persistent cn T0 Cns st Cr.
  (* ...AND THE SEAL, because a NAMED instance does not protect a
     TRANSPARENT obligation (durable-notes, LINK-GEN-6): without it the
     [Persistent] search unfolds [sh_pay_at] into [UkSh.ush_rest_l_at]'s
     wand tower before it ever reaches the instance above.  ONLY
     [sh_pay_at]: sealing [init_sh_slot] as well breaks the [iDestruct
     "Hcore" as "(#Hinv & _)"] below ("No matching clauses for match" --
     [IntoSep] cannot see through a seal either), and it is not needed,
     because the search unfolds [init_sh_slot]'s three [box]-conjuncts
     cheaply and lands on [Persistent Pay] with [Pay] sealed. *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.

  Lemma pipe_cons_sup_of_sh_slot
      (Dsc : list (bv 8) -> Prop)
      (* [%list] IS NOT DECORATION: with this file's Require set the bare
         [++] parses in [string_scope] ("The term I has type bio_x while it
         is expected to have type string"), where [UInitSh.v]'s identical
         text parses in [list_scope]. *)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b])%list -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl])%list ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (cn : cons_names) (st : fdstate)
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    UInitSh.cons_cred_holds_at cn T Dsc Hdncr Hdshort Dl Hdline Cr ->
    udep (PS := uprogSG_free) -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    UInitSh.init_sh_slot T (UInitSh.sh_pay_at Dl T Cr Rsh n0) -∗
    UkInit.init_cons_sup cn T (init_cons_cred T r) st Cr.
  Proof using .
    intros Heq Hpsok_free Hn0 Hst HCr.
    iIntros "#Hdep #Hdp #Hplaw #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct "Hcore" as "#Hcore'".
      iApply (UInitSh.init_exec_sup_of_sh_slot_at Dsc Hdncr Hdshort Dl Hdline
                T cn st (cons_never r) Cr Rsh n0 Hpsok_free Hn0 Hst HCr
                with "Hdep Hdp Hplaw [] Hcore'").
      iApply (pipe_cons_in_of_Cns Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (init_cons_cred_of_taint T r with "HT").
  Qed.

End UInitPipeSeam.

(* ===================================================================== *)
(*  S3/S4  THE CREDENTIAL AND THE BUNDLE                                  *)
(*  ([UInitBoot]'s [Section EchoInitBoot] binder list, verbatim, plus the  *)
(*  pipeline classes.)                                                    *)
(* ===================================================================== *)
Section PipeInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  (* THE ROUND'S GHOSTS: the pipe protocol, the per-process registry and
     the N-writer family's modes -- the child law allocates all three *)
  Context `{!pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.

  #[local] Instance pipes_links_pers0 `{!riscvGS Σ} (g : pipe_gn) :
    Persistent (pipes_links g) | 0 := pipes_links_persistent g.
  #[local] Instance pipe_T_pers0 (g : pipe_gn) :
    Persistent (echo_taint (pgn_cl g)) | 0
    := echo_taint_persistent (pgn_cl g).
  #[local] Instance pipe_T_tl0 (g : pipe_gn) :
    Timeless (echo_taint (pgn_cl g)) | 0
    := echo_taint_timeless (pgn_cl g).

  (* =================================================================== *)
  (*  S3  THE APPLICATION'S CONSOLE CREDENTIAL                            *)
  (* =================================================================== *)
  Lemma pipes_cc_rd_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) :
    forall i : nat,
      Timeless (UShLine.ush_rd_pin_at (lk_rres (pipes_link_inst_at g))
                  (pgn_cl g) i).
  Proof using .
    intro i. rewrite /UShLine.ush_rd_pin_at.
    apply bi.exist_timeless; intro v.
    apply bi.exist_timeless; intro I.
    apply bi.sep_timeless; [ apply bi.pure_timeless | ].
    apply bi.sep_timeless; [ apply era_pin_timeless | ].
    apply bi.sep_timeless; [ apply _ | ].
    apply bi.sep_timeless; [ apply inp_lb_timeless | ].
    apply (lk_rres_tl (pipes_link_inst_at g)).
  Qed.

  Lemma pipes_cc_wb_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) :
    forall I : list (bv 8), Timeless (pipes_Wbl_at g I).
  Proof using . intro I. apply pipes_Wbl_at_timeless. Qed.

  (* THE ERA'S WRITE CREDENTIAL IS THE WIDENED ONE: the terminal and the
     committed round reach the prompt inside the loop's own credential *)
  Definition pipes_cc (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) : cons_cred Σ :=
    MkConsCred
      (UShLine.ush_rd_pin_at (lk_rres (pipes_link_inst_at g)) (pgn_cl g))
      (pipes_cc_rd_timeless HR GEN g)
      (UShLine.ush_mid_at (lk_rres (pipes_link_inst_at g)) (pgn_cl g))
      (pterm_wcN g)
      (pipes_Wbl_at g) (pipes_cc_wb_timeless HR GEN g)
      (UInitDiag.kinit_pro_at (pipes_link_inst_at g)).

  (* ...AND THE TEN LAWS *)
  Lemma pipes_cc_holds (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) (r : echo_names) :
    @file_app Σ HF = MkAppcfg echo_names (pipe_pred (pgn_cl g)) r ->
    (⊢ pipes_links g) ->
    UInitSh.cons_cred_holds_at fsc_cons (echo_taint (pgn_cl g))
      (lm_disc_input pipes_lmE) psq_disc_snoc_ncr psq_disc_rest_short
      ush_line_pipes psq_disc_line
      (pipes_cc HR GEN g).
  Proof using .
    intros Heq Hlkp.
    assert (Htsw : ⊢ echo_taint (pgn_cl g) -∗ app_sup).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Ht". iApply (pipe_sup_of_taint (pgn_cl g) r with "Ht"). }
    assert (Hstw : ⊢ app_sup -∗ echo_taint (pgn_cl g)).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Hs". iApply (pipe_taint_of_sup (pgn_cl g) r with "Hs"). }
    pose proof (pipes_wc_inp g) as Hwci.
    pose proof (pipes_wb_inp g) as Hwbi.
    rewrite /UInitSh.cons_cred_holds_at /pipes_cc /=.
    split_and!.
    (* (1) sh's read leaf, at the pipeline discipline *)
    - intros γp N l Hpeq.
      exact (UShLine.ush_read_recv_leaf_holds_at (pipes_read_inst g)
               (pgn_cl g) (pipes_Wbl_at g) N γp l Hpeq Hstw Htsw
               (pipes_pin_refl g) Hlkp).
    (* (2) the lease, off the position *)
    - intros γp N i Hpeq.
      exact (UShLine.ush_lease_of_at (lk_rres (pipes_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipes_Wbl_at g) N γp i
               Hpeq).
    (* (3) ...and back together under the taint *)
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_taint_at (lk_rres (pipes_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipes_Wbl_at g) N γp I
               Hpeq).
    (* (4) ...and with the banner-owed credential *)
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_wb_at (lk_rres (pipes_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipes_Wbl_at g) N γp I
               Hpeq Hwbi).
    (* (5) the write credential's step at the read, at the widened
       credential: the terminal arm is refuted *)
    - intros γp I l Hnl. exact (pipes_wc_read_t g γp I l Hnl).
    (* (6) the banner-owed credential is a boundary credential *)
    - intros I. exact (pterm_wbN_wc g I).
    (* (7) a block owed is one too *)
    - intros I. exact (pterm_wcN_blk_line g I).
    (* (8) a line read at an unwritten prompt is the taint *)
    - intros γp I l Hnl.
      exact (UShLine.ush_wb_read_holds_at (pipes_link_inst_at g) (pgn_cl g)
               γp (S gen_id) I l Hnl (pipes_ep_refl g)).
    (* (9) the cursor's boundary, at the widened credential *)
    - intros γp N l i Hpeq.
      exact (UShLine.ush_posb_of_lend_at (lk_rres (pipes_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) N γp
               (pterm_wcN g) (pipes_Wbl_at g) l i Hpeq
               (pterm_wcN_inp_of g Hwci) Hwbi).
    (* (10) the lend's conversion at the shell's entry *)
    - intros n. iIntros "H".
      iDestruct (pipes_wp_line g n with "H") as (I) "[%Hlen Hc]".
      iExists I. iSplitR; [ by iPureIntro | ].
      iApply (pterm_wcN_of g I 0%nat with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S4  /init's EXEC BUNDLE AT THE PIPELINE RECORD                      *)
  (* =================================================================== *)
  Lemma pipes_Hinit_boot
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) (r : echo_names) :
    @file_app Σ HF = MkAppcfg echo_names (pipe_pred (pgn_cl g)) r ->
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = pipe_ifc g ->
    ⊢ app_inv fsc_fs -∗ pipe_boot (pgn_cl g) (S gen_id) r -∗
      pturn g (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof using HU pipeProtoG0 pnsRegG0 pipesNG0.
    intros Heq Hiface.
    (* the three projections, off the one equation *)
    assert (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = ptagE g)
      by (rewrite /riscv_rx_tag Hiface; by cbn [pipe_ifc ai_tag pipe_tag]).
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR)
                    = echo_taint (pgn_cl g))
      by (rewrite /app_taint Hiface; by cbn [pipe_ifc ai_kill pipe_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = peclE g)
      by (rewrite /riscv_cons_res Hiface; by cbn [pipe_ifc ai_cons pipe_cons]).
    assert (Hktaint : ⊢ app_taint -∗ echo_taint (pgn_cl g)).
    { rewrite Hkill. iIntros "#H". iExact "H". }
    iIntros "#Hinv Hb Hturn". iModIntro.
    (* ---- THE ERA'S PIN, out of the turn and back ---- *)
    iAssert ((∃ v : era_pins, era_pin (pgn_cl g) (S gen_id) v)
             ∗ pturn g (S gen_id))%I
      with "[Hturn]" as "[#Hpine Hturn]".
    { rewrite /pturn /EchoOut.eturn.
      iDestruct "Hturn" as (v0) "(#Hp0 & Ht1 & Ht2 & Ht3 & Ht4 & Ht5)".
      iSplitR; [ iExists v0; iExact "Hp0" | ].
      iExists v0. iFrame "Hp0 Ht1 Ht2 Ht3 Ht4 Ht5". }
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iAssert (□ (echo_taint (pgn_cl g) -∗ app_sup))%I as "#Hsup".
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!> #Ht". iApply (pipe_sup_of_taint (pgn_cl g) r with "Ht"). }
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iAssert (□ (∀ (R : iProp Σ) (W : uvis),
                  echo_taint (pgn_cl g) -∗
                  my_pay (uvis_gen W) (fun _ => R)%I -∗
                  □ (app_taint -∗ R) -∗ uslot W))%I as "#Hmint".
    { iIntros "!>" (R W) "#Ht Hp #HR".
      iDestruct ("Hsup" with "Ht") as "#Hs".
      iAssert (app_taint)%I as "#Hkc";
        [ rewrite Hkill; iExact "Ht" | ].
      iApply (uslot_mint_all with "Hs Hkc Hwp Hp HR"). }
    (* ---- the pins law, and /init's own row out of it ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint (pgn_cl g))))%I
      as "#Hfs".
    { rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!>" (v) "Hp".
      iApply (pipe_echo_fs_pure_acc (pgn_cl g) r v with "Hp"). }
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜era0_pins v⌝ ∨ echo_taint (pgn_cl g))))%I
      as "#Hcl".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    (* ---- /init's three deposits ---- *)
    iAssert (□ UkInit.init_deps (PS := uprogSG_free) (echo_taint (pgn_cl g)))%I
      as "#Hdp".
    { iApply (init_deps_of_laws (PSx := uprogSG_free) (echo_taint (pgn_cl g))
                with "[] [] [] []").
      - iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
        + iApply ("Hsup" with "HT").
        + rewrite Hkill. iExact "HT".
      - rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b).
        iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b).
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 15
                  (or_introl eq_refl)).
        iApply ("Hsup" with "HT").
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 17
                  (or_intror eq_refl)).
        iApply ("Hsup" with "HT"). }
    (* ---- the tag's reading, at the PIPELINE discipline ---- *)
    iAssert (UkSh.ush_tag_law (echo_taint (pgn_cl g))) as "#Htg".
    { iApply (UkSh.ush_tag_law_of_at (echo_taint (pgn_cl g))
                (lm_disc pipes_lmE) psq_disc_no_ctrl_d).
      rewrite /UkSh.ush_tag_law_at. iIntros "!>" (h) "Hr".
      rewrite Htag /ptagE.
      iDestruct "Hr" as "[_ Hr]". iExact "Hr". }
    (* THE LINKS, ONCE *)
    iAssert (pipes_links g) as "#Hlks";
      [ iApply (pipes_links_holds g Hcons) | ].
    assert (Hlkp : ⊢ pipes_links g)
      by (iApply (pipes_links_holds g Hcons)).
    (* ---- /echo's PINNED ENTRY ---- *)
    iAssert (UShEcho.sh_echo_slot (echo_taint (pgn_cl g))) as "#Hslot".
    { iApply UShEcho.sh_echo_slot_of_fs_pure_holds.
      rewrite /UShEcho.sh_echo_slot_of_fs_pure.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | iExact "Hmint" ]. }
    (* ---- /cat's PINNED ENTRY (lane PIPE-STAGE-5, design SS4.3n's fourth
           bullet).  The round's right child execs /cat, and the pin its
           (W) half needs has exactly one producer in the tree, at
           [FileFsPure.file_fs_pure] -- which is reachable only through
           the ERA EQUATION [Heq], and that lives here and nowhere below.
           Beside [Hslot], off the same [Hinv] and the same [Hmint]. ---- *)
    iAssert (UShCatPay.sh_cat_slot (echo_taint (pgn_cl g))) as "#Hcat".
    { iApply (UShPipeCatSlot.pipe_sh_cat_slot (pgn_cl g) r Heq
                with "Hinv Hmint"). }
    (* ---- the shell's slot: the state payload, the TAIL at the pipeline
           era's round, and the tag ---- *)
    (* LINEAR, NOT [#Hsh], and it is the lane's third wedge: an
       [iAssert ... as "#H"] raises [Persistent P] on its STATEMENT, and
       here that is [Persistent (sh_pay_at ush_line_pipes T (pipes_cc ..)
       sh_Rsh 0)], whose search descends into [UkSh.ush_rest_l_at]'s wand
       tower and does not come back (measured, twice, with the named
       instance and the [Typeclasses Opaque] seal both in place).  The
       slot is SPENT ONCE -- by [pipe_cons_sup_of_sh_slot] below, which
       intros it persistently in ITS own file's context -- so nothing
       needs it duplicated here.  [with "[]"]: it is built from the
       intuitionistic context alone, so the round's [Hb]/[Hturn] stay. *)
    iAssert (UInitSh.init_sh_slot (echo_taint (pgn_cl g))
               (UInitSh.sh_pay_at ush_line_pipes
                  (echo_taint (pgn_cl g)) (pipes_cc HR GEN g)
                  UInitSh.sh_Rsh 0%nat))%I with "[]" as "Hsh".
    { rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | ].
      iSplitR; [ iExact "Hmint" | ].
      iApply (UInitSh.sh_pay_of_parts_at ush_line_pipes
                (echo_taint (pgn_cl g)) (pipes_cc HR GEN g)
                UInitSh.sh_Rsh 0%nat
                with "[] [] Htg");
        [ iApply UInitSh.sh_pay_state_holds | ].
      iIntros (γp N).
      iApply (sh_round_holds_pipes g Hcons Hkill r Heq γp N
                with "Hlks [] Hslot Hcat Hpine").
      iApply (udep_free). }
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY, off the links, AT
       THE WIDENED CREDENTIAL: the record's law on the first arm, the
       terminal round's two prompt bytes and the committed round's filing
       on the other two.  The law is built one file down
       ([UShPipesRound.pipes_sh_prompt_law_t]), where the section
       carries ONE instance set beside the record equation; at THIS lemma,
       which takes [HR] and [GEN] explicitly, the wand's two sides are
       elaborated at different [uprogSG] instances and the proofmode's
       [IntoWand] does not come back (measured: 1h28m). *)
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free)
               (pterm_wcN g))%I as "#Hplaw".
    { iApply (pipes_sh_prompt_law_t g Hcons with "Hlks"). }
    (* ---- the supply as a wand from the console credential ---- *)
    iAssert (UkInit.init_cons_sup fsc_cons (echo_taint (pgn_cl g))
               (init_cons_cred (echo_taint (pgn_cl g)) r) init_cons_fd
               (pipes_cc HR GEN g))%I as "#Hxs".
    { iApply (pipe_cons_sup_of_sh_slot g r
                (lm_disc_input pipes_lmE) psq_disc_snoc_ncr psq_disc_rest_short
                ush_line_pipes psq_disc_line
                fsc_cons init_cons_fd (pipes_cc HR GEN g)
                UInitSh.sh_Rsh 0%nat Heq (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                (pipes_cc_holds HR GEN g r Heq Hlkp)
                with "[] [] Hplaw Hsh").
      - iApply (udep_free).
      - iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
        + iApply ("Hsup" with "HT").
        + rewrite Hkill. iExact "HT". }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (echo_taint (pgn_cl g))
               (init_cons_cred (echo_taint (pgn_cl g)) r)
               init_cons_fd)%I with "[Hb]" as "Hdn".
    { rewrite /pipe_boot /echo_boot. iDestruct "Hb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (echo_taint (pgn_cl g))
                  (init_cons_cred (echo_taint (pgn_cl g)) r)
                  (cons_key r) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_pipe (pgn_cl g) r Heq with "Hinv").
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (echo_taint (pgn_cl g))
                  (init_cons_cred (echo_taint (pgn_cl g)) r)
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_pipe (pgn_cl g) r i Heq with "Hm Hinv").
        + iApply (init_cons_cred_made_pipe (pgn_cl g) r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (echo_taint (pgn_cl g))
                    (init_cons_cred (echo_taint (pgn_cl g)) r)
                    fsc_cons init_cons_fd
                    (pipes_cc HR GEN g)
                    -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
                (echo_taint (pgn_cl g))
                (init_cons_cred (echo_taint (pgn_cl g)) r) init_cons_fd
                (pipes_cc HR GEN g)
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
    iApply (init_boot_bundle_of_pinned (echo_taint (pgn_cl g))
              (UInitKernel.init_boot_pay (PS := uprogSG_free)
                 (echo_taint (pgn_cl g))
                 (init_cons_cred (echo_taint (pgn_cl g)) r) fsc_cons
                 init_cons_fd (pipes_cc HR GEN g))
              with "Hcl Hinv Hcon [] [Hdn Hturn]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp []").
      iModIntro. iIntros "_". done.
    - iIntros "Hrd". rewrite /UInitKernel.init_boot_pay.
      (* THE READER'S RECEIPT RESIDUE AT COUNT ZERO, at the record's own
         residue ([GenLinksLine.gwc_rres]) *)
      iAssert (∃ v0 : era_pins, era_pin (pgn_cl g) (S gen_id) v0
                 ∗ gwc_rres pipes_lmE (pipes_params g) v0 [])%I
        with "[Hturn]" as "(%v0 & #Hpin0 & #Hres0)".
      { rewrite /pturn /EchoOut.eturn.
        iDestruct "Hturn" as (v0) "(#Hpin0 & Htn & _ & #Hcs0 & #Hps0 & _)".
        iExists v0. iFrame "Hpin0". rewrite /gwc_rres.
        iExists [], [], tt. iEval (rewrite /EchoOut.turn) in "Htn".
        iDestruct (mono_nat_lb_own_get with "Htn") as "#Hlb0".
        rewrite (lm_proc_before_nil pipes_lmE). cbn [length].
        iSplitR; [iPureIntro; exact (lm_rd_stage_0 pipes_lmE tt) |].
        iFrame "Hlb0 Hps0 Hcs0". }
      iDestruct (UInitBanner.kinit_ban0_of_eturn_at (pipes_link_inst_at g)
                   with "[Hturn]")
        as "[Hdl Hbn]";
        [ rewrite (pipes_inst_turn g); iExact "Hturn" | ].
      (* THE THREE LAWS, at the record *)
      iDestruct (UInitDiag.kinit_banner_law_pro_holds_at
                   (pipes_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hblaw".
      iDestruct (UInitDiag.kinit_execfail_law_holds_at
                   (pipes_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hxlaw".
      iDestruct (UInitDiag.kinit_forkfail_law_holds_at
                   (pipes_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hflaw".
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ rewrite ucons_reader_eq; iExact "Hrd" | ].
      iSplitL "Hdl".
      { rewrite /UInitBanner.kinit_dl0_at.
        iDestruct "Hdl" as (v) "(#Hpin & Hdl & #HE)".
        iDestruct (era_pin_agree with "Hpin0 Hpin") as %<-.
        rewrite /pipes_cc /=. rewrite /UShLine.ush_rd_pin_at.
        iExists v0, []. iSplitR;
          [ iPureIntro; split; [ reflexivity | exact rest_of_nil ] | ].
        iFrame "Hpin0 Hdl HE Hres0". }
      (* the banner-owed family and the record's [cc_wbn] are ONE family *)
      iAssert (□ (∀ n : nat,
                    UInitBanner.kinit_ban_at (pipes_link_inst_at g) n -∗
                    UserConsole.cc_wbn (pipes_cc HR GEN g) n))%I as "#Hbto".
      { iIntros "!>" (n) "Hb".
        rewrite /UInitBanner.kinit_ban_at /UserConsole.cc_wbn
                /pipes_cc /pipes_Wbl_at /=.
        iDestruct "Hb" as (v I) "(%Hlen & #Hpin & Hb)".
        iExists I. iSplitR; [ by iPureIntro | ]. iExists v. iFrame "Hpin Hb". }
      iAssert (□ (∀ n : nat, UserConsole.cc_wbn (pipes_cc HR GEN g) n -∗
                    UInitBanner.kinit_ban_at (pipes_link_inst_at g) n))%I
        as "#Hbfr".
      { iIntros "!>" (n) "Hb".
        rewrite /UInitBanner.kinit_ban_at /UserConsole.cc_wbn
                /pipes_cc /pipes_Wbl_at /=.
        iDestruct "Hb" as (I) "[%Hlen Hb]".
        iDestruct "Hb" as (v) "[#Hpin Hb]".
        iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hb". }
      iSplitL "Hbn"; [ iApply ("Hbto" with "Hbn") | ].
      iSplitR.
      { iIntros "!>" (n N') "Hb".
        iApply ("Hblaw" $! n N' with "[Hb]"). iApply ("Hbfr" with "Hb"). }
      rewrite /UkInitMain.kinit_diag_law.
      iSplitR; [ | iExact "Hflaw" ].
      iIntros "!>" (n N') "Hp".
      iPoseProof ("Hxlaw" $! n N' with "Hp") as "H".
      rewrite /UkInit.kinit_banner_pay.
      iIntros "Hl". iDestruct ("H" with "Hl") as (Ch) "(#Hst & H0 & Hfin)".
      iExists Ch. iFrame "Hst H0".
      iIntros "HC". iDestruct ("Hfin" with "HC") as "[$ Hrt]".
      iApply ("Hbto" with "Hrt").
  Qed.

End PipeInitBoot.
