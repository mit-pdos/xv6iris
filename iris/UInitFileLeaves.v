(* ===================================================================== *)
(*  UInitFileLeaves.v -- /init's LEAVES AT THE FILE CLAIM                *)
(*                                                                       *)
(*  What the union's boot ([UInitUnionBoot] / [UInitUnionCC]) takes from  *)
(*  the retired file application's /init files, moved here verbatim when  *)
(*  those were deleted (union cut C9h): the boot filing ([boot_at], the   *)
(*  head precondition at the era's boot state), the two readings of the   *)
(*  supply at the claim equation, the claim's pure half and /init's pin   *)
(*  row, /init's three deposits, the taint's generic slot, the banner     *)
(*  writer's frame, and the console credential's readings.  Every one is  *)
(*  about [AppFile.file_pred] / [FileOut.file_gn] and states the claim    *)
(*  equation it needs as a parameter, so nothing here names a record.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ObsTrace.
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FsAbsDefs.
Require Import FileInvDefs.
Require Import UserFd.
Require Import ConsoleInv.
Require Import WpUart.
Require Import UexecSlot.
Require Import UexecRet.
Require Import UexecSG.
Require Import UexecExecInst.      (* the INSTANCES: [uprogSG_free] *)
Require Import UexecExecMint.      (* [udepw_law_of_sup] / [uslot_mint_all] *)
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import FsInitPinBoot.      (* [era0_pins] *)
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import FileFsPure.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import AppFile.
Require Import AppFileCons.        (* the claim's console readings *)
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import LinkRec.
Require Import FileLinkGen.        (* [f0pre_at] *)
Require Import GenLinksLine.
Require Import UkRun.
Require Import UkWriteClosed.      (* [kinit_w1_of_closed_l0] *)
Require Import UkInit.
Require Import UkInitMain.
Require Import UkSh.
Require Import UShLine.
Require Import UShConsK.
Require Import UInitDiag.
Require Import UInitBanner.
Require Import UInitCons.
Require Import UInitSh.
Require Import UInitConsFile.      (* the console's two open leaves at the file claim *)
Require Import LinkUserinit.       (* [UG.uexec_wp_gen] *)
Import Defs.
Local Open Scope Z_scope.

Section UInitFileLeaves.
  (* [UInitBoot.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), plus
     the file claim's and the file stage's classes.  NO [uexecSG] and NO
     [uprogSG] SECTION VARIABLE -- every deposit position names
     [UexecExecInst.uprogSG_free] per lemma. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* the era's record ([FileOut]'s gname pair) and the deed's names *)
  Context (g : file_gn) (r : file_names).

  Local Notation FT := (file_taint (fgn_cl g)).

  (* =================================================================== *)
  (*  1.  THE BOOT FILING, AND THE HEAD PRECONDITION AT THE BOOT STATE    *)
  (* =================================================================== *)
  (* THE BOOT FILING (RULING F0-BOOT).  The deed's typed witness names the
     era's boot state; init files it into the boot ledger it holds in
     [fturn], and what comes out is the head precondition AT THAT STATE.
     Under the taint the witness names nothing, so the state is [None]. *)
  Definition boot_at (s0 : fstate) (s : dst) : iProp Σ :=
    ((⌜s0 = dst_content s⌝ ∗ f_typed (fgn_cl g) s) ∨ (⌜s0 = None⌝ ∗ FT))%I.

  Global Instance boot_at_persistent s0 s : Persistent (boot_at s0 s).
  Proof using . rewrite /boot_at. apply _. Qed.

  (* THE FILING, out of the boot ledger's authority alone *)
  Lemma file_f0bw_of_boot (s0 : fstate) :
    FileOut.fturn g (S gen_id) ==∗
    FileOut.fturn_core g (S gen_id) ∗ FileLinksLine.f0bw g (S gen_id) s0.
  Proof using .
    iIntros "Ht".
    iMod (FileOut.fturn_file g (S gen_id) s0 with "Ht") as "[Ht Hbl]".
    iDestruct "Hbl" as (vf) "[#Hvf #Hbl]".
    iModIntro. iFrame "Ht". rewrite /FileLinksLine.f0bw.
    iSplitR; [ by iPureIntro | ]. iExists vf. iFrame "Hvf Hbl".
  Qed.

  (* ...AND THE HEAD PRECONDITION, out of the witness beside it.  A plain
     wand, so that /init can take it UNDER THE LATER [AppFile.file_boot]
     puts on the witness (its boot transport is a [|==>], whose conclusion
     is no [◇]-absorber). *)
  Lemma file_f0pre_at_of_bw (s0 : fstate) (s : dst) :
    FileLinksLine.f0bw g (S gen_id) s0 -∗ boot_at s0 s -∗ f0pre_at g s0.
  Proof using .
    iIntros "#Hbw Hb". rewrite /FileLinkGen.f0pre_at.
    iDestruct "Hb" as "[[-> Hty] | [-> #HT]]".
    - destruct s as [[i bs] | ];
        cbn [dst_content fmap option_fmap option_map].
      + iEval (rewrite /f_typed /=) in "Hty".
        iDestruct "Hty" as (ls) "[#Hlb %Hbt]".
        iSplitR.
        { iPureIntro. destruct Hbt as (ws & sel & _ & Hok & Hsel & ->).
          exact (FileDisc.fcont_ok_subseq ws sel Hok Hsel). }
        iSplitR; [ | iExact "Hbw" ].
        iLeft. iEval (rewrite /FileOut.f0_typed /=).
        iExists ls. iFrame "Hlb". by iPureIntro.
      + iSplitR; [ iPureIntro; exact I | ].
        iSplitR; [ | iExact "Hbw" ].
        iLeft. iApply (FileOut.f0_typed_none g).
    - iSplitR; [ iPureIntro; exact I | ].
      iSplitR; [ | iExact "Hbw" ]. by iRight.
  Qed.

  (* =================================================================== *)
  (*  2.  THE TWO READINGS OF THE SUPPLY                                  *)
  (*                                                                     *)
  (*  [AppFile.file_sup_of_taint] / [file_taint_of_sup] at the CLAIM      *)
  (*  equation, which is where they become facts about [AppInv.app_sup].  *)
  (* =================================================================== *)
  Lemma file_sup_of_taint_at
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (FT -∗ AppInv.app_sup).
  Proof using .
    rewrite /AppInv.app_sup Heq.
    cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!> #Ht". iApply (AppFile.file_sup_of_taint (fgn_cl g) r with "Ht").
  Qed.

  Lemma file_taint_of_sup_at
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ AppInv.app_sup -∗ FT.
  Proof using .
    rewrite /AppInv.app_sup Heq.
    cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "#Hs". iApply (AppFile.file_taint_of_sup (fgn_cl g) r with "Hs").
  Qed.

  (* =================================================================== *)
  (*  3.  THE CLAIM'S PURE HALF, AND /init's OWN PIN ROW                  *)
  (*                                                                     *)
  (*  [AppEcho.echo_fs_pure_acc]'s twin, straight off [AppFile.file_pred] *)
  (*  -- the claim IS the taint or the pure half beside the two state     *)
  (*  conjuncts, so the accessor costs nothing -- and the projection      *)
  (*  [FsInitPinBoot.era0_pins] that [PinnedExec]'s bundle asks for.      *)
  (* =================================================================== *)
  Lemma file_fs_pure_law
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
           AppCfg.app_pred AppCfg.app_run v
           ∗ (⌜FileFsPure.file_fs_pure v⌝ ∨ FT)).
  Proof using .
    rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!>" (v) "Hp". iApply (AppFileCons.file_fs_pure_acc (fgn_cl g) r v with "Hp").
  Qed.

  Lemma file_era0_pins_law
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
           AppCfg.app_pred AppCfg.app_run v
           ∗ (⌜FsInitPinBoot.era0_pins v⌝ ∨ FT)).
  Proof using .
    iDestruct (file_fs_pure_law Heq) as "#Hfs".
    iIntros "!>" (v) "Hp".
    iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro;
        exact (proj1 (FileFsPure.file_fs_pure_echo v Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* =================================================================== *)
  (*  4.  /init's THREE DEPOSITS, AT THE FILE TAINT                       *)
  (*                                                                     *)
  (*  [UInitBoot.init_deps_of_laws] is echo's file's, and re-proved here  *)
  (*  rather than imported: importing [UInitBoot.v] would put the whole   *)
  (*  ECHO program tier in front of this leaf for six lines of plumbing.  *)
  (*  The deposits themselves are the supply's, exactly as at echo --     *)
  (*  write(16) under the taint, the closed-fd leaf at every record, and  *)
  (*  open(15) / mknod(17) free off the supply.                           *)
  (* =================================================================== *)
  Lemma file_init_deps_of_laws `{PSx : uprogSG Σ} (T : iProp Σ) :
    □ (T -∗ UkRun.udepw_law (PS := PSx) 16) -∗
    UkInit.kinit_wcl (PS := PSx) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 15) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 17) -∗
    □ UkInit.init_deps (PS := PSx) T.
  Proof using .
    iIntros "#Hwr #Hwcl #H15 #H17 !>".
    rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
    iSplit; [ iSplit; [ iModIntro; iExact "Hwr" | iExact "Hwcl" ] | ].
    iSplit.
    - iModIntro. iExact "H15".
    - iModIntro. iExact "H17".
  Qed.

  Lemma file_init_deps
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = FT) :
    ⊢ □ UkInit.init_deps (PS := uprogSG_free) FT.
  Proof using .
    iDestruct (file_sup_of_taint_at Heq) as "#Hsup".
    iApply (file_init_deps_of_laws (PSx := uprogSG_free) FT
              with "[] [] [] []").
    - iModIntro. iIntros "#HT".
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      + iApply ("Hsup" with "HT").
      + rewrite Hkill. iExact "HT".
    - rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b).
      iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b).
    - iModIntro. iIntros "HT".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 15 (or_introl eq_refl)).
      iApply ("Hsup" with "HT").
    - iModIntro. iIntros "HT".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 17 (or_intror eq_refl)).
      iApply ("Hsup" with "HT").
  Qed.

  (* =================================================================== *)
  (*  5.  THE TAINT'S GENERIC SLOT                                        *)
  (*                                                                     *)
  (*  [UInitBoot]'s [Hmint] at the file taint: the arm every pinned exec  *)
  (*  falls back on once the era is off the discipline.                   *)
  (* =================================================================== *)
  Lemma file_gen_mint
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = FT) :
    ⊢ □ (∀ (R : iProp Σ) (W : uvis),
           FT -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (app_taint -∗ R) -∗ uslot W).
  Proof using .
    iDestruct (file_sup_of_taint_at Heq) as "#Hsup".
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iIntros "!>" (R W) "#Ht Hp #HR".
    iDestruct ("Hsup" with "Ht") as "#Hs".
    iAssert (app_taint)%I as "#Hkc"; [ rewrite Hkill; iExact "Ht" | ].
    iApply (uslot_mint_all with "Hs Hkc Hwp Hp HR").
  Qed.
End UInitFileLeaves.


Section UInitFileLeavesCC.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!fileAppG Σ, !fileOutG Σ}.

  (* THE WRITER FRAMES A RESOURCE (PROGRAM-STREAM stretch 15): [UkInit.
     kinit_banner_pay]'s per-byte family carries [H] beside each step
     ([UkInit.kinit_w1_frame]) and hands it back beside the post.  This is
     what lets the /init prologue laws, stated at the bare record
     credential, carry the deed's hold. *)
  Lemma kinit_banner_pay_frame (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (N : uk_names Σ) (stc : fdstate) (len : nat) (f : nat -> bv 8)
      (Rt H : iProp Σ) :
    UkInit.kinit_banner_pay (PS := uprogSG_free) N stc len f Rt -∗ H -∗
    UkInit.kinit_banner_pay (PS := uprogSG_free) N stc len f (Rt ∗ H).
  Proof using .
    iIntros "Hp HH Hstd". iDestruct ("Hp" with "Hstd") as (Ch) "(#Hst & H0 & Hend)".
    iExists (fun j : nat => (Ch j ∗ H)%I). iSplitR.
    { iIntros "!>" (j) "%Hj".
      iApply (UkInit.kinit_w1_frame with "[]"). iApply ("Hst" $! j with "[%]").
      exact Hj. }
    iSplitL "H0 HH"; [ iFrame "H0 HH" | ].
    iIntros "[Hc HH]". iDestruct ("Hend" with "Hc") as "[$ $]". iExact "HH".
  Qed.


  (* ===================================================================== *)
  (*  THE CONSOLE'S TWO OPEN LEAVES, out of /init's console credential,     *)
  (*  at the file claim.                                                    *)
  (* ===================================================================== *)
  Lemma file_cons_in_of_Cns (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    app_inv fsc_fs -∗ UInitCons.init_cons_cred (file_taint (fgn_cl g)) (fn_cons r) -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N (file_taint (fgn_cl g)))
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N
               (file_taint (fgn_cl g)) (cons_never (fn_cons r)))
        ∗ cons_never (fn_cons r))
     ∨ file_taint (fgn_cl g)).
  Proof using .
    iIntros "#Hinv #Hc". rewrite /UInitCons.init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (UInitConsFile.sh_cons_absent_file g r (cons_never (fn_cons r))
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /UShConsK.sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (AppFileCons.file_cons_never_law (fgn_cl g) r).
    - iLeft.
      iApply (UInitConsFile.sh_cons_console_file_of_leg g r i Heq
                with "[] Hm Hinv").
      iApply UInitConsFile.file_cons_create_leg_holds.
    - iRight. iRight. iExact "HT".
  Qed.

  (* THE CREDENTIAL /init HANDS DOWN, READ AS THE FILE CLAIM'S: the three
     arms of [UInitCons.init_cons_cred] are the two flags of
     [AppFileCons.file_cons_cred] beside its taint arm -- [None] serves the
     sealed console and the tainted era alike, since the file claim's
     consumers only ever spend the flag as "not the row I am touching". *)
  Lemma file_cons_cred_of_init (g : file_gn) (r : file_names) :
    UInitCons.init_cons_cred (file_taint (fgn_cl g)) (fn_cons r) -∗
    ∃ jo : option Z, file_cons_cred (fgn_cl g) r jo.
  Proof using .
    rewrite /UInitCons.init_cons_cred. iIntros "#[Hn | [[%j Hm] | HT]]".
    - iExists None. iApply (file_cons_cred_of_never with "Hn").
    - iExists (Some j). iApply (file_cons_cred_of_made with "Hm").
    - iExists None. iApply (file_cons_cred_of_taint with "HT").
  Qed.
End UInitFileLeavesCC.

