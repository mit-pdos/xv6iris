(* ===================================================================== *)
(*  UInitConsFile.v -- /init's CONSOLE DANCE AT THE **FILE** APPLICATION'S *)
(*  CLAIM (lane INIT-FILE).                                               *)
(*                                                                        *)
(*  [UInitCons.init_cons_laws_echo] / [init_cons_laws_made_echo] and the   *)
(*  six [UInitConsK] / two [UShConsK] wrappers built over them are stated  *)
(*  at an era whose record is ECHO's.  This file is those same lemmas one  *)
(*  application over: the era's record equation is                        *)
(*                                                                        *)
(*    file_app = MkAppcfg file_names (AppFile.file_pred (fgn_cl g)) r      *)
(*                                                                        *)
(*  and every conjunct is discharged out of [AppFileCons] /               *)
(*  [FileOpen.file_cons_law] instead of [AppEcho].                        *)
(*                                                                        *)
(*  NOTHING NEW IS MINTED HERE.  [AppFile.file_taint c] IS                *)
(*  [AppEcho.echo_taint c.1] definitionally and [AppFile.fn_cons r] is an  *)
(*  [AppEcho.echo_names], so every credential the dance spends -- the key, *)
(*  the flag, the seal, [UInitCons.init_cons_cred] -- is echo's, read at   *)
(*  [fn_cons r].  What changes is only WHICH claim pays the nine laws.     *)
(*                                                                        *)
(*  TWO READINGS OF THE PURE HALF, and both are needed.  Conjunct (b) is   *)
(*  stated at a parameter [Pure]; the file era wants it at                 *)
(*  [FileFsPure.file_fs_pure], because conjunct (e)'s landed discharge     *)
(*  ([FileDeltas.file_fs_pure_unarm_fresh], through                        *)
(*  [AppFileCons.file_cons_unarm]) reads the ARM's view at that strength.  *)
(*  But [UInitConsK.init_mknod_leaf_holds] and                             *)
(*  [init_open_console_leaf_holds] -- and [UShConsK.sh_open_console_leaf_  *)
(*  holds], through [UInitCons.init_cons_laws] -- FIX the parameter at     *)
(*  [EchoFsPure.echo_fs_pure].  So the bundle is built twice, and the      *)
(*  weaker one needs an unarm leg that reads only [echo_fs_pure] at the    *)
(*  arm's view: section 1's [file_cons_unarm_efp].  It is available        *)
(*  because the arm's view is used for ONE thing only -- separating the    *)
(*  unarmed inum from the root -- and every other separation comes off the *)
(*  unarmed row's own NODE, which is a DEVICE where each pinned row is a   *)
(*  FILE.                                                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import FsTree.             (* [fname] *)
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsAbsDefs.
Require Import FsAbsDelta.         (* [cre_pre] / [delta_arm] / [delta_unarm] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsConsPin.
Require Import FsImgCheck.        (* [fname_f] *)
Require FileDisc.                 (* the class [FileDisc.uname] *)
Require Import FsFPin.            (* [f_absent] *)
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import FileDeltas.
Require Import AppEcho.
Require Import AppFile.
Require Import AppFileCons.
Require Import FileOpen.
Require Import FileOut.
Require Import EchoOut.            (* [echoOutG] *)
Require Import UInitCons.
Require Import UInitConsK.
Require Import UShConsK.
Require Import CtxIdDefs.
Require FsImg.
Require User.InitSyms.
Import Defs.

Local Open Scope Z_scope.

Section UInitConsFile.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s note): no local
     [Context {SG}] / [Context {PS}], or two [sbundle]s print identically
     and [UexecSG.psok] resolves to the generic [fun _ => True]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console KEY's camera.  NOT [mono_natG]: [Xv6Cameras]'s note --
     the flag's camera is [riscvFixedGS]'s own, and a second binder here
     would be a second instance that prints alike, which is exactly what
     makes [UInitCons.init_cons_laws_echo]'s record equation unusable. *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class (lane ECHO-OUT part 5) *)
  Context `{!echoOutG Σ}.
  (* ...and the FILE claim's own ghosts (the deed, the ticket, the escrow
     ledger, the line list) *)
  Context `{!fileAppG Σ}.

  (* THE ERA'S FIXED PART AND ITS INSTANCE.  [FileOut.file_gn] is the
     record's fixed half and [AppFile]'s is [fgn_cl g]; [r] is the era's
     name record, whose console pair [fn_cons r] is an [echo_names]. *)
  Context (g : FileOut.file_gn) (r : AppFile.file_names).

  Local Notation cdev := (ADev CONSOLE 0).

  (* =================================================================== *)
  (*  1.  THE UNARM LEG AT THE WEAKER PURE PARAMETER                      *)
  (*                                                                      *)
  (*  [AppFileCons.file_cons_unarm] reads the ARM's view at                *)
  (*  [FileFsPure.file_fs_pure], because its pure leg is                   *)
  (*  [FileDeltas.file_fs_pure_unarm_fresh], which asks for all FOUR pins  *)
  (*  there.  The consumers in [UInitConsK] / [UShConsK] fix conjunct (b)  *)
  (*  at [EchoFsPure.echo_fs_pure], which has only three -- so the leg is  *)
  (*  redone here off the unarmed ROW instead.                            *)
  (*                                                                      *)
  (*  WHAT THE ARM'S VIEW IS STILL FOR: the ROOT.  Every other separation  *)
  (*  the unarm needs comes off the node the arm put at [i] -- a DEVICE,   *)
  (*  where each of [file_fs_pure]'s four pinned rows and the deed's row   *)
  (*  is a FILE -- and the root is not separated that way, because         *)
  (*  [node_pin]'s own root reading is about a row the arm's view already  *)
  (*  had.  [echo_fs_pure av0] pins it, and [av0 !! i = None] is the       *)
  (*  receipt's freshness.                                                *)
  (* =================================================================== *)

  Lemma echo_fs_pure_unarm_root (av0 : aview) (i : Z) :
    av0 !! i = None -> echo_fs_pure av0 -> i <> FsImg.ROOTINO.
  Proof using .
    intros Hfree (Hp & _ & _).
    destruct (FileDeltas.node_pin_root _ _ _ av0
                (FileDeltas.node_pin_of_file_pin _ _ _ av0
                   (proj2 (file_pin_init av0) Hp)))
      as (ents & nl & Hrt & _).
    intros ->. by rewrite Hrt in Hfree.
  Qed.

  (* the four pins ride across at the ROW, not at the arm's view: a pinned
     row is a FILE and the row the unarm deletes is the DEVICE the arm
     put there *)
  Lemma file_fs_pure_unarm_dev (i : Z) (av : aview) (cn : absnode) :
    i <> FsImg.ROOTINO ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    file_fs_pure av -> file_fs_pure (delta_unarm i av).
  Proof using .
    intros Hroot Hrow Hcn Hp.
    assert (Hne : forall (nm : fname) (ino : Z) (bs : list (bv 8)),
              node_pin nm ino (MkAnode (AFile bs) 1%nat) av ->
              i <> ino).
    { intros nm ino bs Hpin Hij. destruct Hpin as (_ & Hr).
      rewrite Hij in Hrow. rewrite Hrow in Hr.
      injection Hr as Hnode. rewrite Hcn in Hnode. discriminate Hnode. }
    destruct (FileDeltas.file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4 & H5).
    apply FileDeltas.file_fs_pure_of_pins.
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H1) H1).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H2) H2).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H3) H3).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H4) H4).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H5) H5).
  Qed.

  (* [AppFileCons.file_cons_unarm] with [echo_fs_pure] at the arm's view *)
  Lemma file_cons_unarm_efp (av0 av : aview) (i : Z) (cn : absnode) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    (forall j : Z, cons_present_at j av -> i <> j) ->
    file_pred (FileOut.fgn_cl g) r av -∗
    file_pred (FileOut.fgn_cl g) r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hsep.
    pose proof (echo_fs_pure_unarm_root av0 i Hfree Hp0) as Hroot.
    (* ...AND NO FILE IS THIS ROW: [f_ok av s] pins each entry's
       [av !! j] at a FILE node and the unarmed row is a DEVICE. *)
    assert (Hdeed : forall s : dst,
              f_ok av s ->
              forall (N : fname) (j : Z) (bs : list (bv 8)),
                s !! N = Some (j, bs) -> i <> j).
    { intros s Hok N j bs Hs. destruct (f_ok_pin av s N j bs Hok Hs) as (_ & Hrj).
      intros Hij. subst j. rewrite Hrow in Hrj.
      injection Hrj as Hnode.
      rewrite Hcn in Hnode. discriminate Hnode. }
    iApply (file_step_free (FileOut.fgn_cl g) r av (delta_unarm i av)
              (fun Hp => file_fs_pure_unarm_dev i av cn Hroot Hrow Hcn Hp)
              (fun Hab => FsConsPin.cons_absent_unarm i av Hab)
              (fun j Hpr => FsConsPin.cons_present_unarm j i av
                              (Hsep j Hpr) Hroot Hpr)
              (fun s Hok => FileDeltas.f_ok_unarm i av s Hroot
                              (Hdeed s Hok) Hok)).
  Qed.

  (* ---- at the KEY arm ([Pv := cons_absent]) ---- *)
  Lemma file_cons_unarm_efp_absent (av0 av : aview) (i : Z) (cn : absnode) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    cons_absent av ->
    file_pred (FileOut.fgn_cl g) r av -∗
    file_pred (FileOut.fgn_cl g) r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hab.
    iApply (file_cons_unarm_efp av0 av i cn Hfree Hp0 Hrow Hcn).
    intros j Hpr. exfalso.
    pose proof (cons_present_astep j av Hpr) as Hst.
    rewrite /cons_absent in Hab. rewrite Hab in Hst. discriminate Hst.
  Qed.

  (* ---- ...and at the FLAG arm ([Pv := cons_present_at i0]) ---- *)
  Lemma file_cons_unarm_efp_present (av0 av : aview) (i i0 : Z)
      (cn : absnode) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    cons_present_at i0 av0 ->
    cons_present_at i0 av ->
    file_pred (FileOut.fgn_cl g) r av -∗
    file_pred (FileOut.fgn_cl g) r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hpv0 Hpv.
    iApply (file_cons_unarm_efp av0 av i cn Hfree Hp0 Hrow Hcn).
    intros j Hpr.
    assert (Hj : j = i0).
    { pose proof (cons_present_astep j av Hpr) as Hj1.
      pose proof (cons_present_astep i0 av Hpv) as Hj2.
      rewrite Hj1 in Hj2. injection Hj2 as Heq0. exact Heq0. }
    subst j. destruct Hpv0 as (_ & Hrow0 & _).
    intros ->. by rewrite Hrow0 in Hfree.
  Qed.

  (* =================================================================== *)
  (*  2.  THE SEAL, AND THE CREDENTIAL THE SHELL IS HANDED                *)
  (*                                                                      *)
  (*  [UInitConsK]'s [init_cons_never_abs_law] / [init_cons_seal_law_echo] *)
  (*  / [init_cons_seal_out_echo] at the file claim.  None of the three    *)
  (*  reads the nine laws: the first two are [AppFileCons]'s own seal      *)
  (*  lemmas at the era's record and the third is built from them through  *)
  (*  [AppInv.app_claim_update] and [UInitConsK.init_open_absent_leaf_     *)
  (*  holds], which takes only [UInitCons.init_cons_abs_law].             *)
  (* =================================================================== *)

  (* THE SEAL'S ABSENCE LAW at the file era.  [AppEcho.cons_never] is the
     ghost FRAGMENT, so it is persistent and timeless at this era too. *)
  Lemma init_cons_never_abs_law_file :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    ⊢ init_cons_abs_law (file_taint (FileOut.fgn_cl g))
        (cons_never (fn_cons r)).
  Proof using .
    intros Heq. rewrite /init_cons_abs_law /init_cons_pin_law.
    rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (v) "#Hn Hp".
    iDestruct (file_cons_never_law (FileOut.fgn_cl g) r) as "#Hl".
    iDestruct ("Hl" with "Hn") as "#Hl'".
    iDestruct ("Hl'" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hn Hc".
  Qed.

  (* ...and the STEP that mints it ([AppFileCons.file_cons_seal_step]). *)
  Lemma init_cons_seal_law_file :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    ⊢ □ (∀ av : aview, cons_key (fn_cons r) -∗ ▷ app_pred app_run av
           ={⊤ ∖ ↑appN}=∗
           ▷ app_pred app_run av
             ∗ (cons_never (fn_cons r) ∨ file_taint (FileOut.fgn_cl g))).
  Proof using .
    intros Heq. rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (av) "HK >Hp".
    iMod (file_cons_seal_step (FileOut.fgn_cl g) r av with "HK Hp") as "[Hp Hn]".
    iModIntro. iFrame "Hp Hn".
  Qed.

  (* WHAT A FAILED MKNOD LEAVES AT THE KEY ARM. *)
  Lemma init_cons_seal_out_file (N : uk_names Σ) :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    app_inv fsc_fs -∗
    □ (cons_key (fn_cons r) ={⊤}=∗
         UkInit.uki_mknod_out (PS := uprogSG_free) N
           (file_taint (FileOut.fgn_cl g))
           (init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r))
           init_cons_fd).
  Proof using .
    intros Heq. iIntros "#Hinv !> HK".
    iDestruct (init_cons_never_abs_law_file Heq) as "#Habs".
    iMod (app_claim_update ⊤ fsc_fs (cons_key (fn_cons r))
            (cons_never (fn_cons r) ∨ file_taint (FileOut.fgn_cl g))%I
            ltac:(set_solver) with "Hinv [] HK") as "Hn".
    { iApply (init_cons_seal_law_file Heq). }
    iModIntro. rewrite /UkInit.uki_mknod_out.
    iDestruct "Hn" as "[#Hn | #HT]"; last first.
    { iRight. iRight. iExact "HT". }
    iRight. iLeft. iExists (cons_never (fn_cons r)).
    iDestruct (init_open_absent_leaf_holds N
                 (file_taint (FileOut.fgn_cl g)) (cons_never (fn_cons r))
                 ltac:(apply _) ltac:(apply _) ltac:(apply _)
                 with "Habs Hinv") as "#Hlf".
    iSplitR; [ iExact "Hlf" | ]. iSplitR; [ iExact "Hn" | ].
    iApply (init_cons_cred_of_never (file_taint (FileOut.fgn_cl g))
              (fn_cons r) with "Hn").
  Qed.

  (* the credential the FLAG arm hands the shell *)
  Lemma init_cons_cred_made_file (i0 : Z) :
    cons_made (fn_cons r) i0 -∗
    init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r).
  Proof using .
    iApply (init_cons_cred_of_made (file_taint (FileOut.fgn_cl g))
              (fn_cons r) i0).
  Qed.

  (* ---- SH'S ABSENT ARM: generic in the credential, so the file era's
     version is [UShConsK.sh_open_absent_leaf_holds] verbatim ---- *)
  Lemma sh_cons_absent_file (K : iProp Σ) :
    Persistent K -> Timeless K ->
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    UShConsK.sh_cons_never_law (file_taint (FileOut.fgn_cl g)) K -∗
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkSh.ush_open_absent_leaf (PS := uprogSG_free) N
           (file_taint (FileOut.fgn_cl g)) K).
  Proof using .
    intros HPK HTK Heq. iIntros "#Hlaw #Hinv". iIntros "!>" (N).
    iDestruct (UShConsK.sh_open_absent_leaf_holds N
                 (file_taint (FileOut.fgn_cl g)) K _ _ HPK HTK
                 with "Hlaw Hinv") as "#H".
    iApply "H".
  Qed.

  (* =================================================================== *)
  (*  3.  THE NINE LAWS AT THE FILE CLAIM -- AND THE ONE THAT IS FALSE    *)
  (*                                                                      *)
  (*  [UInitCons.init_cons_laws_at]'s conjunct (g) -- the create at a      *)
  (*  parent and a name the syscall could have reached other than          *)
  (*  (ROOTINO, `console`) -- is REFUTABLE at [AppFile.file_pred], so      *)
  (*  neither [init_cons_laws_file] nor [init_cons_laws_made_file] exists  *)
  (*  and nothing built over them does either.  The conjunct reads         *)
  (*                                                                      *)
  (*    □ (∀ av d nmn ents nl i,                                          *)
  (*         ⌜cre_pre av d nmn ents nl i (ADev CONSOLE 0)⌝ -∗             *)
  (*         ⌜d <> ROOTINO \/ nmn <> fname_console⌝ -∗                     *)
  (*         app_pred app_run av -∗                                        *)
  (*         app_pred app_run (delta_create d nmn i (ADev CONSOLE 0) av))  *)
  (*                                                                      *)
  (*  and its side condition ADMITS [d = ROOTINO] with [nmn = fname_f],    *)
  (*  since [FileDeltas.fname_f_ne_console].  There the file claim's own   *)
  (*  deed conjunct is broken at EVERY deed value, which is                *)
  (*  [file_cons_create_other_refuted] below: at a PRESENT deed            *)
  (*  [cre_pre]'s [ents !! nmn = None] already contradicts [f_ok av s],    *)
  (*  and at an ABSENT one the create makes `f` resolve, so [f_ok] fails   *)
  (*  at the NEW view.  No reading of the claim repairs it -- the taint is *)
  (*  not available to a step wand.                                        *)
  (*                                                                      *)
  (*  WHAT IS TRUE is [file_cons_create_other_deed]: the same leg with the *)
  (*  DEED'S OWN separation beside the console's, which is the side        *)
  (*  condition [FileDeltas.f_ok_create_other] asks for.  It subsumes      *)
  (*  [AppFileCons.file_cons_create_other] (whose [nmn = fname_console]    *)
  (*  premise is unused in its proof, so that lemma is really this one at  *)
  (*  the LEFT disjunct twice) and it is the shape conjunct (g) would have *)
  (*  to take for the file era to pay it.                                  *)
  (* =================================================================== *)

  (* [cre_pre] says the created name does not resolve in the OLD view --
     the one reading of it both halves of the refutation use. *)
  Lemma cre_pre_astep_none (av : aview) (d : Z) (nmn : fname)
      (ents : gmap fname Z) (nl : nat) (i : Z) (cn : absnode) :
    cre_pre av d nmn ents nl i cn -> astep av d nmn = None.
  Proof using .
    intros (Hd & Hnm & _). rewrite /astep /aents Hd /= /anode_ents /=.
    exact Hnm.
  Qed.

  (* THE LEG THAT IS TRUE: conjunct (g)'s premise PLUS the deed's own
     separation.  [AppFileCons.file_cons_create_other] is this at
     [or_introl] twice. *)
  Lemma file_cons_create_other_deed (av : aview) (d : Z) (nmn : fname)
      (ents : gmap fname Z) (nl : nat) (i : Z) :
    cre_pre av d nmn ents nl i cdev ->
    (d <> FsImg.ROOTINO \/ nmn <> fname_console) ->
    (d <> FsImg.ROOTINO \/ ~ FileDisc.uname nmn) ->
    file_pred (FileOut.fgn_cl g) r av -∗
    file_pred (FileOut.fgn_cl g) r (delta_create d nmn i cdev av).
  Proof using .
    intros Hpre Hcons Hf.
    iApply (file_step_free (FileOut.fgn_cl g) r av
              (delta_create d nmn i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_create d nmn ents nl i cdev
                           av Hpre file_cons_arm_nd Hp)
              (fun Hab => FileDeltas.cons_absent_create_nd d nmn ents nl i
                            cdev av Hpre file_cons_arm_nd Hcons Hab)
              (fun j Hpr => FileDeltas.cons_present_create_nd j d nmn ents nl
                              i cdev av Hpre file_cons_arm_nd Hpr)
              (fun s Hok => FileDeltas.f_ok_create_other d nmn ents nl i cdev
                              av s Hpre file_cons_arm_nd Hf Hok)).
  Qed.

  (* =================================================================== *)
  (*  4.  THE REST OF THE DANCE, MODULO THAT ONE LEG                      *)
  (*                                                                      *)
  (*  Conjunct (g) is the ONLY thing missing, and these lemmas say so      *)
  (*  mechanically: each takes [file_cons_create_leg] -- conjunct (g)      *)
  (*  verbatim, at the file claim -- as a premise and concludes exactly    *)
  (*  what [UInitCons.init_cons_laws_echo] / [init_cons_laws_made_echo]    *)
  (*  and [UInitConsK.init_cons_leaves_echo] / [init_cons_hit_echo] /      *)
  (*  [UShConsK.sh_cons_console_echo] conclude, one application over.      *)
  (*  NOTHING IS ASSUMED HERE THAT IS NOT CONJUNCT (g) ITSELF: repair      *)
  (*  (g)'s side condition in [UInitCons.init_cons_laws_at] -- the R3.4    *)
  (*  spelling [d <> ROOTINO \/ (nmn <> fname_console /\ nmn <> fname_f)]  *)
  (*  is enough -- discharge it by [file_cons_create_other_deed], and the  *)
  (*  five lemmas below lose their premise with no other change.           *)
  (*                                                                      *)
  (*  THE BUNDLE IS BUILT FOUR TIMES, two credentials by two readings of   *)
  (*  the pure half.  The [_efp] pair is the one every landed consumer     *)
  (*  takes ([UInitConsK.init_mknod_leaf_holds],                           *)
  (*  [init_open_console_leaf_holds] and [UShConsK.sh_open_console_leaf_   *)
  (*  holds] fix conjunct (b) at [echo_fs_pure]); the [file_fs_pure] pair  *)
  (*  is the STRONGER statement, the one an unarm leg that reads the       *)
  (*  arm's view at full strength can have, and it is what a consumer      *)
  (*  generalised over [Pure] would want.                                  *)
  (* =================================================================== *)

  Definition file_cons_create_leg : iProp Σ :=
    (□ (∀ (av : aview) (d : Z) (nmn : fname) (ents : gmap fname Z)
          (nl : nat) (i : Z),
          ⌜cre_pre av d nmn ents nl i cdev⌝ -∗
          ⌜d <> FsImg.ROOTINO \/ nmn <> fname_console⌝ -∗
          ⌜d <> FsImg.ROOTINO \/ ~ FileDisc.uname nmn⌝ -∗
          file_pred (FileOut.fgn_cl g) r av -∗
          file_pred (FileOut.fgn_cl g) r (delta_create d nmn i cdev av)))%I.

  (* ...AND IT IS NOW A THEOREM.  Lane INIT-FILE repaired conjunct (g)'s
     side condition in [UInitCons.v] exactly as this file's refutation
     asked: it excludes the FILE application's own name too, and at that
     strength [file_cons_create_other_deed] proves the leg outright.  So
     every [_of_leg] lemma below loses its premise. *)
  Lemma file_cons_create_leg_holds : ⊢ file_cons_create_leg.
  Proof using .
    rewrite /file_cons_create_leg.
    iIntros "!>" (av d nmn ents nl i) "%Hpre %Hnc %Hnf Hp".
    iApply (file_cons_create_other_deed av d nmn ents nl i Hpre Hnc Hnf
              with "Hp").
  Qed.

  Global Instance file_cons_create_leg_persistent :
    Persistent file_cons_create_leg.
  Proof using . rewrite /file_cons_create_leg. apply _. Qed.

  (* the FLAG arm's own create leg, VACUOUS: a create of `console` at the
     root cannot fire at a view where `console` already resolves
     ([AppEcho.echo_cons_mknod_present]'s twin). *)
  Lemma file_cons_mknod_present (av : aview) (ents : gmap fname Z)
      (nl : nat) (i j : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i cdev ->
    cons_made (fn_cons r) j -∗ file_pred (FileOut.fgn_cl g) r av -∗
      file_pred (FileOut.fgn_cl g) r
        (delta_create FsImg.ROOTINO fname_console i cdev av).
  Proof using .
    intros Hpre. iIntros "#Hm Hp".
    iDestruct (FileOpen.file_cons_law (FileOut.fgn_cl g) r j with "Hm")
      as "#Hl".
    iDestruct ("Hl" $! av with "Hp") as "[Hp [%Hpr | #Ht]]"; last first.
    { rewrite /file_pred. by iLeft. }
    exfalso.
    pose proof (cons_present_astep j av Hpr) as Hst.
    pose proof (cre_pre_astep_none av FsImg.ROOTINO fname_console ents nl i
                  cdev Hpre) as Hn.
    rewrite Hst in Hn. discriminate Hn.
  Qed.

  (* ---- 4b.  ...and at the ECHO reading, which is what the leaves take ---- *)
  Lemma init_cons_laws_efp_file_of_leg :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    file_cons_create_leg -∗
    init_cons_laws (file_taint (FileOut.fgn_cl g)) (cons_key (fn_cons r))
      (fn_cons r).
  Proof using .
    intros Heq.
    rewrite /init_cons_laws /init_cons_laws_at /init_cons_pin_law
            /file_cons_create_leg.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iIntros "#Hg".
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht".
      iApply (file_sup_of_taint (FileOut.fgn_cl g) r with "Ht").
    - iIntros "!>" (v) "Hp".
      iApply (file_echo_fs_pure_acc (FileOut.fgn_cl g) r v with "Hp").
    - iApply (file_cons_abs_law (FileOut.fgn_cl g) r).
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (file_cons_arm (FileOut.fgn_cl g) r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hab0 %Hab %Hrow %Hcn Hp".
      iApply (file_cons_unarm_efp_absent av0 av i cn
                Hfree Hp0 Hrow Hcn Hab with "Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (file_cons_mknod (FileOut.fgn_cl g) r av ents nl i Hpre
                with "Hk Hp").
    - iExact "Hg".
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (file_cons_shoot (FileOut.fgn_cl g) r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm".
      iApply (FileOpen.file_cons_law (FileOut.fgn_cl g) r i with "Hm").
  Qed.

  Lemma init_cons_laws_made_efp_file_of_leg (i0 : Z) :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    file_cons_create_leg -∗
    cons_made (fn_cons r) i0 -∗
    init_cons_laws_at EchoFsPure.echo_fs_pure (cons_made (fn_cons r))
      (cons_present_at i0) (file_taint (FileOut.fgn_cl g))
      (cons_made (fn_cons r) i0).
  Proof using .
    intros Heq.
    rewrite /init_cons_laws_at /init_cons_pin_law /file_cons_create_leg.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iIntros "#Hg #Hm".
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht".
      iApply (file_sup_of_taint (FileOut.fgn_cl g) r with "Ht").
    - iIntros "!>" (v) "Hp".
      iApply (file_echo_fs_pure_acc (FileOut.fgn_cl g) r v with "Hp").
    - iIntros "!>" (v) "#Hm' Hp".
      iDestruct (FileOpen.file_cons_law (FileOut.fgn_cl g) r i0 with "Hm")
        as "#Hl".
      iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hm' Hc".
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (file_cons_arm (FileOut.fgn_cl g) r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hpv0 %Hpv %Hrow %Hcn Hp".
      iApply (file_cons_unarm_efp_present av0 av i i0 cn
                Hfree Hp0 Hrow Hcn Hpv0 Hpv with "Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (file_cons_mknod_present av ents nl i i0 Hpre with "Hk Hp").
    - iExact "Hg".
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (file_cons_shoot (FileOut.fgn_cl g) r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm2".
      iApply (FileOpen.file_cons_law (FileOut.fgn_cl g) r i with "Hm2").
  Qed.

  (* ---- 4d.  THE MISS ARM'S PAIR ---- *)
  Lemma init_cons_leaves_file_of_leg :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    file_cons_create_leg -∗
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkInit.init_cons_leaves (PS := uprogSG_free) N
           (file_taint (FileOut.fgn_cl g)) (cons_key (fn_cons r))
           (init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r))
           init_cons_fd).
  Proof using .
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hg #Hinv".
    iDestruct (init_cons_laws_efp_file_of_leg Heq with "Hg") as "#Hlaws".
    iModIntro. iIntros (N). rewrite /UkInit.init_cons_leaves. iSplit.
    - iApply (init_open_absent_leaf_holds N (file_taint (FileOut.fgn_cl g))
                (cons_key (fn_cons r))
                ltac:(apply _) ltac:(apply _) ltac:(apply _)
                with "[] Hinv").
      rewrite /init_cons_laws /init_cons_laws_at.
      iDestruct "Hlaws" as "(_ & _ & #Hc & _)". iExact "Hc".
    - iApply (init_mknod_leaf_holds N cons_absent
                (file_taint (FileOut.fgn_cl g)) (cons_key (fn_cons r))
                (fn_cons r)
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iApply (init_cons_seal_out_file N Heq with "Hinv").
  Qed.

  (* ---- 4e.  THE FLAG ARM'S PAIR: the node is already there ---- *)
  Lemma init_cons_hit_file_of_leg (i0 : Z) :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    file_cons_create_leg -∗
    cons_made (fn_cons r) i0 -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         □ UkInit.uki_open_console_leaf (PS := uprogSG_free) N
             (file_taint (FileOut.fgn_cl g)) init_cons_fd
         ∗ □ UkInit.uki_mknod_hit_leaf (PS := uprogSG_free) N
               (file_taint (FileOut.fgn_cl g))
               (init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r))
               init_cons_fd).
  Proof using .
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hg #Hm #Hinv".
    iDestruct (init_cons_laws_made_efp_file_of_leg i0 Heq with "Hg Hm")
      as "#Hlaws".
    iAssert (init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r))
      as "#Hcred".
    { iApply (init_cons_cred_made_file i0 with "Hm"). }
    iModIntro. iIntros (N). iSplit.
    - iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (file_taint (FileOut.fgn_cl g)) (cons_made (fn_cons r) i0)
                (fn_cons r) i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
    - iModIntro.
      iApply (UkInit.uki_mknod_hit_of_leaf (PS := uprogSG_free) N
                (file_taint (FileOut.fgn_cl g)) (cons_made (fn_cons r) i0)
                (init_cons_cred (file_taint (FileOut.fgn_cl g)) (fn_cons r))
                init_cons_fd with "[] Hm").
      iApply (init_mknod_leaf_holds N (cons_present_at i0)
                (file_taint (FileOut.fgn_cl g)) (cons_made (fn_cons r) i0)
                (fn_cons r)
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iIntros "!> #Hm'". iModIntro. rewrite /UkInit.uki_mknod_out. iLeft.
      iSplitR; [ | iExact "Hcred" ].
      iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (file_taint (FileOut.fgn_cl g)) (cons_made (fn_cons r) i0)
                (fn_cons r) i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
  Qed.

  (* ---- 4f.  WHAT SH'S CONSOLE ARM IS HANDED ---- *)
  Lemma sh_cons_console_file_of_leg (i : Z) :
    file_app = MkAppcfg file_names (file_pred (FileOut.fgn_cl g)) r ->
    file_cons_create_leg -∗
    cons_made (fn_cons r) i -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkSh.ush_open_console_leaf (PS := uprogSG_free) N
           (file_taint (FileOut.fgn_cl g))).
  Proof using .
    intros Heq. iIntros "#Hg #Hmade #Hinv".
    iDestruct (init_cons_laws_efp_file_of_leg Heq with "Hg") as "#Hlaws".
    iIntros "!>" (N).
    iDestruct (UShConsK.sh_open_console_leaf_holds N
                 (file_taint (FileOut.fgn_cl g)) (cons_key (fn_cons r))
                 (fn_cons r) i _ _ with "Hlaws Hmade Hinv") as "#H".
    iApply "H".
  Qed.

End UInitConsFile.
