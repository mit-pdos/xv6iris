(* ===================================================================== *)
(*  AppFileCons.v -- THE FILE CLAIM'S CONSOLE READINGS (lane INIT-FILE). *)
(*                                                                       *)
(*  [AppEcho]'s console laws at [AppFile.file_pred], each one            *)
(*  application of [AppFile.file_pred_cons] over the echo lemma.  They    *)
(*  are exactly the conjuncts of [UInitCons.init_cons_laws_at] whose      *)
(*  view does NOT move: the accessor closes at the same [av], so the      *)
(*  file conjunct of the claim is framed and nothing about the file is    *)
(*  read.  [FileOpen.file_cons_law] is the shape and was the first of     *)
(*  them; these are the other five, gathered here rather than in          *)
(*  [FileOpen.v] because they are about the CONSOLE and not the deed,     *)
(*  and because a consumer of them should not have to take the whole      *)
(*  open cone.                                                           *)
(*                                                                       *)
(*  THE MOVING-VIEW CONJUNCTS ARE HERE TOO ([init_cons_laws_at]'s arm,    *)
(*  unarm, mknod and create-other legs), through                          *)
(*  [AppFile.file_step_free] / [file_pred_split] and the [FileDeltas]     *)
(*  legs.  The UNARM is the last of them and it needed the conjunct to    *)
(*  MOVE: it is derivable once (e) carries the unarmed row and its NODE   *)
(*  (lane INIT-FILE, the UNARM ruling), and was not derivable before.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.
Require Import FsAbsDefs.
Require Import FsConsPin.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import EchoDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FsTree.            (* [fname] *)
Require Import FsAbsDelta.        (* [cre_pre] / [delta_arm] / [delta_create] *)
Require Import FsImg.             (* [ROOTINO] *)
Require Import FileDeltas.        (* the pure legs *)
Require Import FsInitPin.         (* [INIT_INO] *)
Require Import FsShPin.           (* [SH_INO] *)
Require Import FsEchoPin.         (* [ECHO_INO] *)
Require Import FsCatPin.          (* [CAT_INO] *)
Require Import FsGrepPin.         (* [GREP_INO] *)
Require Import ConsoleInv.        (* [CONSOLE] *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  THE CONSOLE'S FACT, INDEXED BY WHAT /init's mknod DECIDED              *)
(*                                                                        *)
(*  /init's restart loop hands every child ONE credential about the       *)
(*  console ([UInitCons.init_cons_cred]): its row was MADE at inum [j]     *)
(*  ([AppEcho.cons_made]), or its key was SEALED because the mknod failed  *)
(*  ([AppEcho.cons_never]), or the era is tainted.  What the file claim's  *)
(*  consumers spend it as is always the same fact -- the console's row is *)
(*  not the one I am touching -- and the sealed arm answers it as        *)
(*  well as the made one.  So the consumers are stated at ONE fact over   *)
(*  [option Z]: present at [j], or absent.                                *)
(* ====================================================================== *)
Definition cons_fact (jo : option Z) (av : aview) : Prop :=
  match jo with
  | Some j => cons_present_at j av
  | None => cons_absent av
  end.

(* a present console pins the index: whoever is present is the flag's *)
Lemma cons_fact_present (jo : option Z) (av : aview) (j : Z) :
  cons_fact jo av -> cons_present_at j av -> jo = Some j.
Proof.
  destruct jo as [j0 |]; cbn [cons_fact]; intros H Hj.
  - pose proof (cons_present_astep j av Hj) as H1.
    pose proof (cons_present_astep j0 av H) as H2.
    rewrite H1 in H2. injection H2 as ->. reflexivity.
  - rewrite /cons_absent (cons_present_astep j av Hj) in H. discriminate H.
Qed.

Section AppFileCons.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context (c : file_fixed) (r : file_names).

  (* ---- the claim's PURE half, at both readings ---- *)
  (* [AppEcho.echo_fs_pure_acc]'s twin.  It needs no accessor at all: the
     file claim IS the taint or the pure half beside its two state
     conjuncts, so the reading is a destructuring. *)
  Lemma file_fs_pure_acc (av : aview) :
    file_pred c r av -∗
    file_pred c r av ∗ (⌜file_fs_pure av⌝ ∨ file_taint c).
  Proof using .
    rewrite /file_pred. iIntros "[#HT | (%Hp & Hcs & Hf)]".
    - iSplitR; [ by iLeft | by iRight ].
    - iSplitL "Hcs Hf"; [ | by iLeft ].
      iRight. iFrame "Hcs Hf". by iPureIntro.
  Qed.

  (* ...AND THE WEAKENING EVERY LANDED CONSUMER READS
     ([FileFsPure.file_fs_pure_echo]): [UInitSh.init_sh_slot_core] and
     [UShEcho.sh_echo_slot_of_fs_pure] are stated at [echo_fs_pure], and
     this is the one line that lets the file era feed them. *)
  Lemma file_echo_fs_pure_acc (av : aview) :
    file_pred c r av -∗
    file_pred c r av ∗ (⌜echo_fs_pure av⌝ ∨ file_taint c).
  Proof using .
    iIntros "Hp". iDestruct (file_fs_pure_acc av with "Hp") as "[Hp Hr]".
    iFrame "Hp". iDestruct "Hr" as "[%Hf | HT]"; [ | by iRight ].
    iLeft. iPureIntro. exact (file_fs_pure_echo av Hf).
  Qed.

  (* ---- THE DEED'S INUM IS NOT ONE OF THE IMAGE'S (the PROGRAM STREAM) --
     K1's entry ([UEchoFile.efile_image_entry]) takes four inequalities --
     `f`'s inode is not /init's, sh's, /echo's or cat's -- and they are the
     CLAIM's fact, not the open's: [AppFile.f_ok]'s [Some] arm pins the row
     at [i], the four image inodes' rows are pinned by [FileFsPure.
     file_fs_pure], and the contents differ by LENGTH
     ([FileDeltas.f_inum_not_pinned]).  A holder of the deed reads it in
     one destructuring, with no accessor: this is [file_fs_pure_acc] and
     [AppFile.file_deed_law] together. ---- *)
  Lemma file_deed_inum_acc (av : aview) (i : Z) (bs : list (bv 8)) :
    (length bs < EchoDisc.line_max)%nat ->
    fdeed r (Some (i, bs)) -∗ file_pred c r av -∗
    file_pred c r av ∗ fdeed r (Some (i, bs)) ∗
    (⌜i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO /\ i <> CAT_INO /\ i <> GREP_INO⌝
     ∨ file_taint c).
  Proof using .
    intros Hlen. iIntros "Hd Hp".
    iPoseProof (file_deed_law c r) as "#Hlaw".
    iDestruct (file_fs_pure_acc av with "Hp") as "[Hp Hpure]".
    iDestruct ("Hlaw" $! av (Some (i, bs)) with "Hd Hp") as "(Hp & Hd & Hres)".
    iFrame "Hp Hd".
    iDestruct "Hres" as "[[%Hok _] | #Ht]"; [ | by iRight ].
    iDestruct "Hpure" as "[%Hpure | #Ht]"; [ | by iRight ].
    iLeft. iPureIntro.
    exact (f_inum_not_pinned av i bs Hpure (proj2 Hok) Hlen).
  Qed.

  (* ---- the key's ABSENCE law ([AppEcho.echo_cons_abs_law]) ---- *)
  Lemma file_cons_abs_law :
    ⊢ □ (∀ v : aview, cons_key (fn_cons r) -∗ file_pred c r v -∗
           file_pred c r v ∗ cons_key (fn_cons r)
           ∗ (⌜cons_absent v⌝ ∨ file_taint c)).
  Proof using .
    iDestruct (echo_cons_abs_law c.1 (fn_cons r)) as "#Hl".
    iIntros "!>" (v) "Hk Hp".
    iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
    iDestruct ("Hl" $! v with "Hk He") as "(He & Hk & Hc)".
    iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    iFrame "Hk". rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the SEAL's law ([AppEcho.echo_cons_never_law]) ---- *)
  Lemma file_cons_never_law :
    ⊢ □ (cons_never (fn_cons r) -∗
           □ (∀ v : aview, file_pred c r v -∗
                file_pred c r v ∗ (⌜cons_absent v⌝ ∨ file_taint c))).
  Proof using .
    iDestruct (echo_cons_never_law c.1 (fn_cons r)) as "#Hl".
    iIntros "!> #Hn". iDestruct ("Hl" with "Hn") as "#Hl'".
    iIntros "!>" (v) "Hp".
    iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
    iDestruct ("Hl'" $! v with "He") as "[He Hc]".
    iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the SEAL STEP ([AppEcho.echo_cons_seal_step]) ---- *)
  Lemma file_cons_seal_step (av : aview) :
    cons_key (fn_cons r) -∗ file_pred c r av ==∗
      file_pred c r av ∗ (cons_never (fn_cons r) ∨ file_taint c).
  Proof using .
    iIntros "Hk Hp".
    iDestruct (file_pred_cons c r av with "Hp") as "[He Hback]".
    iMod (echo_cons_seal_step c.1 (fn_cons r) av with "Hk He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the FLAG's birth ([AppEcho.echo_cons_shoot]) ---- *)
  Lemma file_cons_shoot (av : aview) (i : Z) :
    cons_present_at i av ->
    file_pred c r av ==∗
      file_pred c r av ∗ (cons_made (fn_cons r) i ∨ file_taint c).
  Proof using .
    intros Hpr. iIntros "Hp".
    iDestruct (file_pred_cons c r av with "Hp") as "[He Hback]".
    iMod (echo_cons_shoot c.1 (fn_cons r) av i Hpr with "He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* =================================================================== *)
  (*  THE TWO MOVING-VIEW LEGS THAT DO GO THROUGH                        *)
  (*                                                                     *)
  (*  [UInitCons.init_cons_laws_at]'s (d) and (f).  Here the view MOVES,  *)
  (*  so [file_pred_cons] is useless -- it closes only at the same [av].  *)
  (*  (d) touches neither the console's ghost nor [f], so it is           *)
  (*  [AppFile.file_step_free] at four landed [FileDeltas] legs; (f) IS   *)
  (*  the console's own create, so the echo half moves by echo's own law  *)
  (*  and the file half rides across on [AppFile.file_pred_split] /       *)
  (*  [file_pred_join].                                                   *)
  (*                                                                     *)
  (*  (g) THE CREATE AT ANOTHER NAME GOES THROUGH TOO, now that the      *)
  (*  NAME PREDICATE is threaded (lane INIT-FILE, section 3.4): the       *)
  (*  bundle asks for it only at the names sys_mknod can reach, which on  *)
  (*  /init's path is [fname_console] alone -- so the parent is NOT the   *)
  (*  root and [FileDeltas.f_ok_create_other]'s disjunction is paid by    *)
  (*  its LEFT arm.  At the old premise -- a create of a device under ANY *)
  (*  name at ANY parent -- this was REFUTABLE ([f_ok] at an absent deed  *)
  (*  is [f_absent], and a create called `f` in the root makes it         *)
  (*  present).                                                          *)
  (*                                                                     *)
  (*  (e) THE UNARM GOES THROUGH TOO, now that the conjunct carries the   *)
  (*  unarmed row and its NODE: see the note at [file_cons_unarm].        *)
  (* =================================================================== *)
  Local Notation cdev := (ADev CONSOLE 0).

  Lemma file_cons_arm_nd : forall e : gmap fname Z, cdev <> ADir e.
  Proof using . exact FileDeltas.cons_dev_nondir. Qed.

  (* ---- (d) THE ARM: a row [ialloc] just took, at the console's node ---- *)
  Lemma file_cons_arm (av : aview) (i : Z) :
    av !! i = None ->
    file_pred c r av -∗ file_pred c r (delta_arm i cdev av).
  Proof using .
    intros Hfree.
    iApply (file_step_free c r av (delta_arm i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_arm i cdev av Hfree Hp)
              (fun Hab => FileDeltas.cons_absent_arm_nd i cdev av
                            file_cons_arm_nd Hab)
              (fun j Hpr => FileDeltas.cons_present_arm_nd j i cdev av
                              Hfree Hpr)
              (fun s Hok => FileDeltas.f_ok_arm i cdev av s Hfree
                              file_cons_arm_nd Hok)).
  Qed.

  (* ---- (f) THE CONSOLE'S OWN CREATE ---- *)
  Lemma file_cons_mknod (av : aview) (ents : gmap fname Z) (nl : nat)
      (i : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i cdev ->
    cons_key (fn_cons r) -∗ file_pred c r av -∗
    file_pred c r (delta_create FsImg.ROOTINO fname_console i cdev av).
  Proof using .
    intros Hpre. iIntros "Hk Hp".
    iDestruct (file_pred_split c r av with "Hp") as "[He Hres]".
    iDestruct (echo_cons_mknod c.1 (fn_cons r) av ents nl i Hpre
                 with "Hk He") as "He".
    iApply (file_pred_join c r _ with "He").
    iDestruct "Hres" as "[#Ht | [%Hp Hf]]"; [ by iLeft | ].
    iRight. iSplitR.
    { iPureIntro.
      exact (FileDeltas.file_fs_pure_create FsImg.ROOTINO fname_console
               ents nl i cdev av Hpre file_cons_arm_nd Hp). }
    iApply (f_state_mono c r av (delta_create FsImg.ROOTINO fname_console
                                   i cdev av)
              (fun s Hok =>
                 FileDeltas.f_ok_create_other FsImg.ROOTINO fname_console
                   ents nl i cdev av s Hpre file_cons_arm_nd
                   (or_intror FileDeltas.fname_console_ne_f) Hok)
              with "Hf").
  Qed.

  (* ---- (g) A CREATE AT ANOTHER (d, nm), AT THE NAMES THE SYSCALL CAN
     REACH.  The name is the last element of the path sys_mknod walked,
     which at /init's [mknod("console", …)] is [fname_console], so the
     only other create this claim is ever asked to absorb is a console
     made in a directory that is not the root.  Neither pin moves: the
     console's is guarded by [d <> ROOTINO] and the deed's by the same,
     through [FileDeltas.f_ok_create_other]'s LEFT disjunct.  No key and
     no accessor -- the view moves, so this is [AppFile.file_step_free]
     at four landed [FileDeltas] legs, exactly as (d) is. ---- *)
  Lemma file_cons_create_other (av : aview) (d : Z) (nmn : fname)
      (ents : gmap fname Z) (nl : nat) (i : Z) :
    cre_pre av d nmn ents nl i cdev ->
    nmn = fname_console ->
    d <> FsImg.ROOTINO ->
    file_pred c r av -∗
    file_pred c r (delta_create d nmn i cdev av).
  Proof using .
    intros Hpre Hnm Hd.
    iApply (file_step_free c r av (delta_create d nmn i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_create d nmn ents nl i cdev
                           av Hpre file_cons_arm_nd Hp)
              (fun Hab => FileDeltas.cons_absent_create_nd d nmn ents nl i
                            cdev av Hpre file_cons_arm_nd
                            (or_introl Hd) Hab)
              (fun j Hpr => FileDeltas.cons_present_create_nd j d nmn ents nl
                              i cdev av Hpre file_cons_arm_nd Hpr)
              (fun s Hok => FileDeltas.f_ok_create_other d nmn ents nl i cdev
                              av s Hpre file_cons_arm_nd
                              (or_introl Hd) Hok)).
  Qed.

  (* =================================================================== *)
  (*  (e) THE UNARM -- AND WHAT MAKES IT GO THROUGH                       *)
  (*                                                                     *)
  (*  [UInitCons.init_cons_laws_at]'s (e) now carries the ROW and the     *)
  (*  NODE of the row the create unarms (lane INIT-FILE, the UNARM        *)
  (*  ruling), and the node is what the file claim needs: the arm put a   *)
  (*  DEVICE there and the deed's row is a plain FILE, so the two rows    *)
  (*  cannot be the same and the deed's pin rides across untouched.  No   *)
  (*  receipt about the ARM'S VIEW could have said that -- the deed's row *)
  (*  may have been created after the arm, so [av0 !! i = None] does not  *)
  (*  separate them.                                                      *)
  (*                                                                     *)
  (*  ONE THING THE NODE DOES NOT SETTLE, and it is the reason for the    *)
  (*  extra premise below: the CONSOLE's own row.  [cons_present_at j av] *)
  (*  pins [av !! j = Some FsConsPin.cons_dev] and [cons_dev] IS          *)
  (*  [MkAnode (ADev CONSOLE 0) 1], so at [i = j] the row the unarm       *)
  (*  deletes is exactly the console's and the leg is FALSE.  Only the    *)
  (*  CREDENTIAL separates those two, which is why (e) carries [Pv av0]   *)
  (*  and [Pv av] as well; the two corollaries below are this lemma at    *)
  (*  the two credentials /init actually holds.                           *)
  (* =================================================================== *)
  Lemma file_cons_unarm (av0 av : aview) (i : Z) (cn : absnode) :
    av0 !! i = None ->
    file_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = ADev CONSOLE 0 ->
    (forall j : Z, cons_present_at j av -> i <> j) ->
    file_pred c r av -∗ file_pred c r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hsep.
    (* [i <> ROOTINO]: the root is the parent of every row the pure half
       pins, and [av0] does not have [i] at all. *)
    assert (Hroot : i <> FsImg.ROOTINO).
    { destruct (FileDeltas.file_fs_pure_pins av0 Hp0) as (H1 & _ & _ & _ & _).
      destruct (FileDeltas.node_pin_root _ _ _ av0 H1)
        as (ents & nl & Hrt & _).
      intros ->. by rewrite Hrt in Hfree. }
    (* ...AND THE DEED IS NOT THIS ROW: [f_ok av (Some (j, bs))] pins
       [av !! j] at a FILE node and the unarmed row is a DEVICE. *)
    assert (Hdeed : forall s : dst,
              f_ok av s ->
              forall (j : Z) (bs : list (bv 8)), s = Some (j, bs) -> i <> j).
    { intros s Hok j bs Hs. subst s. destruct Hok as (_ & Hrj).
      intros Hij. subst j. rewrite Hrow in Hrj.
      injection Hrj as Hnode.
      rewrite Hcn in Hnode. discriminate Hnode. }
    iApply (file_step_free c r av (delta_unarm i av)
              (fun Hp => FileDeltas.file_fs_pure_unarm_fresh i av0 av
                           Hfree Hp0 Hp)
              (fun Hab => FsConsPin.cons_absent_unarm i av Hab)
              (fun j Hpr => FsConsPin.cons_present_unarm j i av
                              (Hsep j Hpr) Hroot Hpr)
              (fun s Hok => FileDeltas.f_ok_unarm i av s Hroot
                              (Hdeed s Hok) Hok)).
  Qed.

  (* ---- at the KEY arm ([Pv := cons_absent]): the present leg is
     vacuous, because the credential says `console` does not resolve. ---- *)
  Lemma file_cons_unarm_absent (av0 av : aview) (i : Z) (cn : absnode) :
    av0 !! i = None ->
    file_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = ADev CONSOLE 0 ->
    cons_absent av ->
    file_pred c r av -∗ file_pred c r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hab.
    iApply (file_cons_unarm av0 av i cn Hfree Hp0 Hrow Hcn).
    intros j Hpr. exfalso.
    pose proof (cons_present_astep j av Hpr) as Hst.
    rewrite /cons_absent in Hab. rewrite Hab in Hst. discriminate Hst.
  Qed.

  (* ---- ...and at the FLAG arm ([Pv := cons_present_at i0]): the console
     is at [i0] in BOTH views and [av0 !! i = None] separates [i] from
     [i0], so it separates it from every inum the console resolves to. ---- *)
  Lemma file_cons_unarm_present (av0 av : aview) (i i0 : Z) (cn : absnode) :
    av0 !! i = None ->
    file_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = ADev CONSOLE 0 ->
    cons_present_at i0 av0 ->
    cons_present_at i0 av ->
    file_pred c r av -∗ file_pred c r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hpv0 Hpv.
    iApply (file_cons_unarm av0 av i cn Hfree Hp0 Hrow Hcn).
    intros j Hpr.
    assert (Hj : j = i0).
    { pose proof (cons_present_astep j av Hpr) as Hj1.
      pose proof (cons_present_astep i0 av Hpv) as Hj2.
      rewrite Hj1 in Hj2. injection Hj2 as Heq. exact Heq. }
    subst j. destruct Hpv0 as (_ & Hrow0 & _).
    intros ->. by rewrite Hrow0 in Hfree.
  Qed.

  (* ---- THE CREDENTIAL THE FILE CLAIM'S CONSUMERS TAKE ([cons_fact]'s
     iProp side): the flag at the index, with the era's taint beside it
     the way every claim law carries it.  [UInitCons.init_cons_cred] is
     [∃ jo, file_cons_cred jo] (the bridge lives with the /init tier). ---- *)
  Definition cons_flag (jo : option Z) : iProp Σ :=
    match jo with
    | Some j => cons_made (fn_cons r) j
    | None => cons_never (fn_cons r)
    end.

  Global Instance cons_flag_persistent (jo : option Z) : Persistent (cons_flag jo).
  Proof using . destruct jo; rewrite /cons_flag; apply _. Qed.

  Definition file_cons_cred (jo : option Z) : iProp Σ :=
    (cons_flag jo ∨ file_taint c)%I.

  Global Instance file_cons_cred_persistent (jo : option Z) :
    Persistent (file_cons_cred jo).
  Proof using . rewrite /file_cons_cred. apply _. Qed.

  Lemma file_cons_cred_of_made (j : Z) :
    cons_made (fn_cons r) j -∗ file_cons_cred (Some j).
  Proof using . iIntros "#H". rewrite /file_cons_cred /cons_flag. by iLeft. Qed.

  Lemma file_cons_cred_of_never :
    cons_never (fn_cons r) -∗ file_cons_cred None.
  Proof using . iIntros "#H". rewrite /file_cons_cred /cons_flag. by iLeft. Qed.

  Lemma file_cons_cred_of_taint (jo : option Z) :
    file_taint c -∗ file_cons_cred jo.
  Proof using . iIntros "#H". rewrite /file_cons_cred. by iRight. Qed.

  (* THE LAW, at both flags: [AppEcho.echo_cons_law] read through
     [AppFile.file_pred_cons] on the made arm, [file_cons_never_law] on the
     sealed one, and the taint arm answers with itself. *)
  Lemma file_cons_cred_law (jo : option Z) :
    file_cons_cred jo -∗
    □ (∀ v : aview, file_pred c r v -∗
         file_pred c r v ∗ (⌜cons_fact jo v⌝ ∨ file_taint c)).
  Proof using .
    iIntros "#[Hf | HT]"; last first.
    { iIntros "!>" (v) "Hp". iFrame "Hp". by iRight. }
    destruct jo as [j |]; iEval (rewrite /cons_flag) in "Hf"; cbn [cons_fact].
    - iDestruct (echo_cons_law c.1 (fn_cons r) j with "Hf") as "#Hl".
      iIntros "!>" (v) "Hp".
      iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
      iDestruct ("Hl" $! v with "He") as "[He Hc]".
      iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
      rewrite /file_taint. iExact "Hc".
    - iDestruct (file_cons_never_law) as "#Hn".
      iDestruct ("Hn" with "Hf") as "#Hl".
      iIntros "!>" (v) "Hp". iApply ("Hl" with "Hp").
  Qed.

End AppFileCons.
