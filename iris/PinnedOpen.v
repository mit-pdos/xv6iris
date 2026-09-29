(* ===================================================================== *)
(* PinnedOpen.v -- A VERIFIED PROGRAM'S OWN open() DEPOSIT, FROM A PIN ON *)
(* THE ABSTRACT VIEW.  [PinnedExec.v] one syscall over, and its SECOND    *)
(* instantiation of [PinnedObs.pinned_obs] (app-echo.md, `PINNING -- THE  *)
(* OWNER'S RULING`, rule (3): the general lemma is the walk cursor, the   *)
(* observation and the node identification, which are exactly the same    *)
(* three here; what is open's own is its DESCRIPTOR RECEIPT).             *)
(*                                                                       *)
(* WHAT A PINNED OPEN BUYS.  open's receipt already names WHICH file was  *)
(* opened ([SpecSysOpen.open_receipt_plain]'s success existential carries *)
(* [ArgPath.arg_path_of M pv pl], PATH-ARGS) and WHICH KIND of node it    *)
(* reached -- but its device arm says only `SOME major`.  Answered at a   *)
(* pin, the walk's terminal cursor and the observation's receipt identify *)
(* the node ([PinnedObs.pobs_node]), so the arm says the descriptor is    *)
(* the PINNED device's major: for /init's open("console"), [FdDevice      *)
(* CONSOLE].  That is the row [UConsLine.ush_std_cons] needs of fd 0 and  *)
(* the reason this file exists.                                          *)
(*                                                                       *)
(* THE FILE AND DIRECTORY ARMS ARE REFUTED at the pinned node by the same *)
(* step, so the receipt collapses to `the console, or the walk missed and *)
(* [r = -1], or the taint`.                                              *)
(*                                                                       *)
(* THE TRUNCATION PIECE RIDES THE OMODE.  open's bundle owes               *)
(* [SysOpenDefs.atrunc_commit_at] only under [om_trunc vom]                *)
(* ([SysOpenDefs.open_trunc_piece]), because that is when the code runs    *)
(* [itrunc].  A pin-carrying application opening WITHOUT O_TRUNC -- /init's *)
(* [open("console", O_RDWR)] -- therefore owes nothing at all, which is    *)
(* [pinned_open_bundle_notrunc] below: no [Ft] premise, no                 *)
(* [AppInv.app_step] at a row the application pins.  At [om_trunc vom =    *)
(* true] the piece is still the caller's, and it is a premise of the       *)
(* general form -- keyed by the WALK'S TERMINAL CURSOR                     *)
(* ([SysOpenDefs.trunc_term_arg], lane TRUNC-PERMIT), which is what lets   *)
(* an open at an ABSENT pin pay it out of the taint alone                  *)
(* ([pobs_dead_trunc_piece]): the walk dies at its first hop, so the       *)
(* terminal cursor the permit hands over IS the taint.  A truncating open  *)
(* spends that cursor ([SpecSysOpen.cur_kept]), so the receipt readers    *)
(* that need it on the FILE arm take [om_trunc vom = false].               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedObs.v]'s header: a field instance is inert wherever its
   module is not imported). *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] / [icfg] fields *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBlocks.        (* [fs_names], [fs_top] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import AppCfg.          (* [app_pred] / [app_run] *)
Require Import AppInv.          (* [app_inv], [appE] *)
Require Import ArgPath.         (* [arg_path_of], [arg_path_of_uniq] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import FsAbsDefs.       (* [arow_at], [abs_view], [anode] *)
Require Import SysOpenDefs.     (* [open_au_plain_at], [aopen_commit_at],
                                   [open_trunc_piece], [open_fd_rcpt],
                                   [om_readable] / [om_writable] / [om_trunc] *)
Require Import SpecSysOpen.     (* [open_receipt_plain], [open_in] *)
Require Import PinnedObs.       (* [pin_resolves_at], [pobs_P]/[pobs_Pmiss],
                                   [pobs_Fo], [pobs_node], [pinned_obs] *)
Import Defs.

Local Open Scope Z_scope.

Section PinnedOpen.
  (* [SpecSysOpen.SysOpenArms]'s binder list, which is [PinnedObs]'s plus
     [GenId] -- [open_receipt_plain] is stated at a U-mode key and carries
     no [CurCtx] (SysOpenDefs' note at [aopen_commit_at]), so no binder
     here re-indexes the bundle. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  1.  THE BUNDLE                                                      *)
  (* ------------------------------------------------------------------ *)

  (* [PinnedObs.pinned_obs] at open's two pieces.  The walk is owed at the
     ONE path the caller's argument 0 names (PATH-ARGS: [open_au_plain_at]
     guards it with [arg_path_of], and [arg_path_of_uniq] is what lets the
     pin -- sound at one path -- answer it); the observation is the
     general lemma's; the TRUNCATION piece is the caller's, for the reason
     the header gives. *)
  Lemma pinned_open_bundle_at (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    pin_resolves_at Pin cw pl hops ino a ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_trunc_piece (fs_gamma_L γfs) vom (trunc_term_arg M pv (pobs_P T hops)) Ft -∗
    open_au_plain_at (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) Ft.
  Proof using .
    intros Hres Hpath. iIntros "#Hcl #Hinv Ht".
    iDestruct (pinned_obs γfs Pin T (pobs_Pmiss T) cw pl hops ino a Hres
                 with "[] Hcl Hinv") as "(Hw & Ho & _)";
      [ iApply pobs_miss_taint_Pmiss | ].
    rewrite /open_au_plain_at. iFrame "Ho Ht".
    iIntros (pl') "%Hpath'".
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath). iExact "Hw".
  Qed.

  (* ...and the shape a deposit site takes it at: the families are the
     bundle's business, so they leave existentially -- the form
     [UexecExecInst]'s row 15 ([SpecSysOpen.open_in] at [om_create] false)
     is stated over. *)
  Lemma pinned_open_bundle (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    pin_resolves_at Pin cw pl hops ino a ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_trunc_piece (fs_gamma_L γfs) vom (trunc_term_arg M pv (pobs_P T hops)) Ft -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) Farm Fun Fok Fex (pobs_Fo Pin T) Ft.
  Proof using .
    intros Hcr Hres Hpath. iIntros "#Hcl #Hinv Ht".
    rewrite /open_in Hcr.
    iApply (pinned_open_bundle_at γfs Pin T cw pl hops ino a M pv vom Ft
              Hres Hpath with "Hcl Hinv Ht").
  Qed.

  (* ...AND THE FORM INIT TAKES IT AT: no O_TRUNC, so the trunc piece is
     not owed and the bundle costs the pin and nothing else.  This is the
     whole point of the tightening at the application boundary -- there is
     no [Ft] premise to supply and no [AppInv.app_step] at a pinned row. *)
  Lemma pinned_open_bundle_notrunc (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    om_trunc vom = false ->
    pin_resolves_at Pin cw pl hops ino a ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) Farm Fun Fok Fex (pobs_Fo Pin T) Ft.
  Proof using .
    intros Hcr Htr Hres Hpath. iIntros "#Hcl #Hinv".
    iApply (pinned_open_bundle γfs Pin T cw pl hops ino a M pv vom Ft
              Farm Fun Fok Fex Hcr Hres Hpath with "Hcl Hinv []").
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE RECEIPT, READ AT THE PIN                                    *)
  (* ------------------------------------------------------------------ *)

  (* THE STEP OPEN'S OWN PIECE IS: the walk's terminal cursor and the
     observation's receipt identify the node ([PinnedObs.pobs_node]), so at
     a DEVICE pin the three success arms collapse -- the file and directory
     arms are refuted by the identification, and the device arm's major IS
     the pin's.  Either premise at the taint gives the taint back.

     WHAT COMES BACK ON THE SUCCESS ARM: the pure descriptor receipt
     ([SysOpenDefs.open_fd_rcpt]) at the pinned major, and the caller's
     TRUNCATION piece, unfired -- the omode has no O_TRUNC and a device is
     not truncated, so the arm hands the whole piece back.  AT
     [om_trunc vom = false]: a truncating open spends the terminal cursor
     into the permit and the FILE arm's refutation needs it (header). *)
  Lemma pinned_open_dev (γfs : fs_names)
      (omo : offmode)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (ma mi : Z) (nl : nat)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    pin_resolves_at Pin cw pl hops ino (MkAnode (ADev ma mi) nl) ->
    arg_path_of M pv pl ->
    om_trunc vom = false ->
    open_receipt_plain omo (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) Ft sts r fdv' -∗
      (* THE WALK MISSED, or the call failed after it: nothing moved *)
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝)
       (* THE CONSOLE: the descriptor is the PINNED device's *)
       ∨ (⌜open_fd_rcpt (om_readable vom) (om_writable vom) (FdDevice ma)
             sts r fdv'⌝
          ∗ open_trunc_at (fs_gamma_L γfs) vom ino Ft)
       (* ...or the application is tainted *)
       ∨ T).
  Proof using .
    intros Hres Hpath Htr. iIntros "Hrc". rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & _) | Hok]".
    { iLeft. iPureIntro. exact (conj Hr Hfd). }
    iDestruct "Hok" as (pl' av i) "(%Hpath' & HP & Harm)".
    (* THE RECEIPT'S PATH IS THE PIN'S: both are the reading of the
       caller's argument 0, and the reading is a function of it
       ([ArgPath.arg_path_of_uniq]) *)
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
    (* no O_TRUNC: the cursor is whole *)
    iEval (rewrite /cur_kept Htr) in "HP".
    iDestruct "Harm" as "[Hdev | [Hfile | Hdir]]".
    - (* DEVICE: the identification names the major *)
      iDestruct "Hdev" as (ma' mi' nl') "(%Hrow & %Hnd & Hrecv & Ht & %Hfdr)".
      iDestruct (plain_trunc_kept_forget with "Ht") as "Ht".
      iDestruct (pobs_node Pin T cw pl hops ino (MkAnode (ADev ma mi) nl)
                   av i (MkAnode (ADev ma' mi') nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [Hino Hnode]. subst i.
      injection Hnode; intros Hnl Hmi Hma.
      subst ma' mi' nl'.
      iRight. iLeft. iFrame "Ht". iPureIntro. exact Hfdr.
    - (* FILE: refuted at a device pin *)
      iDestruct "Hfile" as (bs0 nl') "(%Hrow & Hrecv & _ & _)".
      iDestruct (pobs_node Pin T cw pl hops ino (MkAnode (ADev ma mi) nl)
                   av i (MkAnode (AFile bs0) nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. discriminate Hnode.
    - (* DIRECTORY: refuted the same way *)
      iDestruct "Hdir" as (ents nl') "(%Hrow & _ & Hrecv & _ & _)".
      iDestruct (pobs_node Pin T cw pl hops ino (MkAnode (ADev ma mi) nl)
                   av i (MkAnode (ADir ents) nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. discriminate Hnode.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE OPEN THAT MUST FAIL                                         *)
  (*                                                                      *)
  (*  /init's FIRST open("console", O_RDWR), at era 0.  The claim says the *)
  (*  console node is not there yet, so the walk dies at its first hop     *)
  (*  ([PinnedObs.pobs_walk_dead]) and the call returns [-1].  What the    *)
  (*  caller gets is not a descriptor but the REFUTATION of the success    *)
  (*  fold: [pobs_P_dead]'s cursor at the walk's terminal hop IS the taint *)
  (*  ([PinnedObs.pobs_dead_term]), and [open_receipt_plain] hands that    *)
  (*  cursor back inside every success arm.                               *)
  (*                                                                      *)
  (*  THE OBSERVATION PIECE IS TRIVIAL here, and honestly so: it is never  *)
  (*  fired (the walk died before any node was locked) and its receipt is  *)
  (*  never read.                                                         *)
  (* ------------------------------------------------------------------ *)
  Lemma pinned_open_bundle_dead (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (K : iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    om_trunc vom = false ->
    pin_misses_at Pin cw pl d0 ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_free Pmiss -∗
    app_inv γfs -∗
    K -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead T d0) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof using .
    intros Hcr Htr Hres Hpath. iIntros "#Hcl #Hfree #Hinv HK".
    rewrite /open_in Hcr /open_au_plain_at.
    iSplitL "HK".
    { iIntros (pl') "%Hpath'".
      rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
      iApply (pobs_walk_dead γfs Pin T K Pmiss cw pl d0 Hres
                with "Hcl Hfree Hinv HK"). }
    iSplitR; [ iApply pobs_aopen_triv | ].
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* ...AND THE RECEIPT, READ: the call failed and the table did not move,
     or the application is tainted.  There is no third arm -- which is the
     point, and is what kills the `fd 0 is open at SOME type` arm /init's
     head carried while its first open went through the generic leaf. *)
  Lemma pinned_open_dead (γfs : fs_names) (T : iProp Σ)
      (omo : offmode)
      (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv pl ->
    path_elems pl <> [] ->
    om_trunc vom = false ->
    open_receipt_plain omo (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead T d0) Pmiss Fo Ft sts r fdv' -∗
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝) ∨ T).
  Proof using .
    intros Hpath Hne Htr. iIntros "Hrc". rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & _) | Hok]".
    { iLeft. iPureIntro. exact (conj Hr Hfd). }
    iDestruct "Hok" as (pl' av i) "(%Hpath' & HP & _)".
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
    iEval (rewrite /cur_kept Htr) in "HP".
    iRight.
    iApply (pobs_dead_term T d0 (length (path_elems pl)) i with "HP").
    intros Hz. apply Hne. by apply nil_length_inv.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3a.  THE DEAD OPEN THAT REFUNDS ITS CREDENTIAL (lane F-OPEN-2)      *)
  (*                                                                      *)
  (*  Section 3 SPENDS [K] -- [PinnedObs] section 8's hop drops it -- and  *)
  (*  /init could afford that because its console key is re-minted by the  *)
  (*  mknod.  A FRACTION OF A LIVE DEED cannot be re-minted, so cat's      *)
  (*  absent-`f` open takes [PinnedObs] section 8a's refunding walk        *)
  (*  instead: the credential rides the cursor, and both arms of the       *)
  (*  failure fold hand it back.                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma pinned_open_bundle_dead_lin_at (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (K : iProp Σ) `{!Timeless K} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    pin_misses_at Pin cw pl d0 ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_taint T Pmiss -∗
    pobs_miss_hold K Pmiss -∗
    app_inv γfs -∗
    K -∗
    (* the truncate's piece, at the dead walk's own terminal permit *)
    open_trunc_piece (fs_gamma_L γfs) vom
      (trunc_term_arg M pv (pobs_P_dead_lin T K d0)) Ft -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin T K d0) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof using .
    intros Hcr Hres Hpath. iIntros "#Hcl #Hmt #Hmh #Hinv HK Ht".
    rewrite /open_in Hcr /open_au_plain_at.
    iSplitL "HK".
    { iIntros (pl') "%Hpath'".
      rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
      iApply (pobs_walk_dead_lin γfs Pin T K Pmiss cw pl d0 Hres
                with "Hcl Hmt Hmh Hinv HK"). }
    iSplitR; [ iApply pobs_aopen_triv | ].
    iExact "Ht".
  Qed.

  (* THE PIECE AT A DEAD PIN COSTS THE TAINT AND NOTHING ELSE (lane
     TRUNC-PERMIT).  The permit is the walk's terminal cursor, and at any
     hop but the first that cursor IS the taint ([PinnedObs.
     pobs_dead_term_lin]); the taint answers for every view
     ([AppInv.app_sup]), so the step is paid out of the supply and its
     receipt is the taint again -- which is what the receipt reader below
     collects on the FILE arm. *)
  Lemma pobs_dead_trunc_piece (γfs : fs_names) (T K : iProp Σ)
      `{!Persistent T} (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    arg_path_of M pv pl ->
    path_elems pl <> [] ->
    □ (T -∗ app_sup) -∗
    open_trunc_piece (fs_gamma_L γfs) vom
      (trunc_term_arg M pv (pobs_P_dead_lin T K d0))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => T)).
  Proof using .
    intros Hpath Hne. iIntros "#Hsup". rewrite /open_trunc_piece.
    destruct (om_trunc vom); [| done].
    iApply pf_at_triv. rewrite /atrunc_of_permit. iIntros (i) "Hk".
    iDestruct (trunc_term_at_of_arg M pv pl _ i Hpath with "Hk") as "Hk".
    rewrite /trunc_term_at.
    iDestruct (pobs_dead_term_lin T K d0 (length (path_elems pl)) i
                 ltac:(intros Hz; apply Hne; by apply nil_length_inv)
                 with "Hk") as "#HT".
    iApply atrunc_commit_i_of_at.
    iApply (atrunc_commit_at_unit_pers γfs appE T with "[] HT").
    iApply ("Hsup" with "HT").
  Qed.

  (* ...so the dead open's bundle owes NO trunc piece at any mode: at the
     taint's receipt family, which is the one the piece can be paid at *)
  Lemma pinned_open_bundle_dead_lin (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (K : iProp Σ) `{!Timeless K} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    pin_misses_at Pin cw pl d0 ->
    arg_path_of M pv pl ->
    path_elems pl <> [] ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_taint T Pmiss -∗
    pobs_miss_hold K Pmiss -∗
    app_inv γfs -∗
    □ (T -∗ app_sup) -∗
    K -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin T K d0) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => T)).
  Proof using .
    intros Hcr Hres Hpath Hne. iIntros "#Hcl #Hmt #Hmh #Hinv #Hsup HK".
    iApply (pinned_open_bundle_dead_lin_at γfs Pin T K Pmiss cw pl d0 M pv vom
              _ Farm Fun Fok Fex Hcr Hres Hpath with "Hcl Hmt Hmh Hinv HK").
    iApply (pobs_dead_trunc_piece γfs T K d0 M pv vom pl Hpath Hne with "Hsup").
  Qed.

  (* ...and at a mode without O_TRUNC, at any receipt family *)
  Lemma pinned_open_bundle_dead_lin_notrunc (γfs : fs_names)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (K : iProp Σ) `{!Timeless K} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    om_trunc vom = false ->
    pin_misses_at Pin cw pl d0 ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_taint T Pmiss -∗
    pobs_miss_hold K Pmiss -∗
    app_inv γfs -∗
    K -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin T K d0) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof using .
    intros Hcr Htr Hres Hpath. iIntros "#Hcl #Hmt #Hmh #Hinv HK".
    iApply (pinned_open_bundle_dead_lin_at γfs Pin T K Pmiss cw pl d0 M pv vom
              Ft Farm Fun Fok Fex Hcr Hres Hpath with "Hcl Hmt Hmh Hinv HK").
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* ...AND THE RECEIPT, READ: the call failed and the table did not move
     AND THE CREDENTIAL IS BACK, or the application is tainted.  The one
     [={⊤}=>] is the failure fold's first arm: argstr may never have
     answered, so what comes back there is the walk one-shot itself and
     the cursor is behind its fupd ([PinnedObs.pobs_dead_start_refund]).
     AT A TRUNCATING MODE the success fold's FILE arm has spent the cursor
     ([SpecSysOpen.cur_kept]) and reports the truncate's own receipt in its
     place, so the reader asks that receipt to carry the taint -- which is
     the family the bundle above pays at; the guard makes the premise
     free at every other mode. *)
  Lemma pinned_open_dead_lin (γfs : fs_names) (T K : iProp Σ)
      (omo : offmode)
      (cw : Z) (pl : list (bv 8)) (d0 : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv pl ->
    path_elems pl <> [] ->
    (om_trunc vom = true ->
       forall (av : aview) (i : Z) (bs : list (bv 8)), Ft.(pf_recv) av i bs ⊢ T) ->
    open_receipt_plain omo (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin T K d0) (pobs_Pmiss_ref T K) Fo Ft sts r fdv'
    ={⊤}=∗ ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝ ∗ K) ∨ T).
  Proof using .
    intros Hpath Hne Hft. iIntros "Hrc". rewrite /open_receipt_plain.
    assert (Hlen : length (path_elems pl) <> 0%nat)
      by (intros Hz; apply Hne; by apply nil_length_inv).
    iDestruct "Hrc" as "[(%Hr & %Hfd & Hfail) | Hok]"; last first.
    { iDestruct "Hok" as (pl' av i) "(%Hpath' & HP & Harm)".
      rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
      iModIntro. iRight.
      (* the terminal cursor: whole, on the kept piece's refund, or -- at
         a truncating FILE arm -- spent, and the receipt is the taint *)
      iDestruct "Harm" as "[Hdev | [Hfile | Hdir]]".
      - iDestruct "Hdev" as (ma mi nl) "(_ & _ & _ & Ht & _)".
        iDestruct (plain_cur_of_kept with "HP Ht") as "HP".
        iApply (pobs_dead_term_lin T K d0 (length (path_elems pl)) i Hlen
                  with "HP").
      - iDestruct "Hfile" as (bs0 nl) "(_ & _ & Htr & _)".
        destruct (om_trunc vom) eqn:Hot.
        + iDestruct "Htr" as (av') "[_ Hrv]". iApply (Hft eq_refl av' i bs0 with "Hrv").
        + iEval (rewrite /cur_kept Hot) in "HP".
          iApply (pobs_dead_term_lin T K d0 (length (path_elems pl)) i Hlen
                    with "HP").
      - iDestruct "Hdir" as (ents nl) "(_ & _ & _ & Ht & _)".
        iDestruct (plain_cur_of_kept with "HP Ht") as "HP".
        iApply (pobs_dead_term_lin T K d0 (length (path_elems pl)) i Hlen
                  with "HP"). }
    rewrite /open_post_fail_plain.
    iDestruct "Hfail" as "[Hpre | Hrest]".
    - rewrite /open_au_plain_at. iDestruct "Hpre" as "(Hw & _ & _)".
      iDestruct ("Hw" $! pl with "[%]") as "Hst"; [ exact Hpath | ].
      iMod (pobs_dead_start_refund γfs T K (pobs_Pmiss_ref T K) cw pl d0
              with "Hst") as "Hc".
      iModIntro. iDestruct "Hc" as "[HK | HT]"; [ | by iRight ].
      iLeft. iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iExact "HK".
    - iDestruct "Hrest" as (pl') "(%Hpath' & Hr2)".
      rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
      iDestruct "Hr2" as "[Hdead | Hpost]"; last first.
      { iDestruct "Hpost" as (i) "(HP & _ & Ht)".
        iDestruct (plain_cur_of_kept with "HP Ht") as "HP".
        iModIntro. iRight.
        iApply (pobs_dead_term_lin T K d0 (length (path_elems pl)) i Hlen
                  with "HP"). }
      iDestruct "Hdead" as "(Hde & _ & _)".
      rewrite /namei_walk_dead_era.
      iDestruct "Hde" as (k d) "(%Hk & Harm)". iModIntro.
      iAssert (K ∨ T)%I with "[Harm]" as "Hc".
      { iDestruct "Harm" as "[[HP _] | [HPm _]]".
        - iApply (pobs_dead_cursor_refund with "HP").
        - iApply (pobs_dead_miss_refund with "HPm"). }
      iDestruct "Hc" as "[HK | HT]"; [ | by iRight ].
      iLeft. iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iExact "HK".
  Qed.

End PinnedOpen.
