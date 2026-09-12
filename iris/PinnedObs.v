(* ===================================================================== *)
(* PinnedObs.v -- THE PINNED OBSERVATION FAMILY, ONCE, FOR ANY SYSCALL    *)
(* WHOSE BUNDLE IS "WALK A PATH, OBSERVE THE NODE".                       *)
(*                                                                       *)
(* [PinnedExec.v] is where this construction was first written, for       *)
(* exec: an application that KNOWS which file a content-dependent         *)
(* syscall is about answers that syscall's AU families out of its own     *)
(* durable claim rather than out of the generic supply.  Three of its     *)
(* four ingredients say nothing about exec at all -- the walk cursor,     *)
(* the observation, and the step that identifies the observed node --     *)
(* so they live here, stated once, and exec's bundle is one              *)
(* instantiation of them.  (app-echo.md, "PINNING -- THE OWNER'S RULING", *)
(* rule (3): factor before the second instance.)                          *)
(*                                                                       *)
(* WHAT A PIN IS.  [Pin : aview -> Prop] is a pure claim about the        *)
(* running abstract view; [pin_resolves_at] is the part of it this file   *)
(* consumes -- one path from one cwd, the run it walks, and the NODE it   *)
(* reaches.  [FsShPin.era0_sh_pins] is an instance.                       *)
(*                                                                       *)
(* WHERE THE PIN IS READ.  Not from held [FsAbs.nview] shares -- a        *)
(* verified program holds none -- but from [AppInv.app_inv], INSIDE each  *)
(* fire.  The claim law is therefore stated DUPLICATING ([app_pred]       *)
(* comes back, because the fire puts the body back), and the TAINT [T] is *)
(* Persistent AND Timeless (the claim sits under [app_body]'s later, and  *)
(* the fires strip it).  The invariant's own half of [ghost_map_auth      *)
(* (fs_top γfs)] is what identifies the map the application speaks about  *)
(* with the map the kernel lends at the fire.                             *)
(*                                                                       *)
(* THE THREE PIECES:                                                      *)
(*                                                                       *)
(*  THE CURSOR [pobs_P] / [pobs_Pmiss]: the walk's inum at hop [k] is the *)
(*  pinned run's, or the taint.  Each hop opens [app_inv] inside its own  *)
(*  [={⊤}=∗], reads the claim, and reads the LENT entry map against the   *)
(*  invariant's authority ([pobs_elend_aents]) -- [FsAbs.apn_hop_rd]'s    *)
(*  reasoning with the pin coming from the invariant rather than from     *)
(*  held shares.  A miss is the taint: at a pinned path the entry is      *)
(*  there, so the arm is unreachable rather than false.                   *)
(*                                                                       *)
(*  THE OBSERVATION [pobs_Fo]: [FsAbsInvFire.fsabs_aopen]'s mold with the *)
(*  receipt enriched by the claim -- the row the kernel observed, beside  *)
(*  "the pins hold of the very view it observed it in, or the taint".     *)
(*                                                                       *)
(*  THE NODE [pobs_node]: the cursor at the walk's TERMINAL hop together  *)
(*  with that receipt says the observed inum is the pin's and the         *)
(*  observed node IS the pinned one -- or the taint.  This is the step a  *)
(*  syscall's own slot/receipt piece is built on: exec's arm (a) reads it *)
(*  to identify the image and its arm (b) is refuted by it.               *)
(*                                                                       *)
(* WHAT IS NOT HERE.  The syscall's own piece: exec's slot wands          *)
(* ([PinnedExec.pex_slot]), open's descriptor row.  Those read a          *)
(* contract's own definitions, so they stay at the syscall's file; what   *)
(* they take from this one is [pobs_node].                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each one IMPORTED and not
   merely required: [FileInvDefs]'s field instances ([file_app],
   [file_icfg]) are what resolve [AppInv.app_inv]'s [appcfg] and [icfg],
   and a field instance is inert wherever its module is not imported
   (durable-notes, "Typeclasses and ghost-class bundling"). *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G]: the bundle *)
Require Import FdSlots.         (* [fdslotG] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] / [icfg] fields *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBlocks.        (* [fs_names], [fs_top] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import AppCfg.          (* [app_pred] / [app_run] *)
Require Import AppInv.          (* [app_inv], [app_body], [appN] / [appE] *)
Require Import SysOpenDefs.     (* [aopen_commit_at] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import FsAbsEra.        (* [ex_start], [ex_hop], [elend], [um_start_of] *)
Require Import FsAbsDefs.       (* [arun], [arow_at], [aents], [astep], [abs_view] *)
Require Import FsAbs.           (* [astate_q_intro] (FsAbs's own rule: LAST) *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PIN, AS THE PURE INPUT                                        *)
(* ===================================================================== *)

(* What the pieces below read off the application's claim, and nothing
   else: the walk's START inum is the run's head (the C3 start rule at
   this path -- absolute paths ignore [cw], relative ones take it), the
   run's LAST inum is [ino], and at every view the claim admits the run is
   a run and [ino] holds the NODE [a].

   THE NODE, NOT A FILE: exec's pin is at [MkAnode (AFile f) nl] and a
   device pin is at [MkAnode (ADev ma mi) nl], so the node is where the
   syscalls differ and the walk is where they agree.

   Stated as a CONJUNCTION OF PURE FACTS rather than as three premises so
   that an instance is one [split_and!] over its pin lemma. *)
Definition pin_resolves_at (Pin : aview -> Prop) (cw : Z) (pl : list (bv 8))
    (hops : list Z) (ino : Z) (a : anode) : Prop :=
  um_start_of cw pl = hops !!! 0%nat
  /\ hops !!! (length (path_elems pl)) = ino
  /\ (forall v : aview,
        Pin v ->
        arun v (hops !!! 0%nat) (path_elems pl) hops
        /\ v !! ino = Some a).

Section PinnedObs.
  (* [SpecSysExec.SysExecAU]'s ghost list without the two binders nothing
     here reads.  NO [CpuId] and NO [CurCtx]: nothing is hart-indexed, and
     a pinned bundle is deliberately context-free all the way to
     [UexecRet.uslot] (SysOpenDefs' note at [aopen_commit_at]) -- a binder
     here would re-index it. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE FAMILIES                                                    *)
  (* ------------------------------------------------------------------ *)

  (* THE CURSOR: at hop [k] the walk stands on the pinned run's inum, or
     the application is already tainted. *)
  (* SPELLED AT ALL FOUR ARGUMENTS, not as a two-argument lambda: every
     consumer meets it applied, and [rewrite /pobs_P] then reduces without
     a beta step (a [/=] here would be [simpl] on a syscall-altitude
     goal). *)
  Definition pobs_P (T : iProp Σ) (hops : list Z) (k : nat) (d : Z) : iProp Σ :=
    (⌜d = hops !!! k⌝ ∨ T)%I.

  (* ...and a MISS is the taint outright: at a pinned path the entry is
     there, so this arm is only ever reached under [T]. *)
  Definition pobs_Pmiss (T : iProp Σ) (k : nat) (d : Z) : iProp Σ := T.

  (* THE OBSERVATION'S RECEIPT: the row the kernel observed, plus the pin
     AT THE VIEW IT OBSERVED IT IN.  Without the second conjunct the row
     names an arbitrary [aview] and [pobs_node] cannot identify the
     node. *)
  Definition pobs_recv (Pin : aview -> Prop) (T : iProp Σ)
      (v : aview) (i : Z) (a : anode) : iProp Σ :=
    (⌜arow_at v i a⌝ ∗ (⌜Pin v⌝ ∨ T))%I.

  (* the piece's pair: the receipt above beside the TRIVIAL refund -- the
     observation is a read, and reading the invariant spends nothing *)
  Definition pobs_Fo (Pin : aview -> Prop) (T : iProp Σ)
      : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    pfam_triv (pobs_recv Pin T).

  Global Instance pobs_P_persistent (T : iProp Σ) (hops : list Z) k d :
    Persistent T -> Persistent (pobs_P T hops k d).
  Proof. intros. rewrite /pobs_P. apply _. Qed.

  Global Instance pobs_recv_persistent (Pin : aview -> Prop) (T : iProp Σ)
      v i a :
    Persistent T -> Persistent (pobs_recv Pin T v i a).
  Proof. intros. rewrite /pobs_recv. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  READING THE LENT ENTRY MAP AGAINST THE INVARIANT'S AUTHORITY    *)
  (* ------------------------------------------------------------------ *)

  (* [FsAbsEra.elend_aents] with the reading taken straight off the
     [ghost_map_auth] rather than off an [astate] the caller holds: the
     application's invariant owns half the authority, and half is all an
     agreement needs.  This is the step [FsAbsEra.elend_astate_q]'s note
     calls "a consumer that opens ftopN INSIDE the hop's fupd" -- here the
     half comes out of [appN] instead. *)
  Lemma pobs_elend_aents (γfs : fs_names) (q : Qp) (I : gmap Z fs_node)
      (d : Z) (dq : dfrac) (ents : gmap fname Z) :
    ghost_map_auth (fs_top γfs) q I -∗
    elend (fs_gamma_L γfs) d dq ents -∗
    ⌜aents (abs_view I) d = Some ents⌝.
  Proof.
    iIntros "Hh HF".
    iDestruct (astate_q_intro (fs_gamma_L γfs) q I with "Hh") as "Hst".
    iApply (elend_aents (fs_gamma_L γfs) (abs_view I) d dq ents with "[Hst] HF").
    iApply astate_of_q. iExact "Hst".
  Qed.

  (* ...and the same reading at the STEP, which is the form the run's own
     [FsAbsDefs.arun_step_tot] is stated in.  The last line is
     [reflexivity]: [astep] IS the bind, and the lend has just named what
     it binds. *)
  Lemma pobs_elend_astep (γfs : fs_names) (q : Qp) (I : gmap Z fs_node)
      (d : Z) (dq : dfrac) (ents : gmap fname Z) (s : fname) :
    ghost_map_auth (fs_top γfs) q I -∗
    elend (fs_gamma_L γfs) d dq ents -∗
    ⌜astep (abs_view I) d s = ents !! s⌝.
  Proof.
    iIntros "Hh HF".
    iDestruct (pobs_elend_aents γfs q I d dq ents with "Hh HF") as %Hae.
    iPureIntro. rewrite /astep Hae. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE OBSERVATION                                                 *)
  (* ------------------------------------------------------------------ *)

  (* THE FIRE, and the mask discipline is the whole content: the commit is
     owed at [appE] = [↑appN], so the caller's fupd may open [appN] and
     must close it before it returns.  Inside, the kernel's lent half and
     the invariant's half AGREE on the map ([ghost_map_auth_agree]), which
     is what makes the claim -- stated about [abs_view I'] for the
     invariant's own [I'] -- a claim about the very view the receipt
     names.  The claim law is DUPLICATING because the body has to be
     closed with it still there; its output is Timeless, so the later off
     [app_body] strips inside the same fupd. *)
  Lemma pobs_aopen (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} :
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (pobs_Fo Pin T).
  Proof.
    iIntros "#Hcl #Hinv". rewrite /pobs_Fo. iApply pf_at_triv.
    rewrite /aopen_commit_at /pobs_recv. iIntros (I i a) "%Hrow Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I) ∗ (⌜Pin (abs_view I)⌝ ∨ T)))%I
      with "[Hp]" as "Hpc".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpc" as "[Hp Hc]".
    iMod "Hc".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka".
    iSplitR; [ by iPureIntro | ]. iExact "Hc".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  THE CURSOR                                                      *)
  (* ------------------------------------------------------------------ *)

  (* ONE HOP.  The pinned arm opens [appN] inside the hop's own fupd,
     reads the claim, reads the lent entry map against the invariant's
     authority, and steps the run: [arun]'s step at hop [k] is an [astep],
     which is a bind through [anode_ents], so the lent map IS the pinned
     directory's and the entry is the run's next inum.  The tainted arm
     answers both branches with [T] and opens nothing. *)
  Lemma pobs_hop (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (k : nat) (s : fname) :
    pin_resolves_at Pin cw pl hops ino a ->
    path_elems pl !! k = Some s ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_hop γfs (pobs_P T hops) (pobs_Pmiss T) k s.
  Proof.
    intros (_ & _ & Hpin) Hk. iIntros "#Hcl #Hinv".
    rewrite /ex_hop /ax_hop /pobs_P /pobs_Pmiss.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[%Hd | #HT]"; last first.
    { (* tainted: both branches are the taint *)
      iModIntro. iFrame "HF".
      destruct (ents !! s) as [c |]; [ by iRight | iExact "HT" ]. }
    subst d.
    iMod (inv_acc ⊤ appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(>Hh & Hp & >%Hdom & #Hx)".
    iAssert (▷ (app_pred app_run (abs_view I) ∗ (⌜Pin (abs_view I)⌝ ∨ T)))%I
      with "[Hp]" as "Hpc".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpc" as "[Hp Hc]".
    iMod "Hc".
    iDestruct (pobs_elend_astep γfs (1/2)%Qp I (hops !!! k) dqv ents s
                 with "Hh HF") as %Hae.
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "HF".
    iDestruct "Hc" as "[%HP | #HT]"; last first.
    { destruct (ents !! s) as [c |]; [ by iRight | iExact "HT" ]. }
    destruct (Hpin (abs_view I) HP) as [Hrun _].
    pose proof (arun_step_tot (abs_view I) (hops !!! 0%nat) (path_elems pl)
                  hops k s Hrun Hk) as Hst.
    rewrite Hae in Hst. rewrite Hst. by iLeft.
  Qed.

  (* THE WHOLE WALK, at the ONE path the pin is about.  The start rule's
     answer is the run's head, which is [pin_resolves_at]'s first conjunct;
     everything after it is [pobs_hop] under the big-op.

     THE ONE PATH IS THE LIMIT OF THIS FILE, and it is what decides which
     syscalls a pin can be handed to.  A bundle that owes the walk at EVERY
     path ([SysOpenDefs.namei_walk_pre_era]'s [∀ pl]) cannot be answered by
     a cursor that names one run's hops: at another path the cursor is
     simply false.  exec, open and mknod owe it at the ONE path their
     argument 0 names, under the reading [ArgPath.arg_path_of] -- so a pin
     goes straight in ([SpecSysExec.sys_exec_au_pre],
     [SysOpenDefs.open_au_plain_at] / [_create_at],
     [SpecSysMknod.mknod_au_at]).  chdir and unlink still carry the [∀ pl]
     form and need that seam first. *)
  Lemma pobs_walk (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_start γfs cw (pobs_P T hops) (pobs_Pmiss T) pl.
  Proof.
    intros Hres. iIntros "#Hcl #Hinv".
    pose proof Hres as Hres'. destruct Hres' as (Hstart & _ & _).
    rewrite /ex_start. iIntros (r Hr). iModIntro. iSplitR.
    { rewrite /pobs_P. iLeft. iPureIntro. by rewrite Hr Hstart. }
    rewrite /ex_hops_from /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    iApply (pobs_hop γfs Pin T cw pl hops ino a (0 + j)%nat s Hres Hj
              with "Hcl Hinv").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  THE NODE                                                        *)
  (* ------------------------------------------------------------------ *)

  (* THE IDENTIFICATION, and it is the whole reason the receipt carries the
     claim: the terminal cursor says the observed inum is the pin's, the
     receipt says the row the kernel read is the row of a view the pin
     holds of, and the pin says what that row is -- so the observed node IS
     the pinned one.  Either premise at the taint gives the taint back.

     AT VARIABLES ([FsInitPin] section 3's performance rule): the node is a
     parameter here, so no instance's literal is ever entered by this
     proof; the instances read [b = a] and take their own constructor
     apart. *)
  Lemma pobs_node (Pin : aview -> Prop) (T : iProp Σ)
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (v : aview) (i : Z) (b : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    pobs_P T hops (length (path_elems pl)) i -∗
    pobs_recv Pin T v i b -∗
    ⌜i = ino /\ b = a⌝ ∨ T.
  Proof.
    intros (_ & Hfin & Hpin).
    rewrite /pobs_P /pobs_recv.
    iIntros "HP [%Hrow Hc]".
    iDestruct "HP" as "[%Hi | HT]"; [ | iRight; iExact "HT" ].
    iDestruct "Hc" as "[%HP | HT]"; [ | iRight; iExact "HT" ].
    destruct (Hpin v HP) as [_ Hrowpin].
    rewrite Hfin in Hi. subst i.
    destruct (decide (an_nlink b = 0%nat)) as [Hz | Hnz].
    { exfalso. rewrite (arow_at_gone v ino b Hrow Hz) in Hrowpin.
      discriminate Hrowpin. }
    rewrite (arow_at_live v ino b Hrow Hnz) in Hrowpin.
    (* [Some_inj], never [injection]: at an instance the row carries the
       pinned file's literal ([FsInitPin] section 3's rule) *)
    apply Some_inj in Hrowpin.
    iLeft. iPureIntro. split; [ reflexivity | exact Hrowpin ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  THE GENERAL LEMMA                                               *)
  (* ------------------------------------------------------------------ *)

  (* THE PINNED OBSERVATION FAMILY, in one sentence: from the application's
     claim law and its invariant, a walk-shaped syscall's cursor family,
     observation piece and node identification, at the pin.  A syscall's
     own bundle is this lemma plus that syscall's own piece -- exec's slot
     wands are [PinnedExec.pex_slot], and exec's bundle
     ([PinnedExec.pinned_exec_bundle]) is the assembly. *)
  Lemma pinned_obs (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
      (* (i) THE WALK, at the one path the pin is about *)
      ex_start γfs cw (pobs_P T hops) (pobs_Pmiss T) pl
      (* (ii) THE OBSERVATION *)
      ∗ pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (pobs_Fo Pin T)
      (* (iii) THE NODE, off the terminal cursor and that observation's
         own receipt *)
      ∗ □ (∀ (v : aview) (i : Z) (b : anode),
             pobs_P T hops (length (path_elems pl)) i -∗
             pobs_recv Pin T v i b -∗ ⌜i = ino /\ b = a⌝ ∨ T).
  Proof.
    intros Hres. iIntros "#Hcl #Hinv".
    iSplitL.
    { iApply (pobs_walk γfs Pin T cw pl hops ino a Hres with "Hcl Hinv"). }
    iSplitR.
    { iApply (pobs_aopen γfs Pin T with "Hcl Hinv"). }
    iModIntro. iIntros (v i b) "HP Hr".
    iApply (pobs_node Pin T cw pl hops ino a v i b Hres with "HP Hr").
  Qed.

End PinnedObs.
