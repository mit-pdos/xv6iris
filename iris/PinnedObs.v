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
(*  THE CURSOR [pobs_P] AND THE MISS [Pmiss]: the walk's inum at hop [k] *)
(*  is the pinned run's, or the taint.  Each hop opens [app_inv] inside   *)
(*  its own [={⊤}=∗], reads the claim, and reads the LENT entry map       *)
(*  against the invariant's authority ([pobs_elend_aents]) --             *)
(*  [FsAbs.apn_hop_rd]'s reasoning with the pin coming from the           *)
(*  invariant rather than from held shares.                              *)
(*                                                                       *)
(*  THE MISS ARM IS A PARAMETER.  At a pin that RESOLVES the entry is     *)
(*  there, so the arm is unreachable and any [Pmiss] does ([pobs_Pmiss    *)
(*  T] -- the taint -- is what exec takes).  At a pin that says the entry *)
(*  is NOT there the walk legitimately MISSES, and then the arm has to be *)
(*  payable: section 8's dead walk takes [pobs_miss_free Pmiss].  The     *)
(*  only thing every hop owes whatever the pin is, is the TAINTED branch  *)
(*  of its own cursor, which carries no view and no inum -- hence the one *)
(*  premise [pobs_miss_taint].                                           *)
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

(* ...AND THE OTHER KIND OF PIN: one that says the path is NOT THERE.
   [pin_misses_at Pin cw pl d0] is "the walk starts at [d0], and at every
   view the claim admits, the FIRST element of the path is not an entry of
   [d0]".  That is all a walk needs to die: namei's first hop misses, the
   syscall returns [-1], and no later hop and no observation ever runs.

   WHY IT IS A SEPARATE DEFINITION and not [pin_resolves_at] at some inum:
   there IS no inum.  [FsConsPin.cons_absent] is the instance -- /init's
   console at era 0, before its own mknod creates the node.

   THE CLAIM LAW THIS ONE NEEDS IS LINEAR.  "the entry is absent" is not a
   consequence of the claim alone: the claim's console conjunct has a
   PRESENT arm too, and what excludes it is an EXCLUSIVE credential the
   caller holds ([AppEcho]'s console flag is the authority side of that;
   see [UInitCons] section 7).  So section 8's law takes a resource [K] and
   hands it back, rather than being [□]-shaped over nothing. *)
Definition pin_misses_at (Pin : aview -> Prop) (cw : Z) (pl : list (bv 8))
    (d0 : Z) : Prop :=
  um_start_of cw pl = d0
  /\ (forall (v : aview) (s : fname),
        Pin v -> path_elems pl !! 0%nat = Some s -> astep v d0 s = None).

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

  (* ...and the MISS ARM exec takes: the taint outright.  At a pinned path
     the entry is there, so this arm is only ever reached under [T]. *)
  Definition pobs_Pmiss (T : iProp Σ) (k : nat) (d : Z) : iProp Σ := T.

  (* THE ONE THING EVERY HOP OWES, whatever the pin says.  A hop whose
     cursor came in TAINTED knows nothing about the entry map it was lent,
     so it may find no entry and must still answer the miss -- and all it
     holds is [T].  Every instance below pays it in one line ([pobs_Pmiss]
     is the identity, [pobs_miss_free] absorbs anything). *)
  Definition pobs_miss_taint (T : iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      : iProp Σ :=
    (□ (∀ (k : nat) (d : Z), T -∗ Pmiss k d))%I.

  Lemma pobs_miss_taint_Pmiss (T : iProp Σ) :
    ⊢ pobs_miss_taint T (pobs_Pmiss T).
  Proof. rewrite /pobs_miss_taint /pobs_Pmiss. iIntros "!>" (k d) "H". iExact "H". Qed.

  (* ...and A FREE MISS: the arm says nothing, so anybody can pay it.
     This is what a pin whose content is "the entry is NOT there" hands the
     walk -- the walk really does miss, and what the CALLER learns from the
     miss is the syscall's own [-1], not this family. *)
  Definition pobs_miss_free (Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (□ (∀ (k : nat) (d : Z), Pmiss k d))%I.

  Lemma pobs_miss_free_triv : ⊢ pobs_miss_free (fun _ _ => True%I).
  Proof. rewrite /pobs_miss_free. iIntros "!>" (k d). done. Qed.

  Lemma pobs_miss_taint_of_free (T : iProp Σ) (Pmiss : nat -> Z -> iProp Σ) :
    pobs_miss_free Pmiss -∗ pobs_miss_taint T Pmiss.
  Proof.
    rewrite /pobs_miss_free /pobs_miss_taint. iIntros "#H !>" (k d) "_".
    iApply "H".
  Qed.

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
      `{!Persistent T} `{!Timeless T} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode)
      (k : nat) (s : fname) :
    pin_resolves_at Pin cw pl hops ino a ->
    path_elems pl !! k = Some s ->
    pobs_miss_taint T Pmiss -∗
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_hop γfs (pobs_P T hops) Pmiss k s.
  Proof.
    intros (_ & _ & Hpin) Hk. iIntros "#Hmt #Hcl #Hinv".
    rewrite /ex_hop /ax_hop /pobs_P.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[%Hd | #HT]"; last first.
    { (* tainted: the hit is the taint and the miss is [pobs_miss_taint] *)
      iModIntro. iFrame "HF".
      destruct (ents !! s) as [c |]; [ by iRight | iApply ("Hmt" with "HT") ]. }
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
    { destruct (ents !! s) as [c |]; [ by iRight | iApply ("Hmt" with "HT") ]. }
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
      `{!Persistent T} `{!Timeless T} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    pobs_miss_taint T Pmiss -∗
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_start γfs cw (pobs_P T hops) Pmiss pl.
  Proof.
    intros Hres. iIntros "#Hmt #Hcl #Hinv".
    pose proof Hres as Hres'. destruct Hres' as (Hstart & _ & _).
    rewrite /ex_start. iIntros (r Hr). iModIntro. iSplitR.
    { rewrite /pobs_P. iLeft. iPureIntro. by rewrite Hr Hstart. }
    rewrite /ex_hops_from /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    iApply (pobs_hop γfs Pin T Pmiss cw pl hops ino a (0 + j)%nat s Hres Hj
              with "Hmt Hcl Hinv").
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
      `{!Persistent T} `{!Timeless T} (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    pobs_miss_taint T Pmiss -∗
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
      (* (i) THE WALK, at the one path the pin is about *)
      ex_start γfs cw (pobs_P T hops) Pmiss pl
      (* (ii) THE OBSERVATION *)
      ∗ pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (pobs_Fo Pin T)
      (* (iii) THE NODE, off the terminal cursor and that observation's
         own receipt *)
      ∗ □ (∀ (v : aview) (i : Z) (b : anode),
             pobs_P T hops (length (path_elems pl)) i -∗
             pobs_recv Pin T v i b -∗ ⌜i = ino /\ b = a⌝ ∨ T).
  Proof.
    intros Hres. iIntros "#Hmt #Hcl #Hinv".
    iSplitL.
    { iApply (pobs_walk γfs Pin T Pmiss cw pl hops ino a Hres with "Hmt Hcl Hinv"). }
    iSplitR.
    { iApply (pobs_aopen γfs Pin T with "Hcl Hinv"). }
    iModIntro. iIntros (v i b) "HP Hr".
    iApply (pobs_node Pin T cw pl hops ino a v i b Hres with "HP Hr").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  8.  THE DEAD WALK: a pin that says the path is not there            *)
  (*                                                                      *)
  (*  /init's FIRST open("console") at era 0.  The application's claim     *)
  (*  says the console node does not exist yet ([FsConsPin.cons_absent]),  *)
  (*  so the walk MISSES at its first hop and the call returns [-1].  What *)
  (*  this buys is not a receipt -- it is the REFUTATION of the success    *)
  (*  arm: the cursor below is the start rule AND NOTHING ELSE, so the     *)
  (*  cursor the receipt hands back at the walk's terminal hop is the      *)
  (*  TAINT, and a syscall's whole success fold collapses to it            *)
  (*  ([PinnedOpen.pinned_open_dead]).                                     *)
  (*                                                                      *)
  (*  THE MISS ARM MUST BE FREE HERE, and that is what the [Pmiss]         *)
  (*  parameter is for: this walk really does miss, so [pobs_Pmiss T] --   *)
  (*  the taint -- is unpayable and [fun _ _ => True] is the instance.     *)
  (* ------------------------------------------------------------------ *)

  (* THE CURSOR: hop 0 stands on the start inum; every later hop, and the
     terminal one, is the taint.  (A later hop is only ever reached under
     the taint anyway -- the walk died at hop 0.) *)
  Definition pobs_P_dead (T : iProp Σ) (d0 : Z) (k : nat) (d : Z) : iProp Σ :=
    (⌜k = 0%nat /\ d = d0⌝ ∨ T)%I.

  Global Instance pobs_P_dead_persistent (T : iProp Σ) d0 k d :
    Persistent T -> Persistent (pobs_P_dead T d0 k d).
  Proof. intros. rewrite /pobs_P_dead. apply _. Qed.

  (* THE TERMINAL READING, and the whole point of the shape: at any hop but
     the first the cursor IS the taint. *)
  Lemma pobs_dead_term (T : iProp Σ) (d0 : Z) (n : nat) (d : Z) :
    (n <> 0)%nat -> pobs_P_dead T d0 n d -∗ T.
  Proof.
    intros Hn. rewrite /pobs_P_dead.
    iIntros "[%Hp | HT]"; [ destruct Hp as [Hk _]; destruct (Hn Hk) | iExact "HT" ].
  Qed.

  (* HOP 0: the claim says the entry is not there, the lent entry map IS
     the start inum's ([pobs_elend_astep]), so the hop takes the MISS
     branch and pays it out of the free supply. *)
  Lemma pobs_hop_dead (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (K : iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z) (s : fname) :
    pin_misses_at Pin cw pl d0 ->
    path_elems pl !! 0%nat = Some s ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_free Pmiss -∗
    app_inv γfs -∗
    K -∗
    ex_hop γfs (pobs_P_dead T d0) Pmiss 0%nat s.
  Proof.
    intros (_ & Hmiss) Hs. iIntros "#Hcl #Hfree #Hinv HK".
    rewrite /ex_hop /ax_hop /pobs_P_dead /pobs_miss_free.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[%Hpd | #HT]"; last first.
    { iModIntro. iFrame "HF".
      destruct (ents !! s) as [c |]; [ by iRight | iApply "Hfree" ]. }
    destruct Hpd as [_ Hd]. subst d.
    iMod (inv_acc ⊤ appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(>Hh & Hp & >%Hdom & #Hx)".
    iAssert (▷ (app_pred app_run (abs_view I) ∗ K ∗ (⌜Pin (abs_view I)⌝ ∨ T)))%I
      with "[Hp HK]" as "Hpc".
    { iNext. iApply ("Hcl" with "HK Hp"). }
    iDestruct "Hpc" as "[Hp [HK Hc]]".
    iMod "Hc".
    iDestruct (pobs_elend_astep γfs (1/2)%Qp I d0 dqv ents s
                 with "Hh HF") as %Hae.
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "HF".
    iDestruct "Hc" as "[%HP | #HT]"; last first.
    { destruct (ents !! s) as [c |]; [ by iRight | iApply "Hfree" ]. }
    assert (Hn : ents !! s = None)
      by (rewrite -Hae; exact (Hmiss (abs_view I) s HP Hs)).
    rewrite Hn. iApply "Hfree".
  Qed.

  (* ...AND EVERY LATER HOP, which is reached only under the taint: the
     cursor hands it over and the hop opens nothing. *)
  Lemma pobs_hop_dead_hi (γfs : fs_names) (T : iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (d0 : Z) (k : nat) (s : fname) :
    (k <> 0)%nat ->
    pobs_miss_free Pmiss -∗ ex_hop γfs (pobs_P_dead T d0) Pmiss k s.
  Proof.
    intros Hk. iIntros "#Hfree".
    rewrite /ex_hop /ax_hop /pobs_P_dead /pobs_miss_free.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[%Hpd | HT]";
      [ destruct Hpd as [Hz _]; destruct (Hk Hz) | ].
    iModIntro. iFrame "HF".
    destruct (ents !! s) as [c |]; [ by iRight | iApply "Hfree" ].
  Qed.

  (* THE WHOLE WALK, at the one path the pin is about. *)
  Lemma pobs_walk_dead (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (K : iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ)
      (cw : Z) (pl : list (bv 8)) (d0 : Z) :
    pin_misses_at Pin cw pl d0 ->
    □ (∀ v : aview, K -∗ app_pred app_run v -∗
                      app_pred app_run v ∗ K ∗ (⌜Pin v⌝ ∨ T)) -∗
    pobs_miss_free Pmiss -∗
    app_inv γfs -∗
    K -∗
    ex_start γfs cw (pobs_P_dead T d0) Pmiss pl.
  Proof.
    intros Hres. pose proof Hres as [Hstart _].
    iIntros "#Hcl #Hfree #Hinv HK".
    rewrite /ex_start. iIntros (r Hr). iModIntro. iSplitR "HK".
    { rewrite /pobs_P_dead. iLeft. iPureIntro.
      split; [ reflexivity | by rewrite Hr ]. }
    rewrite /ex_hops_from /ax_hops_from drop_0.
    destruct (path_elems pl) as [| s0 rest] eqn:Hpe; [ done | ].
    rewrite big_sepL_cons. iSplitL "HK".
    - iApply (pobs_hop_dead γfs Pin T K Pmiss cw pl d0 s0 Hres
                ltac:(rewrite Hpe; reflexivity) with "Hcl Hfree Hinv HK").
    - iApply big_sepL_intro. iIntros "!>" (j s Hj).
      iApply (pobs_hop_dead_hi γfs T Pmiss d0 (0 + S j)%nat s
                ltac:(lia) with "Hfree").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  9.  THE OBSERVATION A DEAD WALK OWES: nothing                       *)
  (*                                                                      *)
  (*  A bundle owes its observation piece whether or not the walk will     *)
  (*  reach it, so the dead walk still has to hand one in -- and since its *)
  (*  receipt is never read (the cursor has already collapsed the success  *)
  (*  fold to the taint), the TRIVIAL family does.  [SysOpenDefs.          *)
  (*  aopen_commit_at_unit] is this without the [pf_at] wrapper and with a *)
  (*  [CurCtx] binder this section does not have.                          *)
  (* ------------------------------------------------------------------ *)
  Lemma pobs_aopen_triv (γfs : fs_names) :
    ⊢ pf_at (aopen_commit_at (fs_gamma_L γfs) appE)
        (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)).
  Proof.
    iApply pf_at_triv. rewrite /aopen_commit_at.
    iIntros (I i a) "%Hrow Hka". iModIntro. by iFrame "Hka".
  Qed.

End PinnedObs.
