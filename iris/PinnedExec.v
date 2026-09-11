(* ===================================================================== *)
(* PinnedExec.v -- A VERIFIED PROGRAM'S OWN exec BUNDLE, from a PIN on    *)
(* the abstract file system.                                             *)
(*                                                                       *)
(* [UkRun.uxsup] -- exec's deposit at EVERY key -- is what a program that *)
(* answers for nothing runs on: the generic family pays both slot wands   *)
(* out of the supply, so the exec'd image may be anything and the WP that *)
(* comes back promises nothing.  A program that KNOWS which file it is    *)
(* about to run pays instead out of its application's own claim, and this *)
(* file is the assembly.                                                  *)
(*                                                                       *)
(* WHAT A PIN IS HERE.  [Pin : aview -> Prop] is a pure claim about the   *)
(* running abstract view; [pin_resolves] is the part of it this file      *)
(* consumes -- one path from one cwd, the run it walks, and the node it   *)
(* reaches.  [FsShPin.era0_sh_pins] is the instance /sh is pinned at.     *)
(*                                                                       *)
(* WHERE THE PIN IS READ.  Not from held [FsAbs.nview] shares -- a        *)
(* verified program holds none -- but from [AppInv.app_inv], INSIDE each  *)
(* fire.  The claim law is therefore stated DUPLICATING                   *)
(* ([app_pred] comes back, because the fire puts the body back), and the  *)
(* TAINT [T] is Persistent AND Timeless (the claim sits under             *)
(* [app_body]'s later, and the fires strip it).  The invariant's own half *)
(* of [ghost_map_auth (fs_top γfs)] is what identifies the map the        *)
(* application speaks about with the map the kernel lends at the fire.    *)
(*                                                                       *)
(* THE THREE PIECES, one per conjunct of                                  *)
(* [SpecSysExec.sys_exec_au_pre]:                                         *)
(*                                                                       *)
(*  THE CURSOR [pex_P] / [pex_Pmiss]: the walk's inum at hop [k] is the   *)
(*  pinned run's, or the taint.  Each hop opens [app_inv] inside its own  *)
(*  [={⊤}=∗], reads the claim, and reads the LENT entry map against the   *)
(*  invariant's authority ([pex_elend_aents]) -- [FsAbs.apn_hop_rd]'s     *)
(*  reasoning with the pin coming from the invariant rather than from     *)
(*  held shares.  A miss is the taint: at a pinned path there is none,    *)
(*  and the arm is unreachable rather than false.                         *)
(*                                                                       *)
(*  THE OBSERVATION [pex_Fo]: [FsAbsInvFire.fsabs_aopen]'s mold with the  *)
(*  receipt enriched by the claim -- the row the kernel observed, beside  *)
(*  "the pins hold of the very view it observed it in, or the taint".     *)
(*                                                                       *)
(*  THE SLOT PIECE [pex_slot]: arm (a) reads the cursor at the walk's     *)
(*  terminal hop together with the receipt, so the observed node IS the   *)
(*  pinned file and the caller's constructor answers from                 *)
(*  [kexec_image_ok]; arm (b) is REFUTED by the same pair, since a pinned *)
(*  file is loadable.  Either arm at the taint goes to the generic slot.  *)
(*                                                                       *)
(* THE REFUND is the payload [Pay].  exec can fail -- the file is there   *)
(* and the arguments do not fit, or a page cannot be allocated -- and the *)
(* process resumes on its own slot, so what the construction SPENT has to *)
(* come back (fs-syscall-specs.md section 4).  The walk and the           *)
(* observation spend nothing but persistent facts.                        *)
(*                                                                       *)
(* THE PATH IS PINNED TOO.  [sys_exec_au_pre] owes the walk and the slot  *)
(* at every [pl] with [exec_path_of M pv pl] -- the string the caller's   *)
(* own image holds at its argument-0 pointer -- and that reading is a     *)
(* FUNCTION of [(M, pv)] ([SpecSysExec.exec_path_of_uniq]), so a caller   *)
(* that knows its image owes the walk at exactly one path.  The premise   *)
(* [exec_path_of M pv pl] is therefore the third pure input here, and a   *)
(* program-side supplier discharges it against its own read-only image.   *)
(*                                                                       *)
(* AND SO IS THE ARGUMENT VECTOR.  The slot wand's second pure input is   *)
(* [SpecSysExec.exec_args_of M av na alen afun], the twin reading at      *)
(* argument 1: not merely a vector of the right shape, but the pointers   *)
(* the caller's own image holds at [av + 8 i] and the strings they name.  *)
(* That is a STRONGER gift to the exec'd program's constructor -- sh's    *)
(* ROOM premise needs [na] and [alen] to price its frames, which a bare   *)
(* shape cannot supply -- and [SpecSysExec.exec_args_of_shape] recovers   *)
(* the shape wherever a consumer wants only that.                         *)
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
Require Import UserFd.          (* [ufdG] *)
Require Import ChildTok.        (* [my_pay]: the exec wands' pay fact *)
Require Import UexecSlot.       (* [uvis] *)
Require Import ElfFile.         (* [elf_bytes] *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBlocks.        (* [fs_names], [fs_top] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import AppCfg.          (* [app_pred] / [app_run] *)
Require Import AppInv.          (* [app_inv], [app_body], [appN] / [appE] *)
Require Import SysOpenDefs.     (* [aopen_commit_at] *)
Require Import SpecKexec.       (* [exec_slot_pre], [kexec_loadable], [anode_loadable] *)
Require Import SpecSysExec.     (* [sys_exec_au_pre], [exec_path_of_uniq] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import FsAbsEra.        (* [ex_start], [ex_hop], [elend], [um_start_of] *)
Require Import FsAbsDefs.       (* [arun], [arow_at], [aents], [astep], [abs_view] *)
Require Import FsAbs.           (* [astate_q_intro] (FsAbs's own rule: LAST) *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PIN, AS THE PURE INPUT                                        *)
(* ===================================================================== *)

(* What the three pieces read off the application's claim, and nothing
   else: the walk's START inum is the run's head (the C3 start rule at
   this path -- absolute paths ignore [cw], relative ones take it), the
   run's LAST inum is [ino], and at every view the claim admits the run
   is a run and [ino] holds the file [f] at nlink [nl].

   Stated as a CONJUNCTION OF PURE FACTS rather than as three premises so
   that an instance is one [split_and!] over its pin lemma
   ([FsShPin.era0_sh_pins] is exactly the second and third conjuncts of
   the [forall v] arm, at [hops := [ROOTINO; SH_INO]]). *)
Definition pin_resolves (Pin : aview -> Prop) (cw : Z) (pl : list (bv 8))
    (hops : list Z) (ino : Z) (f : elf_bytes) (nl : nat) : Prop :=
  um_start_of cw pl = hops !!! 0%nat
  /\ hops !!! (length (path_elems pl)) = ino
  /\ (forall v : aview,
        Pin v ->
        arun v (hops !!! 0%nat) (path_elems pl) hops
        /\ v !! ino = Some (MkAnode (AFile f) nl)).

Section PinnedExec.
  (* [SpecSysExec.SysExecAU]'s ghost list verbatim.  NO [CpuId] and NO
     [CurCtx]: nothing here is hart-indexed, and the exec bundle is
     deliberately context-free all the way to [UexecRet.uslot]
     (SysOpenDefs' note at [aopen_commit_at]) -- a binder here would
     re-index it. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE THREE FAMILIES                                             *)
  (* ------------------------------------------------------------------ *)

  (* THE CURSOR: at hop [k] the walk stands on the pinned run's inum, or
     the application is already tainted. *)
  (* SPELLED AT ALL FOUR ARGUMENTS, not as a two-argument lambda: every
     consumer meets it applied, and [rewrite /pex_P] then reduces without a
     beta step (a [/=] here would be [simpl] on a syscall-altitude goal). *)
  Definition pex_P (T : iProp Σ) (hops : list Z) (k : nat) (d : Z) : iProp Σ :=
    (⌜d = hops !!! k⌝ ∨ T)%I.

  (* ...and a MISS is the taint outright: at a pinned path the entry is
     there, so this arm is only ever reached under [T]. *)
  Definition pex_Pmiss (T : iProp Σ) (k : nat) (d : Z) : iProp Σ := T.

  (* THE OBSERVATION'S RECEIPT: the row the kernel observed, plus the pin
     AT THE VIEW IT OBSERVED IT IN.  Without the second conjunct the row
     names an arbitrary [aview] and the slot piece cannot identify the
     file. *)
  Definition pex_recv (Pin : aview -> Prop) (T : iProp Σ)
      (v : aview) (i : Z) (a : anode) : iProp Σ :=
    (⌜arow_at v i a⌝ ∗ (⌜Pin v⌝ ∨ T))%I.

  (* the piece's pair: the receipt above beside the TRIVIAL refund -- the
     observation is a read, and reading the invariant spends nothing *)
  Definition pex_Fo (Pin : aview -> Prop) (T : iProp Σ)
      : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    pfam_triv (pex_recv Pin T).

  Global Instance pex_P_persistent (T : iProp Σ) (hops : list Z) k d :
    Persistent T -> Persistent (pex_P T hops k d).
  Proof. intros. rewrite /pex_P. apply _. Qed.

  Global Instance pex_recv_persistent (Pin : aview -> Prop) (T : iProp Σ)
      v i a :
    Persistent T -> Persistent (pex_recv Pin T v i a).
  Proof. intros. rewrite /pex_recv. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  READING THE LENT ENTRY MAP AGAINST THE INVARIANT'S AUTHORITY    *)
  (* ------------------------------------------------------------------ *)

  (* [FsAbsEra.elend_aents] with the reading taken straight off the
     [ghost_map_auth] rather than off an [astate] the caller holds: the
     application's invariant owns half the authority, and half is all an
     agreement needs.  This is the step [FsAbsEra.elend_astate_q]'s note
     calls "a consumer that opens ftopN INSIDE the hop's fupd" -- here the
     half comes out of [appN] instead. *)
  Lemma pex_elend_aents (γfs : fs_names) (q : Qp) (I : gmap Z fs_node)
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
  Lemma pex_elend_astep (γfs : fs_names) (q : Qp) (I : gmap Z fs_node)
      (d : Z) (dq : dfrac) (ents : gmap fname Z) (s : fname) :
    ghost_map_auth (fs_top γfs) q I -∗
    elend (fs_gamma_L γfs) d dq ents -∗
    ⌜astep (abs_view I) d s = ents !! s⌝.
  Proof.
    iIntros "Hh HF".
    iDestruct (pex_elend_aents γfs q I d dq ents with "Hh HF") as %Hae.
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
  Lemma pex_aopen (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} :
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (pex_Fo Pin T).
  Proof.
    iIntros "#Hcl #Hinv". rewrite /pex_Fo. iApply pf_at_triv.
    rewrite /aopen_commit_at /pex_recv. iIntros (I i a) "%Hrow Hka".
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
  Lemma pex_hop (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (k : nat) (s : fname) :
    pin_resolves Pin cw pl hops ino f nl ->
    path_elems pl !! k = Some s ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_hop γfs (pex_P T hops) (pex_Pmiss T) k s.
  Proof.
    intros (_ & _ & Hpin) Hk. iIntros "#Hcl #Hinv".
    rewrite /ex_hop /ax_hop /pex_P /pex_Pmiss.
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
    iDestruct (pex_elend_astep γfs (1/2)%Qp I (hops !!! k) dqv ents s
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
     answer is the run's head, which is [pin_resolves]'s first conjunct;
     everything after it is [pex_hop] under the big-op. *)
  Lemma pex_walk (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) :
    pin_resolves Pin cw pl hops ino f nl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    ex_start γfs cw (pex_P T hops) (pex_Pmiss T) pl.
  Proof.
    intros Hres. iIntros "#Hcl #Hinv".
    pose proof Hres as Hres'. destruct Hres' as (Hstart & _ & _).
    rewrite /ex_start. iIntros (r Hr). iModIntro. iSplitR.
    { rewrite /pex_P. iLeft. iPureIntro. by rewrite Hr Hstart. }
    rewrite /ex_hops_from /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    iApply (pex_hop γfs Pin T cw pl hops ino f nl (0 + j)%nat s Hres Hj
              with "Hcl Hinv").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  THE SLOT PIECE                                                  *)
  (* ------------------------------------------------------------------ *)

  (* ARM (a) IDENTIFIES THE FILE and arm (b) is REFUTED, and both do it
     from the SAME pair: the walk's terminal cursor says the observed inum
     is the pin's, the receipt says the row the kernel read is the row of
     a view the pin holds of, and the pin says what that row is.  So
     [f' = f] on (a) -- and the caller's constructor answers from
     [kexec_image_ok f] -- while on (b) the observed node is a loadable
     file and [~ anode_loadable a] is absurd.  Either premise at the taint
     is paid by the generic slot.

     [Pay] goes to ARM (a) ONLY: arm (b) never returns and needs nothing
     but the persistent facts.  The refund is [Pay] itself, and the [∧]
     of [pf_at] is what lets the same payload answer both. *)
  Lemma pex_slot (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ)
      (* THE EXEC'D PROCESS'S PAYLOAD.  The kernel hands the slot wands the
         exec'ing process's own [ChildTok.my_pay] at it ([SpecKexec.
         exec_slot_pre]) -- exec keeps the generation, so it is the fact
         the NEW image's constructor needs -- and both arms below relay it,
         the pinned one to the caller's constructor and the tainted one to
         the generic family. *)
      (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    (* THE TAINT ARM TAKES THE KEY FIRST AND THE PAY FACT BESIDE [T]: a
       tainted process runs on the GENERIC family, which is itself indexed
       by the pay fact ([UexecExecMint.uslot_mint]), so the arm cannot be
       "[T] gives a slot at every key" any more -- it is "[T] and this
       key's payload give a slot at this key". *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    pf_at (fun S => sys_exec_slot_pre S Q (pex_P T hops) (pex_recv Pin T)
                      M pv av sts) (MkPfam X Pay).
  Proof.
    intros Hres Hload Hpath. iIntros "#Hcon #Hgen HPay".
    destruct Hres as (_ & Hfin & Hpin).
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [ | iExact "HPay" ].
    rewrite /sys_exec_slot_pre. iIntros (pl' na alen afun) "%Hpath' %Hargs".
    rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
    rewrite /exec_slot_pre /pex_P /pex_recv. iSplitL "HPay".
    - (* ---- ARM (a): the observed node IS the pinned file ---- *)
      iIntros (av' i f' nl' W') "HP [%Hrow Hc] %Hload' %Hok #Hp".
      iDestruct "HP" as "[%Hi | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp"). }
      iDestruct "Hc" as "[%HP | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp"). }
      destruct (Hpin av' HP) as [_ Hrowpin].
      rewrite Hfin in Hi. subst i.
      destruct (decide (nl' = 0%nat)) as [Hz | Hnz].
      { exfalso. rewrite (arow_at_gone av' ino _ Hrow Hz) in Hrowpin.
        discriminate Hrowpin. }
      rewrite (arow_at_live av' ino _ Hrow Hnz) in Hrowpin.
      simplify_eq.
      iApply ("Hcon" $! na alen afun W' with "[%] [%] Hp HPay");
        [ exact Hok | exact Hargs ].
    - (* ---- ARM (b): a pinned file IS loadable, so this arm is dead ---- *)
      iIntros (av' i a W') "HP [%Hrow Hc] %Hnload %Hkey #Hp".
      iDestruct "HP" as "[%Hi | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp"). }
      iDestruct "Hc" as "[%HP | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp"). }
      destruct (Hpin av' HP) as [_ Hrowpin].
      rewrite Hfin in Hi. subst i.
      destruct (decide (an_nlink a = 0%nat)) as [Hz | Hnz].
      { exfalso. rewrite (arow_at_gone av' ino a Hrow Hz) in Hrowpin.
        discriminate Hrowpin. }
      rewrite (arow_at_live av' ino a Hrow Hnz) in Hrowpin.
      simplify_eq.
      exfalso. apply Hnload. exists f, nl.
      split; [ reflexivity | exact Hload ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  THE BUNDLE                                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma pinned_exec_bundle_at (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* the pin, as a law over the application's claim *)
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    (* the exec'd program's slot at every key the image fact admits *)
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    (* the taint's generic slot, indexed by the pay fact -- see [pex_slot] *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw Q
      (pex_P T hops) (pex_Pmiss T) (pex_Fo Pin T) M pv av sts.
  Proof.
    intros Hres Hload Hpath.
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    rewrite /sys_exec_au_pre. iSplitR.
    { iIntros (pl') "%Hpath'".
      rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
      iApply (pex_walk γfs Pin T cw pl hops ino f nl Hres with "Hcl Hinv"). }
    iSplitR.
    { iApply (pex_aopen γfs Pin T with "Hcl Hinv"). }
    rewrite /pex_Fo /pfam_triv. cbn [pf_recv].
    iApply (pex_slot γfs X Pin T cw pl hops ino f nl Pay Q M pv av sts
              Hres Hload Hpath with "Hcon Hgen HPay").
  Qed.

  (* ...and the shape a deposit site takes it at: the families are the
     bundle's business, so they leave existentially
     ([UexecExecInst.sbundle_exec_intro] takes exactly this quadruple). *)
  Lemma pinned_exec_bundle (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (R : iProp Σ),
      sys_exec_au_pre (MkPfam X R) (fs_gamma_L γfs) γfs cw Q P Pmiss Fo
        M pv av sts.
  Proof.
    intros Hres Hload Hpath. iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iExists (pex_P T hops), (pex_Pmiss T), (pex_Fo Pin T), Pay.
    iApply (pinned_exec_bundle_at γfs X Pin T cw pl hops ino f nl Pay Q
              M pv av sts Hres Hload Hpath with "Hcl Hinv Hcon Hgen HPay").
  Qed.

End PinnedExec.
