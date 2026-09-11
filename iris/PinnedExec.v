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
(* [SpecSysExec.sys_exec_au_pre], and TWO OF THEM ARE NOT EXEC'S.  The    *)
(* cursor ([PinnedObs.pobs_P] / [pobs_Pmiss]) and the observation         *)
(* ([PinnedObs.pobs_Fo], fired by [pobs_aopen]) say nothing about which   *)
(* syscall is walking, so they are stated once in [PinnedObs.v] -- with   *)
(* the walk [pobs_walk] and the step [pobs_node] that reads the observed  *)
(* node off the terminal cursor and the receipt.  This file is exec's own *)
(* third piece and the assembly:                                          *)
(*                                                                       *)
(*  THE SLOT PIECE [pex_slot]: arm (a) reads [PinnedObs.pobs_node] at the *)
(*  walk's terminal hop together with the receipt, so the observed node   *)
(*  IS the pinned file and the caller's constructor answers from          *)
(*  [kexec_image_ok]; arm (b) is REFUTED by the same step, since a pinned *)
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
Require Import PinnedObs.       (* the pinned observation family, factored:
                                   [pin_resolves_at], [pobs_P]/[pobs_Pmiss],
                                   [pobs_recv]/[pobs_Fo], [pinned_obs] *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PIN, AS THE PURE INPUT                                        *)
(* ===================================================================== *)

(* [PinnedObs.pin_resolves_at] AT A FILE NODE, which is the only shape exec
   can use: the walk's START inum is the run's head (the C3 start rule at
   this path -- absolute paths ignore [cw], relative ones take it), the
   run's LAST inum is [ino], and at every view the claim admits the run
   is a run and [ino] holds the file [f] at nlink [nl].

   Stated as a CONJUNCTION OF PURE FACTS rather than as three premises so
   that an instance is one [split_and!] over its pin lemma
   ([FsShPin.era0_sh_pins] is exactly the second and third conjuncts of
   the [forall v] arm, at [hops := [ROOTINO; SH_INO]]). *)
Definition pin_resolves (Pin : aview -> Prop) (cw : Z) (pl : list (bv 8))
    (hops : list Z) (ino : Z) (f : elf_bytes) (nl : nat) : Prop :=
  pin_resolves_at Pin cw pl hops ino (MkAnode (AFile f) nl).

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
  (*  2-5.  THE WALK, THE OBSERVATION AND THE NODE: [PinnedObs]           *)
  (*                                                                      *)
  (*  The cursor family [PinnedObs.pobs_P] / [pobs_Pmiss], the observation *)
  (*  [pobs_Fo] and its fire [pobs_aopen], the per-hop step [pobs_hop] and *)
  (*  the walk [pobs_walk], and the identification [pobs_node] are stated  *)
  (*  ONCE THERE, over any syscall whose bundle is "walk a path, observe   *)
  (*  the node" -- they were written here first and say nothing about      *)
  (*  exec.  What is left in this file is exec's OWN piece: the two slot   *)
  (*  wands below, and the bundle that assembles them with the general     *)
  (*  lemma.                                                              *)
  (* ------------------------------------------------------------------ *)

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
      (* ...AND THE PAYLOAD ITSELF rides with the pay fact, at the kill
         status, because exec KEEPS THE PROCESS: the image that starts here
         runs at the exec'ing process's own generation and its own payload,
         so its run carries [Q (-1)] between traps like any other
         ([UkRun.urun]'s conjunct, which [UkRun.uslot_of_urun_all] takes).
         The one copy in the system is the payment the dispatcher holds
         across the exec trap ([SpecSyscall.sysc_pay_in]); it reaches these
         wands through [SpecKexec.exec_slot_pre] and both arms hand it on --
         the pinned arm to the caller's constructor beside the linear [Pay],
         the tainted arm to the generic family, which runs at the trivial
         payload and drops it.  This is the seam a NON-TRIVIAL payload
         crosses: [Q] is a parameter here, so an application whose exec'd
         image must own something (sh and the console reader) states it. *)
      (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Q (-1) -∗ Pay -∗ X W') -∗
    (* THE TAINT ARM TAKES THE KEY FIRST AND THE PAY FACT BESIDE [T]: a
       tainted process runs on the GENERIC family, which is itself indexed
       by the pay fact ([UexecExecMint.uslot_mint]), so the arm cannot be
       "[T] gives a slot at every key" any more -- it is "[T] and this
       key's payload give a slot at this key". *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ Q (-1) -∗ X W') -∗
    Pay -∗
    pf_at (fun S => sys_exec_slot_pre S Q (pobs_P T hops) (pobs_recv Pin T)
                      M pv av sts) (MkPfam X Pay).
  Proof.
    intros Hres Hload Hpath. iIntros "#Hcon #Hgen HPay".
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [ | iExact "HPay" ].
    rewrite /sys_exec_slot_pre. iIntros (pl' na alen afun) "%Hpath' %Hargs".
    rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
    rewrite /exec_slot_pre. iSplitL "HPay".
    - (* ---- ARM (a): the observed node IS the pinned file ---- *)
      iIntros (av' i f' nl' W') "HP Hrecv %Hload' %Hok #Hp HQ".
      iDestruct (pobs_node Pin T cw pl hops ino (MkAnode (AFile f) nl)
                   av' i (MkAnode (AFile f') nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp HQ"). }
      destruct Hid as [_ Hnode]. injection Hnode; intros Hnl Hf; subst.
      iApply ("Hcon" $! na alen afun W' with "[%] [%] Hp HQ HPay");
        [ exact Hok | exact Hargs ].
    - (* ---- ARM (b): a pinned file IS loadable, so this arm is dead ---- *)
      iIntros (av' i a W') "HP Hrecv %Hnload %Hkey #Hp HQ".
      iDestruct (pobs_node Pin T cw pl hops ino (MkAnode (AFile f) nl)
                   av' i a Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iApply ("Hgen" with "HT Hp HQ"). }
      destruct Hid as [_ ->].
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
    (* the exec'd program's slot at every key the image fact admits, given
       the process's pay fact AND its payload at the kill status -- both
       relayed from [SpecKexec.exec_slot_pre], see [pex_slot] *)
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Q (-1) -∗ Pay -∗ X W') -∗
    (* the taint's generic slot, indexed by the pay fact and handed the
       payload beside it -- see [pex_slot] *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ Q (-1) -∗ X W') -∗
    Pay -∗
    sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw Q
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) M pv av sts.
  Proof.
    intros Hres Hload Hpath.
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    rewrite /sys_exec_au_pre. iSplitR.
    { iIntros (pl') "%Hpath'".
      rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
      iApply (pobs_walk γfs Pin T cw pl hops ino (MkAnode (AFile f) nl)
                Hres with "Hcl Hinv"). }
    iSplitR.
    { iApply (pobs_aopen γfs Pin T with "Hcl Hinv"). }
    rewrite /pobs_Fo /pfam_triv. cbn [pf_recv].
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
         my_pay (uvis_gen W') Q -∗ Q (-1) -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ Q (-1) -∗ X W') -∗
    Pay -∗
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (R : iProp Σ),
      sys_exec_au_pre (MkPfam X R) (fs_gamma_L γfs) γfs cw Q P Pmiss Fo
        M pv av sts.
  Proof.
    intros Hres Hload Hpath. iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iExists (pobs_P T hops), (pobs_Pmiss T), (pobs_Fo Pin T), Pay.
    iApply (pinned_exec_bundle_at γfs X Pin T cw pl hops ino f nl Pay Q
              M pv av sts Hres Hload Hpath with "Hcl Hinv Hcon Hgen HPay").
  Qed.

End PinnedExec.
