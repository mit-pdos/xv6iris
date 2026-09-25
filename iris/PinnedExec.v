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
Require Import FsBlocks.        (* [fs_names], [fs_top] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import AppCfg.          (* [app_pred] / [app_run] *)
Require Import AppInv.          (* [app_inv], [app_body], [appN] / [appE] *)
Require Import SpecKexec.       (* [exec_slot_pre], [kexec_loadable], [anode_loadable] *)
Require Import SpecSysExec.     (* [sys_exec_au_pre], [exec_path_of_uniq] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import FsAbsDefs.       (* [arun], [arow_at], [aents], [astep], [abs_view] *)
Require Import PinnedObs.       (* the pinned observation family, factored:
                                   [pin_resolves_at], [pobs_P]/[pobs_Pmiss],
                                   [pobs_recv]/[pobs_Fo], [pinned_obs] *)
Require Import ExecEntry.       (* (E): [image_entry] / [image_entry_at] /
                                   [image_entry_taint] -- the two [□]
                                   constructor premises below, NAMED *)
Require Import ExecBundle.      (* the general assembly this file is now one
                                   instance of: [ex_node_id],
                                   [exec_slot_of_entry_at],
                                   [sys_exec_slot_of_entry], [exec_bundle_of],
                                   [exec_bundle_of_at] *)
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
  (*  ONCE THERE, over any syscall whose bundle is “walk a path, observe   *)
  (*  the node” -- they were written here first and say nothing about      *)
  (*  exec.  What is left in this file is exec's OWN piece: the two slot   *)
  (*  wands below, and the bundle that assembles them with the general     *)
  (*  lemma.                                                              *)
  (* ------------------------------------------------------------------ *)

  (* ------------------------------------------------------------------ *)
  (*  5b.  THE PIN AS A SUPPLIER OF (W)'s THIRD PIECE                     *)
  (*                                                                      *)
  (*  [ExecBundle.ex_node_id] is what an exec bundle actually spends of   *)
  (*  the walk: the node the observation reports at the last hop is the   *)
  (*  one the caller says it is, or the taint.  [pobs_node] proves it     *)
  (*  from the pin, and says one thing more (the INUM is the pin's) that  *)
  (*  exec never reads -- so the step down to the general premise is the  *)
  (*  projection, and it is the whole of what makes this file an          *)
  (*  INSTANCE of [ExecBundle] rather than a second copy of it.           *)
  (* ------------------------------------------------------------------ *)
  Lemma pobs_node_id (Pin : aview -> Prop) (T : iProp Σ)
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    ⊢ ex_node_id T (pobs_P T hops (length (path_elems pl)))
        (pobs_recv Pin T) a.
  Proof using .
    intros Hres. rewrite /ex_node_id. iIntros "!>" (v i b) "HP Hr".
    iDestruct (pobs_node Pin T cw pl hops ino a v i b Hres with "HP Hr")
      as "[%Hid | HT]"; [ | iRight; iExact "HT" ].
    iLeft. iPureIntro. exact (proj2 Hid).
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
  (* THE PIECE ITSELF, AT ONE ARGUMENT SHAPE.  [SpecKexec.exec_slot_pre]
     is the two wands at a FIXED [(na, alen, afun)]; the syscall's own
     piece quantifies them under the argument reading and the KERNEL'S
     BOOT CALL does not -- [SpecKexec.exec_au_pre] names them, because
     forkret calls [kexec("/init", {"/init", 0})] with a literal vector
     and there is no caller image to read one out of.  So the identifying
     step is stated ONCE here and the two bundles below differ only in
     how their arguments arrive ([pinned_exec_bundle_at] reads them,
     [pinned_exec_bundle_boot] is handed them). *)
  Lemma pex_slot_at (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
    □ (∀ W' : uvis,
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜uvis_cwd W' = cw⌝ -∗ ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         (* ...AND THE TWO IDENTITY ROWS (lane EXEC-SEAM): the resumed
            key's children set and pid are the caller's *)
         ⌜uvis_ch W' = cs⌝ -∗ ⌜uvis_pid W' = pidv⌝ -∗
         (* NO ALL-PARKED ROW ON THE VERIFIED ARM (lane OFF-HAND-4, S2):
            [ExecEntry.image_entry_at]'s note -- an entry that receives it
            can never be entered with a held row.  The TAINT arm below
            keeps one. *)
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    exec_slot_pre X Q (pobs_P T hops (length (path_elems pl)))
      (pobs_recv Pin T) cw secc na alen afun sts cs pidv.
  (* ...AND IT IS [ExecBundle.exec_slot_of_entry_at] AT THE PIN.  The two
     arms are stated and proved there, over an ARBITRARY supplier of
     [ex_node_id]; what is left here is which supplier, and the [□]
     constructor premise is [ExecEntry.image_entry_at] spelled out. *)
  Proof using .
    intros Hres Hload. iIntros "#Hcon #Hgen HPay".
    iApply (exec_slot_of_entry_at X T (pobs_P T hops (length (path_elems pl)))
              (pobs_recv Pin T) f nl Pay Q cw secc na alen afun sts cs pidv Hload
              with "[] [] [] HPay").
    - iApply (pobs_node_id Pin T cw pl hops ino (MkAnode (AFile f) nl) Hres).
    - rewrite /image_entry_at. iExact "Hcon".
    - rewrite /image_entry_taint. iExact "Hgen".
  Qed.

  Lemma pex_slot (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ)
      (* THE EXEC'D PROCESS'S PAYLOAD.  The kernel hands the slot wands the
         exec'ing process's own [ChildTok.my_pay] at it ([SpecKexec.
         exec_slot_pre]) -- exec keeps the generation, so it is the fact
         the NEW image's constructor needs -- and both arms below relay it,
         the pinned one to the caller's constructor and the tainted one to
         the generic family. *)
      (* ...AND NOTHING ELSE CROSSES THE EXEC ANY MORE (lane SELF-KILL,
         P6).  The payload at the KILL status used to ride with the fact,
         because the new image's run carried it between traps; no run does
         now.  What an exec'd image must OWN travels as the linear [Pay] --
         sh's console lease beside its position -- and it goes to the
         PINNED arm, the only one that hands the caller a constructor.
         The TAINT arm takes nothing beside [T] and the pay fact: a
         tainted process runs on the generic family, whose constant
         payload is now carried PERSISTENTLY
         ([UexecExecMint.uslot_mint_all]) and is built out of [T] itself
         ([UserConsole.ucons_pay_taint]) -- which is the whole reason a
         tainted process needs no lease. *)
      (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         (* ...AND THE TWO ROWS [SpecKexec.exec_slot_pre] now carries, in
            its own order (2026-09-12, the coordinator): the resumed key's
            working directory is the caller's, and its lazy bit is
            [false]. *)
         ⌜uvis_cwd W' = cw⌝ -∗
         ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         (* ...AND ITS TWO IDENTITY ROWS (lane EXEC-SEAM): the children
            set and the pid are the caller's, so a freshly exec'd program
            can say it has no children yet and is not <init>. *)
         ⌜uvis_ch W' = cs⌝ -∗
         ⌜uvis_pid W' = pidv⌝ -∗
         (* NO ALL-PARKED ROW ON THE VERIFIED ARM (lane OFF-HAND-4, S2):
            [ExecEntry.image_entry_at]'s note -- an entry that receives it
            can never be entered with a held row.  The TAINT arm below
            keeps one. *)
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    (* THE TAINT ARM TAKES THE KEY FIRST AND THE PAY FACT BESIDE [T]: a
       tainted process runs on the GENERIC family, which is itself indexed
       by the pay fact ([UexecExecMint.uslot_mint]), so the arm cannot be
       "[T] gives a slot at every key" any more -- it is "[T] and this
       key's payload give a slot at this key". *)
    (* (* RA-2: held case here *) ...AND WHEN THE GENERIC FAMILY IS
       NARROWED TO ALL-PARKED KEYS (design/user-read.md SS8.1), this arm
       gains [⌜FdSlots.fdv_all_parked (uvis_fd W')⌝] and this bundle gains
       [fdv_all_parked sts] -- one premise, because the two arms below
       apply the arm at a [W'] the kernel's own [kexec_image_ok] /
       [exec_key_ok] pins to [sts] ([SpecKexec.kexec_image_ok_parked],
       [exec_key_ok_parked] are the two steps).  BUT NOT ON THIS BUNDLE:
       a verified program's U-tier knowledge of its own table is
       [UserFd.ustd] (the low [NSTD] slots) and its [ufd] handles, and
       neither says anything about the rest of it, so a program CANNOT
       state all-parkedness of the table it execs with.  The premise
       belongs on [SpecKexec.exec_slot_pre]'s two WANDS, where the party
       that supplies it is the KERNEL -- which holds the block and reads
       the fact straight off it ([ProcInv.proc_priv_parked]). *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    pf_at (fun S => sys_exec_slot_pre S Q (pobs_P T hops) (pobs_recv Pin T)
                      cw secc M pv av sts cs pidv) (MkPfam X Pay).
  (* ...AND IT IS [ExecBundle.sys_exec_slot_of_entry] AT THE PIN: the path
     reading's uniqueness, the argument reading's relay into the entry and
     the two arms are all stated there; the pin supplies [ex_node_id]. *)
  Proof using .
    intros Hres Hload Hpath. iIntros "#Hcon #Hgen HPay".
    iApply (sys_exec_slot_of_entry X T (pobs_P T hops) (pobs_recv Pin T)
              f nl Pay Q cw secc pl M pv av sts cs pidv Hload Hpath
              with "[] [] [] HPay").
    - iApply (pobs_node_id Pin T cw pl hops ino (MkAnode (AFile f) nl) Hres).
    - rewrite /image_entry. iExact "Hcon".
    - rewrite /image_entry_taint. iExact "Hgen".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  THE BUNDLE                                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma pinned_exec_bundle_at (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* the builder's all-parked row, the taint arm's only (lane
       OFF-HAND-5, D1; see [pex_slot_at]) *)
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
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
         (* ...AND THE TWO ROWS [SpecKexec.exec_slot_pre] now carries, in
            its own order (2026-09-12, the coordinator): the resumed key's
            working directory is the caller's, and its lazy bit is
            [false]. *)
         ⌜uvis_cwd W' = cw⌝ -∗
         ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         (* ...and its two identity rows (lane EXEC-SEAM), see [pex_slot] *)
         ⌜uvis_ch W' = cs⌝ -∗
         ⌜uvis_pid W' = pidv⌝ -∗
         (* NO ALL-PARKED ROW ON THE VERIFIED ARM (lane OFF-HAND-4, S2):
            [ExecEntry.image_entry_at]'s note -- an entry that receives it
            can never be entered with a held row.  The TAINT arm below
            keeps one. *)
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    (* the taint's generic slot, indexed by the pay fact and handed the
       payload beside it -- see [pex_slot] *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw secc Q
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) M pv av sts cs pidv.
  (* ...AND IT IS [ExecBundle.exec_bundle_of] AT THE PIN SUPPLIER OF (W):
     the walk is [PinnedObs.pobs_walk], the observation [pobs_aopen] and
     the node identification [pobs_node_id].  Nothing about exec is
     re-stated here -- (L) and (E) go straight through. *)
  Proof using .
    intros Hres Hload Hpath.
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iApply (exec_bundle_of γfs X T (pobs_P T hops) (pobs_Pmiss T)
              (pobs_Fo Pin T) cw secc pl f nl Pay Q M pv av sts cs pidv
              Hload Hpath with "[] [] [] [] [] HPay").
    - iApply (pobs_walk γfs Pin T (pobs_Pmiss T) cw pl hops ino
                (MkAnode (AFile f) nl) Hres with "[] Hcl Hinv").
      iApply pobs_miss_taint_Pmiss.
    - iApply (pobs_aopen γfs Pin T with "Hcl Hinv").
    - rewrite /pobs_Fo /pfam_triv. cbn [pf_recv].
      iApply (pobs_node_id Pin T cw pl hops ino (MkAnode (AFile f) nl) Hres).
    - rewrite /image_entry. iExact "Hcon".
    - rewrite /image_entry_taint. iExact "Hgen".
  Qed.

  (* ...and the shape a deposit site takes it at: the families are the
     bundle's business, so they leave existentially
     ([UexecExecInst.sbundle_exec_intro] takes exactly this quadruple). *)
  Lemma pinned_exec_bundle (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* the builder's all-parked row, the taint arm's only (lane
       OFF-HAND-5, D1; see [pex_slot_at]) *)
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (W' : uvis),
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         (* ...AND THE TWO ROWS [SpecKexec.exec_slot_pre] now carries, in
            its own order (2026-09-12, the coordinator): the resumed key's
            working directory is the caller's, and its lazy bit is
            [false]. *)
         ⌜uvis_cwd W' = cw⌝ -∗
         ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         (* ...and its two identity rows (lane EXEC-SEAM), see [pex_slot] *)
         ⌜uvis_ch W' = cs⌝ -∗
         ⌜uvis_pid W' = pidv⌝ -∗
         (* NO ALL-PARKED ROW ON THE VERIFIED ARM (lane OFF-HAND-4, S2):
            [ExecEntry.image_entry_at]'s note -- an entry that receives it
            can never be entered with a held row.  The TAINT arm below
            keeps one. *)
         ⌜exec_args_of M av na alen afun⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    (* THE REFUND IS [Pay], NAMED (lane KILL-PAY, K4(a), ruling R-A): a
       FAILED exec hands the deposit's refund back to the process, and a
       caller that cannot say what it gets back cannot spend it on its own
       [exit].  It was existential here for no reason -- the bundle's
       refund IS the linear resource the caller put in. *)
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
      sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw secc Q P Pmiss Fo
        M pv av sts cs pidv.
  Proof using .
    intros Hres Hload Hpath. iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iExists (pobs_P T hops), (pobs_Pmiss T), (pobs_Fo Pin T).
    iApply (pinned_exec_bundle_at γfs X Pin T cw secc pl hops ino f nl Pay Q
              M pv av sts cs pidv Hres Hload Hpath
              with "Hcl Hinv Hcon Hgen HPay").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  8.  THE KERNEL'S OWN CALL: THE BOOT BUNDLE                          *)
  (*                                                                      *)
  (*  [SpecKexec.exec_au_pre] rather than [SpecSysExec.sys_exec_au_pre],   *)
  (*  and the difference is exactly the two argument readings: forkret's   *)
  (*  boot arm calls [kexec("/init", (char *[]){"/init", 0})] with a       *)
  (*  literal path and a literal vector, so there is no caller image [M],  *)
  (*  no path pointer and no argv pointer -- the walk is owed at THE       *)
  (*  path [pl] instead of at every path the image reads, and the slot     *)
  (*  piece at THE shape [(na, alen, afun)] instead of at every shape.     *)
  (*  Everything else is the syscall bundle's: the same cursor family,     *)
  (*  the same observation, the same two slot wands.                       *)
  (*                                                                      *)
  (*  This is what [InitBoot.init_boot_bundle] is discharged from by a     *)
  (*  constraining application, exactly as [InitBoot.init_boot_bundle_triv]*)
  (*  is from [SpecKexec.exec_au_pre_triv_at]. *)
  (* ------------------------------------------------------------------ *)
  Lemma pinned_exec_bundle_boot_at (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    (* the builder's all-parked row, the taint arm's only (lane
       OFF-HAND-5, D1; see [pex_slot_at]) *)
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    (* THE BOOT CONSTRUCTOR READS NO IDENTITY ROW (lane EXEC-SEAM): the
       first process pins nothing about its children set or its pid, so
       the two rows [SpecKexec.exec_slot_pre] now carries are dropped here
       and the bundle is stated at whatever [cs]/[pidv] the boot arm is
       at. *)
    □ (∀ W' : uvis,
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜uvis_cwd W' = cw⌝ -∗ ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw secc Q
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) pl na alen afun sts
      cs pidv.
  (* ...AND IT IS [ExecBundle.exec_bundle_of_at] AT THE SAME SUPPLIER: the
     boot call's only difference is the two readings it does not do, so
     (E) arrives at [ExecEntry.image_entry_at] -- the entry at THE
     argument shape -- and the two identity rows the boot constructor
     does not read are dropped where it is built. *)
  Proof using .
    intros Hres Hload. iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iApply (exec_bundle_of_at γfs X T (pobs_P T hops) (pobs_Pmiss T)
              (pobs_Fo Pin T) cw secc pl f nl Pay Q na alen afun sts cs pidv
              Hload with "[] [] [] [] [] HPay").
    - iApply (pobs_walk γfs Pin T (pobs_Pmiss T) cw pl hops ino
                (MkAnode (AFile f) nl) Hres with "[] Hcl Hinv").
      iApply pobs_miss_taint_Pmiss.
    - iApply (pobs_aopen γfs Pin T with "Hcl Hinv").
    - rewrite /pobs_Fo /pfam_triv. cbn [pf_recv].
      iApply (pobs_node_id Pin T cw pl hops ino (MkAnode (AFile f) nl) Hres).
    - rewrite /image_entry_at.
      iIntros "!>" (W') "%Hok %Hcwq %Hlzq _ _ Hp HPay".
      iApply ("Hcon" $! W' with "[%] [%] [%] Hp HPay");
        [ exact Hok | exact Hcwq | exact Hlzq ].
    - rewrite /image_entry_taint. iExact "Hgen".
  Qed.

  (* ...and the shape [InitBoot.init_boot_bundle] takes it at: the families
     leave existentially, exactly as they do at a syscall deposit site. *)
  Lemma pinned_exec_bundle_boot (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) :
    pin_resolves Pin cw pl hops ino f nl ->
    kexec_loadable f ->
    (* the builder's all-parked row, the taint arm's only (lane
       OFF-HAND-5, D1; see [pex_slot_at]) *)
    (* NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3;
       design/app-file.md SS3 fact 4): the half a held row's fire needs is
       in the descriptor bundle, so the generic family the taint arm runs
       on owes nothing about offsets and a held row crosses on both arms. *)
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    □ (∀ W' : uvis,
         ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
         ⌜uvis_cwd W' = cw⌝ -∗ ⌜uvis_lazy W' = false⌝ -∗
         ⌜uvis_secc W' = secc⌝ -∗
         my_pay (uvis_gen W') Q -∗ Pay -∗ X W') -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W') -∗
    Pay -∗
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (R : iProp Σ),
      (* AT EVERY [cs]/[pidv] (lane EXEC-SEAM): the boot arm names the
         first process's readings when it spends the bundle, and the
         application's constructor reads neither. *)
      ∀ (cs : gset gname) (pidv : mword 32),
        exec_au_pre (MkPfam X R) (fs_gamma_L γfs) γfs cw secc Q P Pmiss Fo
          pl na alen afun sts cs pidv.
  Proof using .
    intros Hres Hload. iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    iExists (pobs_P T hops), (pobs_Pmiss T), (pobs_Fo Pin T), Pay.
    iIntros (cs pidv).
    iApply (pinned_exec_bundle_boot_at γfs X Pin T cw secc pl hops ino f nl Pay Q
              na alen afun sts cs pidv Hres Hload
              with "Hcl Hinv Hcon Hgen HPay").
  Qed.

End PinnedExec.
