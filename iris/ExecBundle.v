(* ===================================================================== *)
(* ExecBundle.v -- THE GENERAL exec BUNDLE: (W) + (L) + (E), and NOTHING  *)
(* ABOUT WHERE ANY OF THE THREE CAME FROM.                                *)
(*                                                                       *)
(* design/user-exec.md section 2.  [PinnedExec.pinned_exec_bundle] is the *)
(* only place a program's knowledge is turned into                        *)
(* [SpecSysExec.sys_exec_au_pre]'s three conjuncts, and it does it from   *)
(* ONE supplier: a pin on the abstract view, read out of the              *)
(* application's invariant.  The three obligations are separable, and     *)
(* this file separates them:                                             *)
(*                                                                       *)
(*  (W) THE RESOLUTION, as three PREMISES rather than as a pin:           *)
(*      [FsAbsEra.ex_start γfs cw P Pmiss pl] -- the walk at the one path *)
(*      the caller's argument names; [pf_at (aopen_commit_at …) Fo] --    *)
(*      the terminal observation; and [ex_node_id] -- the node this       *)
(*      observation reports at the walk's last hop IS the one the caller  *)
(*      says it is, or the taint.  [PinnedObs.pobs_walk] / [pobs_aopen] / *)
(*      [pobs_node] is ONE supplier of that triple (the pin); the         *)
(*      fragment supplier of lane EX-2 -- shares of [FsAbs.nview] along   *)
(*      the hops, the terminal share riding in [Fo]'s own receipt -- is   *)
(*      another, and it plugs in HERE, with nothing restated.             *)
(*                                                                       *)
(*  (L) LOADABILITY: [⌜kexec_loadable f⌝], one decidable fact             *)
(*      ([ElfLoadable.kexec_loadable_of_b] is the decision).  It is what  *)
(*      REFUTES the deposit's arm (b).                                    *)
(*                                                                       *)
(*  (E) THE ENTRY: [ExecEntry.image_entry], the exec'd program's own      *)
(*      theorem at its key, beside [image_entry_taint] for the arm a      *)
(*      tainted process takes and the linear [Pay] the new image owns     *)
(*      from birth.                                                       *)
(*                                                                       *)
(* WHAT IS NOT HERE.  No [AppInv.app_inv], no [AppCfg.app_pred], no claim *)
(* law, no [Pin] -- this file cannot name a pin, which is the point.  The *)
(* MASK is the one thing the application's invariant leaves behind        *)
(* ([AppInv.appE], where [SysOpenDefs.aopen_commit_at]'s commit is owed), *)
(* and it is a constant.                                                  *)
(*                                                                       *)
(* WHY [ex_node_id] AND NOT [PinnedObs.pobs_node].  The pinned step       *)
(* concludes [⌜i = ino /\ b = a⌝ ∨ T] and exec spends only the second     *)
(* conjunct (the inum the walk landed on is never read again -- the       *)
(* cursor is spent at the wand).  Taking the weaker fact as the premise   *)
(* is what lets a supplier that knows the NODE but not the INUM -- a      *)
(* held share is about a node -- answer it.                               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each one IMPORTED and not
   merely required ([PinnedExec.v]'s note): a field instance is inert
   wherever its module is not imported. *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G]: the bundle *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG] *)
Require Import UserFd.          (* [ufdG] *)
Require Import UexecSlot.       (* [uvis] *)
Require Import ElfFile.         (* [elf_bytes] *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsBlocks.        (* [fs_names] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import AppInv.          (* [appE]: the mask the commit is owed at *)
Require Import SpecKexec.       (* [exec_slot_pre], [exec_au_pre],
                                   [kexec_loadable], [anode_loadable] *)
Require Import SpecSysExec.     (* [sys_exec_au_pre], [exec_path_of_uniq] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import SysOpenDefs.     (* [aopen_commit_at] *)
Require Import ExecEntry.       (* [image_entry] / [image_entry_taint] *)
Require Import FsAbsEra.        (* [ex_start]: the walk at ONE path *)
Require Import FsAbsDefs.       (* [anode], [aview] (FsAbs's own rule: LAST) *)
Import Defs.

Local Open Scope Z_scope.

Section ExecBundle.
  (* [SpecSysExec.SysExecAU]'s ghost list verbatim.  NO [CpuId] and NO
     [CurCtx]: nothing here is hart-indexed, and an exec bundle is
     deliberately context-free all the way to [UexecRet.uslot]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  1.  (W)'s THIRD PIECE: THE NODE THE OBSERVATION REPORTS             *)
  (* ------------------------------------------------------------------ *)

  (* THE IDENTIFICATION, at whatever pair of families the supplier chose:
     the cursor at the walk's TERMINAL hop, together with the terminal
     observation's own receipt, says the observed node is [a] -- or the
     application is already tainted.

     [□], because a bundle owes BOTH slot wands and each of them applies
     it: the kernel fires one arm, but the pair has to be there.  The
     wand CONSUMES its two arguments, so a supplier whose receipt is a
     held share may put the share in the receipt. *)
  Definition ex_node_id (T : iProp Σ) (Pfin : Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (a : anode) : iProp Σ :=
    (□ (∀ (v : aview) (i : Z) (b : anode),
          Pfin i -∗ Φo v i b -∗ ⌜b = a⌝ ∨ T))%I.

  Global Instance ex_node_id_persistent T Pfin Φo a :
    Persistent (ex_node_id T Pfin Φo a).
  Proof using . rewrite /ex_node_id. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE SLOT PIECE, AT ONE ARGUMENT SHAPE                           *)
  (* ------------------------------------------------------------------ *)

  (* ARM (a) IDENTIFIES THE FILE and arm (b) is REFUTED, and both do it
     from the SAME step: the observed node IS the file the caller says it
     is, so (a)'s constructor answers from [kexec_image_ok f] and (b)'s
     [~ anode_loadable] is absurd against (L).  Either arm at the taint
     goes to the generic entry.

     [Pay] goes to ARM (a) ONLY: arm (b) never returns and needs nothing
     but what it is handed. *)
  Lemma exec_slot_of_entry_at (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (Pfin : Z -> iProp Σ) (Φo : aview -> Z -> anode -> iProp Σ)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (cw : Z) (secc : mword 64) (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    (* ...AND NO ALL-PARKED ROW ON EITHER ARM (lane OFF-HAND-6, H3).  Lane
       OFF-HAND-4 took it off the VERIFIED arm and lane OFF-HAND-5 moved
       the TAINT arm's off the kernel and onto this builder; fact 4 of
       design/app-file.md SS3 deletes it outright, because the half a held
       row's fire needs is in the DESCRIPTOR BUNDLE and the kernel holds
       it.  So a held row crosses an exec on both arms and this builder
       says nothing at all about offsets. *)
    ex_node_id T Pfin Φo (MkAnode (AFile f) nl) -∗
    image_entry_at f na alen afun sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T sts secc Q X -∗
    Pay -∗
    exec_slot_pre X Q Pfin Φo cw secc na alen afun sts cs pidv.
  Proof using .
    intros Hload. iIntros "#Hid #Hcon #Hgen HPay".
    rewrite /exec_slot_pre /ex_node_id /image_entry_at /image_entry_taint.
    iSplitL "HPay".
    - (* ---- ARM (a): the observed node IS the caller's file ---- *)
      iIntros (av' i f' nl' W') "HP Hrecv %Hload' %Hok %Hcwq %Hlzq %Hscw %Hchq %Hpiq #Hp".
      (* [iPoseProof] first: [Hid] is persistent and its two arguments are
         SPATIAL, so specializing it in place would ask for a persistent
         result.  The copy is spatial and takes them. *)
      iPoseProof ("Hid" $! av' i (MkAnode (AFile f') nl')) as "Hid'".
      iDestruct ("Hid'" with "HP Hrecv") as "[%Hnode | HT]"; last first.
      { (* THE TAINT ARM TAKES THE KEY AND NOTHING ELSE (lane OFF-HAND-6):
           the generic family needs no fact about the key's offsets, so
           what used to be spent here is not asked for. *)
        iApply ("Hgen" $! W' with "HT [%] [%] Hp");
          [ exact (kexec_image_ok_fd _ _ _ _ _ _ Hok) | exact Hscw ]. }
      (* [subst f' nl'] and not a bare [subst]: the rows introduced just
         above are equations on [cw], on [uvis_lazy W'], on [cs] and on
         [pidv], and a bare [subst] would spend one of those instead. *)
      injection Hnode; intros Hnl Hf. subst f' nl'.
      iApply ("Hcon" $! W' with "[%] [%] [%] [%] [%] [%] Hp HPay");
        [ exact Hok | exact Hcwq | exact Hlzq | exact Hscw | exact Hchq | exact Hpiq ].
    - (* ---- ARM (b): a loadable file IS loadable, so this arm is dead ---- *)
      iIntros (av' i a W') "HP Hrecv %Hnload %Hkey %Hcwq %Hlzq %Hscw %Hchq %Hpiq #Hp".
      iPoseProof ("Hid" $! av' i a) as "Hid'".
      iDestruct ("Hid'" with "HP Hrecv") as "[%Hnode | HT]"; last first.
      { iApply ("Hgen" $! W' with "HT [%] [%] Hp");
          [ exact (exec_key_ok_fd _ _ _ _ Hkey) | exact Hscw ]. }
      subst a. exfalso. apply Hnload. exists f, nl.
      split; [ reflexivity | exact Hload ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE SLOT PIECE AT THE SYSCALL BOUNDARY                          *)
  (* ------------------------------------------------------------------ *)

  (* [SpecSysExec.sys_exec_slot_pre] quantifies the path and the argument
     shape, under the caller's own two readings.  THE PATH READING IS A
     FUNCTION of [(M, pv)] ([SpecSysExec.exec_path_of_uniq]), so a caller
     that knows its image owes the walk at exactly one path -- which is
     what lets [Pfin] be the cursor at THAT path's last hop.  THE
     ARGUMENT READING is relayed to the entry, which is where it is
     spent (ExecEntry.v's header). *)
  Lemma sys_exec_slot_of_entry (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (P : nat -> Z -> iProp Σ) (Φo : aview -> Z -> anode -> iProp Σ)
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (M : gmap Z (bv 8)) (pv av : mword 64)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    exec_path_of M pv pl ->
    ex_node_id T (P (length (path_elems pl))) Φo (MkAnode (AFile f) nl) -∗
    image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T sts secc Q X -∗
    Pay -∗
    pf_at (fun S => sys_exec_slot_pre S Q P Φo cw secc M pv av sts cs pidv)
      (MkPfam X Pay).
  Proof using .
    intros Hload Hpath. iIntros "#Hid #Hcon #Hgen HPay".
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [ | iExact "HPay" ].
    rewrite /sys_exec_slot_pre. iIntros (pl' na alen afun) "%Hpath' %Hargs".
    rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
    iApply (exec_slot_of_entry_at X T (P (length (path_elems pl))) Φo f nl
              Pay Q cw secc na alen afun sts cs pidv Hload
              with "Hid [] Hgen HPay").
    iApply (image_entry_at_of f M av sts cw secc cs pidv Q Pay X na alen afun Hargs
              with "Hcon").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE ASSEMBLY                                                    *)
  (* ------------------------------------------------------------------ *)

  (* THE SYSCALL'S BUNDLE, out of (W), (L) and (E) and nothing else.
     [P], [Pmiss] and [Fo] are the SUPPLIER's families and leave
     existentially at a deposit site ([PinnedExec.pinned_exec_bundle] is
     the pin's instance, and does the [iExists] itself). *)
  Lemma exec_bundle_of (γfs : fs_names) (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    (* (L) *)
    kexec_loadable f ->
    (* the path the caller's own image names, the third pure input *)
    exec_path_of M pv pl ->
    (* (W) *)
    ex_start γfs cw P Pmiss pl -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) Fo -∗
    ex_node_id T (P (length (path_elems pl))) Fo.(pf_recv)
      (MkAnode (AFile f) nl) -∗
    (* (E) *)
    image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T sts secc Q X -∗
    Pay -∗
    sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw secc Q P Pmiss Fo
      M pv av sts cs pidv.
  Proof using .
    intros Hload Hpath. iIntros "Hwalk Hobs #Hid #Hcon #Hgen HPay".
    rewrite /sys_exec_au_pre. iSplitL "Hwalk".
    { iIntros (pl') "%Hpath'".
      rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath). iExact "Hwalk". }
    iSplitL "Hobs"; [ iExact "Hobs" | ].
    iApply (sys_exec_slot_of_entry X T P Fo.(pf_recv) f nl Pay Q cw secc pl M pv av
              sts cs pidv Hload Hpath with "Hid Hcon Hgen HPay").
  Qed.

  (* ...AND THE KERNEL'S OWN CALL, at [SpecKexec.exec_au_pre]: forkret's
     boot arm calls [kexec] with a literal path and a literal vector, so
     there is no caller image to read either out of -- the walk is owed at
     THE path and the slot piece at THE argument shape.  Everything else
     is the syscall bundle's. *)
  Lemma exec_bundle_of_at (γfs : fs_names) (X : uvis -d> iPropO Σ)
      (T : iProp Σ) (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    ex_start γfs cw P Pmiss pl -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) Fo -∗
    ex_node_id T (P (length (path_elems pl))) Fo.(pf_recv)
      (MkAnode (AFile f) nl) -∗
    image_entry_at f na alen afun sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T sts secc Q X -∗
    Pay -∗
    exec_au_pre (MkPfam X Pay) (fs_gamma_L γfs) γfs cw secc Q P Pmiss Fo
      pl na alen afun sts cs pidv.
  Proof using .
    intros Hload. iIntros "Hwalk Hobs #Hid #Hcon #Hgen HPay".
    rewrite /exec_au_pre. iSplitL "Hwalk"; [ iExact "Hwalk" | ].
    iSplitL "Hobs"; [ iExact "Hobs" | ].
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [ | iExact "HPay" ].
    iApply (exec_slot_of_entry_at X T (P (length (path_elems pl)))
              Fo.(pf_recv) f nl Pay Q cw secc na alen afun sts cs pidv Hload
              with "Hid Hcon Hgen HPay").
  Qed.

End ExecBundle.
