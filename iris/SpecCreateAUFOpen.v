(* SpecCreateAUFOpen.v -- the T_FILE create carry's payouts, FOLDED INTO
   [SpecSysOpenAU]'s O_CREATE arms.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the T_FILE
   create-AU carry).  A BRIDGE LEAF: it requires both [SpecCreateAUF] and
   [SpecSysOpenAU] and moves neither (R10).  It is a separate file rather
   than a section of [SpecCreateAUF] because the carry is not open's --
   [SpecCreateAUF] must not depend on the syscall that happens to consume
   it first (sys_link and sys_mkdir will want the same carry at their own
   posts), and the mirror forbids appending to a tracked file besides.

   ==== WHAT IS AND IS NOT HERE ========================================

   [cauf_fail_to_open] is the WHOLE failure fold: [cauf_fail]'s three
   alternatives are [open_post_fail_create]'s inner three, arm for arm, and
   the only thing the fold adds is sys_open's own two commits, which on
   every one of create's failure arms are still UNFIRED (create returns 0
   and sys_open has not yet touched the child).  It is stated as a wand
   taking those two commits so that the consumer's prover applies it with
   no case analysis at all.

   The SUCCESS side is NOT folded here, and that is deliberate rather than
   missing: [open_post_ok_create]'s two disjuncts each end in
   [open_fd_ok] -- the descriptor, the file-table slot and the
   [proc_priv]/[fd_frags] bundle -- none of which create ever sees, and on
   the FILE sub-arm the trunc receipt is delivered only if [om_trunc].  So
   the success bridge is not a fold but a FRAMING, and it is one line of
   the consumer's own prover on top of [SpecCreateAUF.cauf_ok_fresh] /
   [cauf_ok_exists], which already hand out exactly the fields the two
   disjuncts name ahead of the descriptor.  [cauf_ok_shape] below records
   that correspondence as a theorem about the parts create DOES own, so
   the consumer's prover can see it fail if the contract ever drifts.

   BINDERS: [SpecSysOpenAU]'s section list ([SpecCreate]'s plus [GenId],
   which the open arms carry for [proc_priv]) -- but nothing here mentions
   a process, so [GenId] is NOT bound: the definitions this file speaks
   about are the AU sides alone. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.           (* [fname]                                 *)
Require Import PathElems.        (* [path_elems]                            *)
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import InodeInv.
Require Import InodeLock.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import FsStateEra.
Require Import InodeRegion.
Require Import Xv6G.
Require Import SpecCreate.
Require Import SpecSysMknodAU.   (* [cre_pre], [mknod_parent_elems]         *)
Require Import FsAbsEra.
Require Import FsAbsEraMknod.    (* [mknod_walk_dead_era]                   *)
Require Import FsAbsMknodFire.   (* the two commits                         *)
Require Import SpecCreateAUF.    (* [cauf_ok], [cauf_fail]                  *)
Require Import SpecSysOpenAU.    (* the consumer, which does NOT move       *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)

Local Open Scope Z_scope.

Section CreateAUFOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  THE FAILURE FOLD                                                    *)
  (* ------------------------------------------------------------------ *)

  (* create failed, so sys_open fails past it with NOTHING of its own
     fired.  The three alternatives land as follows -- and the numbering is
     [SpecSysOpenAU]'s own:

       cauf_fail LEFT (the walk died)      -> the dead-walk disjunct
       cauf_fail RIGHT, Φex FIRED (F-BAD)  -> (b), with [aopen_commit_at]
                                              in ITS left alternative
       cauf_fail RIGHT, commit back (N/G/  -> (c)
         A-FAIL/FAIL, and the "/" arm)

     Arm (a) -- a FRESH create that succeeded and an open that failed past
     it -- is unreachable from [cauf_fail] by construction, because create
     returning 0 is exactly what [cauf_fail] is the payout of.  sys_open
     builds (a) from [cauf_ok]'s [made = true] arm at its OWN later
     failures. *)
  Lemma cauf_fail_to_open Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (pl : list (bv 8)) :
    cauf_fail Γ γfs P Pmiss Φok Φex pl -∗
    aopen_commit_at Γ ∅ Φo -∗
    atrunc_commit_at Γ ∅ Φt -∗
    open_post_fail_create Γ γfs P Pmiss Φok Φex Φo Φt.
  Proof.
    iIntros "Hcf Ho Ht".
    rewrite /cauf_fail /open_post_fail_create.
    iRight. iExists pl.
    iDestruct "Hcf" as "[(Hd & Hac & Hdl) | Hr]".
    - iLeft. iFrame "Hd Hac Hdl Ho Ht".
    - iRight. iDestruct "Hr" as (d) "(HP & Hac & Hrest)".
      iExists d. iFrame "HP Ht".
      iDestruct "Hrest" as "[Hfired | Hdl]".
      + (* (b): the name was there and the observation fired *)
        iRight. iLeft.
        iDestruct "Hfired" as (av i nm ents nl) "(%Hl & %Hrow & %Hent & HΦ)".
        iExists av, i, nm, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |].
        iFrame "HΦ Hac". iLeft. iExact "Ho".
      + (* (c): nothing observed *)
        iRight. iRight. iFrame "Hac Hdl Ho".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE SUCCESS CORRESPONDENCE                                          *)
  (* ------------------------------------------------------------------ *)

  (* The parts of [open_post_ok_create]'s two disjuncts that create owns,
     stated as the shape the consumer frames the descriptor into.  This is
     [cauf_ok] with the [if made] resolved and the cursor pushed inside,
     i.e. precisely [SpecCreateAUF.cauf_ok_fresh] and [cauf_ok_exists] read
     against the consumer -- named here so that a drift in either contract
     breaks a proof rather than a prover. *)
  Lemma cauf_ok_shape Γ (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) (made : bool) (i : Z) :
    cauf_ok Γ P Φok Φex pl made i ⊢
      ∃ (d : Z) (nm : fname),
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        ((* the FRESH half of [open_post_ok_create], ahead of the
            descriptor and the two refunds open keeps for itself *)
         (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
            Φok av d nm i ∗
            dlookup_commit_at Γ ∅ Φex)
         ∨ (* ...and the EXISTS-OPENS half, ahead of the found node's own
              observation *)
         (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
            ⌜ents !! nm = Some i⌝ ∗
            Φex av d nm i ∗
            acre_commit_at Γ ∅ (AFile []) Φok)).
  Proof.
    destruct made.
    - iIntros "H".
      iDestruct (cauf_ok_fresh with "H") as (d nm av ents nl)
        "(%Hl & %Hpre & HP & HΦ & Hdl)".
      iExists d, nm. iSplitR; [by iPureIntro |]. iFrame "HP".
      iLeft. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iFrame "HΦ Hdl".
    - iIntros "H".
      iDestruct (cauf_ok_exists with "H") as (d nm av ents nl)
        "(%Hl & %Hrow & %Hent & HP & HΦ & Hac)".
      iExists d, nm. iSplitR; [by iPureIntro |]. iFrame "HP".
      iRight. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HΦ Hac".
  Qed.

End CreateAUFOpen.
