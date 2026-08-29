(* FsAbsEraMknod.v -- THE FIRST CONSUMER, WIRED: [SpecSysMknodAU]'s two
   commit steps consumed at an ERA hop's fire instant, and the era-lend
   twins of its two walk predicates.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii)
   (the era-fragment walk) meeting lane W (the mknod AU statement).  The
   landed statement file does not move (its own R10-parallel discipline);
   these are the PARALLEL forms beside it.

   WHY THIS FILE.  Lane W's header records what its prover owes, and the
   first item is "the two fire points: dirlookup via [ftop_astate_ro]".
   With the LANDED trace contract that item was not merely unproven, it was
   unprovable: [SpecNameiTr.nx_hop] lends [DirViewG.dv_half], which says
   nothing about gamma-top, so no amount of opening ftopN at the fire
   instant identifies the authority's row for the directory the walk is
   standing on ([FsAbsSeam], findings 2 and 3).  [SpecSysMknodAU]'s
   [mknod_walk_pre] therefore rides [ax_hops_from dv_half] and its prover
   has no way to reach [dlookup_commit]'s premises.

   With the era lend it is three lines: [FsAbsEra.elend_astate] reads the
   row straight off the authority, because the lent fragment and the
   carrier are THE SAME GHOST.  [era_dlookup_fire] below is that step,
   whole; [era_acre_fire] is the success commit's phase 1 at the same
   instant, which needs the parent's row for exactly the same reason.

   WHAT IS NOT HERE.  The nameiparent WALK.  These lemmas are about the
   HOP, and the hop is the same on both sides of namex's [a1] test; what
   the nameiparent side still needs is namex's two npar exits proven at a
   trace contract, which is a walk-proof item and not a lend item (see
   [ProofNamexEra]'s header).  So this file makes the mknod prover's fire
   points discharged-in-advance, and leaves it waiting on the walk that
   delivers them. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import FsTree.
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsImg.           (* [ROOTINO] -- REQUIRED, NOT IMPORTED (lane W's
                                   gotcha: it shadows at syscall altitude) *)
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import SpecSysMknodAU. (* [acre_commit], [dlookup_commit],
                                  [mknod_parent_elems], [cre_pre] *)
Require Import FsAbsEra.       (* [elend], [ex_hops_from], [elend_astate] *)
Require Import FsAbs.          (* LAST (FsAbs's own rule): [astate], [ax_hop] *)

Local Open Scope Z_scope.

Section EraMknod.
  (* [SpecSysMknodAU]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE READ-ONLY FIRE                                              *)
  (* =================================================================== *)

  (* THE STEP LANE W's PROVER OWES, discharged.  At the hop instant the
     caller holds three things: its own [dlookup_commit] (the AU's
     read-only arm), the ERA LEND the walk just handed it, and [astate]
     (borrowed out of ftopN by [FsAbs.ftop_astate_ro] -- the borrow is
     not repeated here because it is [FsAbs]'s and the caller does it
     once around this step).  It gets the receipt, and BOTH the lend and
     the state back: nothing of the walk's is consumed, so the hop's
     "hand the fragment back at the same dfrac" obligation is met by the
     same [HF] that came in.

     The [ents !! nm = Some i] premise is dirlookup's own answer, which
     is what the hop's match is computed from -- so a caller inside
     [ax_hop]'s fupd has it by construction. *)
  Lemma era_dlookup_fire Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (av : aview) (d : Z) (dq : dfrac) (ents : gmap fname Z)
      (nm : fname) (i : Z) :
    ents !! nm = Some i ->
    dlookup_commit Γ E Φ -∗ elend Γ d dq ents -∗ astate Γ av ={E}=∗
      astate Γ av ∗ elend Γ d dq ents ∗ Φ av d nm i.
  Proof.
    intros Hnm. iIntros "Hcm HF Hst".
    iDestruct (elend_astate with "Hst HF") as %(nl & Hav).
    iMod ("Hcm" $! av d i nm ents nl with "[//] [//] Hst") as "[Hst HΦ]".
    iModIntro. iFrame "Hst HF HΦ".
  Qed.

  (* =================================================================== *)
  (*  2.  THE SUCCESS COMMIT'S PHASE 1                                    *)
  (* =================================================================== *)

  (* [acre_commit]'s first phase asks for [cre_pre av d nm ents nl i c],
     which is THREE facts: the parent's row read as an [ADir] at the entry
     map the walk lent, the name's absence from it, and the minted child's
     row.  The first is the one only the lend can supply -- and it is
     exactly what the [dv_half] fire could not -- so the era lend supplies
     it and the [nl] the row carries is existential to the caller.  The
     other two are the caller's own (dirlookup's miss and the mint's
     observation) and are premises here. *)
  Lemma era_acre_fire Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (av : aview) (d i : Z) (dq : dfrac) (ents : gmap fname Z)
      (nm : fname) :
    ents !! nm = None ->
    av !! i = Some (MkAnode c 1%nat) ->
    acre_commit Γ E c Φ -∗ elend Γ d dq ents -∗ astate Γ av ={E}=∗
      elend Γ d dq ents ∗ astate Γ av
      ∗ (astate Γ (delta_create d nm i c av) ={E}=∗
         astate Γ (delta_create d nm i c av) ∗ Φ av d nm i).
  Proof.
    intros Hnm Hi. iIntros "Hcm HF Hst".
    iDestruct (elend_astate with "Hst HF") as %(nl & Hav).
    iMod ("Hcm" $! av d i nm ents nl with "[%] Hst") as "[Hst Hph2]".
    { rewrite /cre_pre. split; [exact Hav | split; [exact Hnm | exact Hi]]. }
    iModIntro. iFrame "HF Hst Hph2".
  Qed.

  (* =================================================================== *)
  (*  3.  THE ERA TWINS OF LANE W's TWO WALK PREDICATES                   *)
  (* =================================================================== *)

  (* [SpecSysMknodAU.mknod_walk_pre] with [dv_half] replaced by the era
     lend and NOTHING else -- same one-shot fupd, same fetched-path
     shape, same root tie.  When the nameiparent era walk lands, THIS is
     the premise the syscall contract carries; the landed one stays for
     the dv-firing walk until the retirement step. *)
  Definition mknod_walk_pre_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜pl !! 0%nat = Some SLASH -> r = FsImg.ROOTINO⌝ ={⊤}=∗
       P 0%nat r
       ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
           (mknod_parent_elems pl) 0%nat)%I.

  Definition mknod_walk_dead_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∃ (k : nat) (d : Z),
       ⌜(k < length (mknod_parent_elems pl))%nat⌝ ∗
       ((P k d ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
                   (mknod_parent_elems pl) k)
        ∨ (Pmiss k d
           ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
               (mknod_parent_elems pl) (S k))))%I.

  (* the same two seals lane W puts on its own pair, and for the same
     reason (they are big-ops behind Definitions at syscall altitude) *)

End EraMknod.

Global Typeclasses Opaque mknod_walk_pre_era mknod_walk_dead_era.
