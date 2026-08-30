(* ===================================================================== *)
(*  ProofKexecPinTrace.v -- THE PINNED WALK'S TRACE, and the one finding   *)
(*  the prover made about [SpecKexecPin]'s premise.                        *)
(*  (fs-syscall-specs, PINNED-EXEC PROVER lane; SpecKexecPin.v sect. 8 (3)) *)
(* ===================================================================== *)

(*  WHAT THIS FILE IS.  [SpecKexecPin] sect. 8 (3) owes "the pinned namei
    trace": the cursor [P] and the hop family that the era walk
    ([SpecNameiEra] over [FsAbsStart.ex_start]) consumes, built out of the
    contract's pin premise, whose success post then reads
    [zi = kxp_ino pb] -- the tie the header oracle needs.

    ---- THE FINDING, STATED FIRST BECAUSE IT MOVES A PREMISE ------------

    [SpecKexecPin.kxp_view_pin] re-reads [kxp_pins av pb] at EVERY instant
    the walk opens the authority, and [kxp_pins] pins the two ENDPOINTS: the
    path resolves from the root to the pinned inum, and that inum's row is
    the pinned file.  For a ONE-ELEMENT path that is the whole chain and the
    walk is pinned.  FOR A LONGER PATH IT IS NOT ENOUGH, and not merely
    unprovable -- the sentence is FALSE:

      take [kxp_path pb = ["a"; "b"]].  The walk fires hop 0 at instant t0,
      reads the root's entries, and steps to whatever "a" names THERE, say
      [d].  It fires hop 1 at instant t1 > t0.  A writer between the two
      instants may re-point the root's "a" at a fresh directory [d'] whose
      "b" is the pinned inum, and leave [d]'s "b" pointing at junk.  BOTH
      instants satisfy [kxp_pins] -- the endpoint pin never broke, it just
      resolves through [d'] now -- and the walk, standing at the stale [d],
      answers junk.  No cursor definable from [kxp_pins] can rule this out:
      the invariant a hop can carry forward has to hold at EVERY
      pin-satisfying view, and "d is the k-th inum" does not.

    THE REPAIR IS ONE CONJUNCT AND IT IS ALREADY WRITTEN UPSTREAM.  What
    pins a walk is the CHAIN, not the answer: [FsAbs.arun av ROOTINO ps ds]
    at a FIXED [ds].  [FsInitPinBoot.era0_pins] and [FsShPin.era0_sh_pins]
    both carry exactly that conjunct already ([arun av ROOTINO init_path
    [ROOTINO; INIT_INO]]), and [SpecKexecPin]'s sect. 5a instance drops it
    on the floor ([intros (Hp & Hc & _)]).  So the honest premise is free at
    both era-0 instances, and this file states it as [kxp_run_pin]: the
    landed [kxp_view_pin]'s reader with the chain beside the pins.  Whether
    [kx_pin] grows a [kxp_chain] field (and [kxp_pins] the third conjunct)
    is the statement lane's call, which is why nothing in SpecKexecPin.v is
    touched -- see [kxp_run_pin_of_view] below, the receipt that the LANDED
    premise still delivers the honest one on every ONE-ELEMENT path, i.e.
    on both era-0 instances ([init_path = ["init"]], [sh_path = ["sh"]]).

    ---- HOW THE HOP FIRES ------------------------------------------------

    The cursor is PURE -- [kxt_P ds k d := ds !! k = Some d] -- so it is
    persistent, duplicable, and carries nothing across an instant that could
    go stale.  All the work is at the fire: the hop opens [ftopN], reads the
    pins AND the chain off the authority ([kxp_run_pin]), reads the lent
    directory's row off the SAME authority ([FsAbsEra.elend_aents], the law
    the era lend exists for), and steps the chain with [FsAbs.arun_step].
    Both readings are PURE conclusions, so the [ghost_map_auth] the body
    came with is handed back UNCHANGED and [ftopN] closes at the very same
    [I] -- [FsAbsReadFire]'s recorded shape ("[ftop_astate_ro]'s give-back
    wants the SAME [I] the borrow named, and [astate]'s existential destroys
    it"): this file never round-trips the authority through [astate].       *)

(* ---- SpecKexecPin.v's Require block, VERBATIM, with the era-walk pair
   spliced in immediately before [FsAbs] (which stays LAST of the fs-abs
   stack, its own rule). ---- *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.     (* [ftop_inv], [ftop_body], [ftopN]         *)
Require Import IrefSlots.
Require Import DirViewG.    (* Require Export's DirViewG: [fv_of]       *)
Require Import DirViewLend.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import DinodeEnc.
Require Import InodeDefs.
Require Import InodeLock.
Require Import PathElems.
Require Import FsTree.
Require FsImg.
Require Import FsStateEra.
Require Import FsState.
Require Import KexecOkQ.
Require Import FsAbsEra.        (* [elend], [ex_hop], [ex_hops_from]        *)
Require Import FsAbsStart.      (* [ex_start]: the deferred start           *)
Require Import FsAbs.           (* LAST of the fs-abs stack (its own rule)  *)
Require Import FsBytesGamma.
Require Import FsInitPin.
Require Import FsInitPinBoot.
From User Require Import InitData ShData.
Require Import SpecKexecPin.    (* the contract this lane serves            *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE TWO ROOT INUMS ARE ONE NUMBER                                 *)
(*                                                                        *)
(*  [kxp_pins] is stated from [FsImg.ROOTINO : Z] (the image's spelling,   *)
(*  which [FsInitPinBoot] uses) and [FsAbsStart.ex_start]'s tie is at      *)
(*  [bv_unsigned InodeInv.ROOTINO] (namex's).  Both are 1.                 *)
(* ===================================================================== *)

Lemma kxt_rootino : FsImg.ROOTINO = bv_unsigned (ROOTINO : mword 32).
Proof. vm_compute. reflexivity. Qed.

Section KexecPinTrace.
  (* [FsAbsReadFire]'s binder list, verbatim -- the one every fire lemma in
     this cone is written at, and the kexec cone's own minus nothing. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE HONEST PREMISE: THE PINS *WITH THE CHAIN*                   *)
  (* =================================================================== *)

  (*  [SpecKexecPin.kxp_view_pin] with [FsInitPinBoot.era0_pins]' THIRD
      conjunct restored (see the header).  The two pure facts in front are
      the chain's endpoints, read off [arun] once by whoever builds this;
      they are carried rather than re-derived because the walk's answer is
      consumed at a point where no authority is open.                      *)
  (* [kxp_run_pin] now lives in SpecKexecPin (the owner-authorized chain
     repair); this file's original definition moved there verbatim. *)

  Lemma kxp_run_pin_ends Γ pb ds :
    kxp_run_pin Γ pb ds -∗
      ⌜ds !! 0%nat = Some FsImg.ROOTINO
       /\ ds !! length (kxp_path pb) = Some (kxp_ino pb)⌝.
  Proof. iIntros "[$ _]". Qed.

  (* ---- 1a.  THE RECEIPT: the LANDED premise delivers the honest one on
     every one-element path -- which is both era-0 instances
     ([FsInitPin.init_path = ["init"]], [FsShPin.sh_path = ["sh"]]).  So
     nothing about [SpecKexecPin]'s statement has to move for /init or sh;
     what moves is the GENERALITY of its Module Type (header). ---- *)
  Lemma kxp_run_pin_of_view Γ (pb : kx_pin) (s : fname) :
    kxp_path pb = [s] ->
    kxp_view_pin Γ pb -∗ kxp_run_pin Γ pb [FsImg.ROOTINO; kxp_ino pb].
  Proof.
    intros Hps. rewrite /kxp_view_pin /kxp_run_pin.
    iIntros "#Hv". iSplitR.
    { iPureIntro. rewrite Hps. cbn. split; reflexivity. }
    iIntros "!>" (av) "Hst".
    iDestruct ("Hv" $! av with "Hst") as "[Hst %Hpins]".
    iFrame "Hst". iPureIntro. split; [exact Hpins |].
    (* the chain, read off the endpoint pin at a ONE-hop path *)
    destruct Hpins as (Hpath & _). rewrite Hps in Hpath. rewrite Hps.
    rewrite apath_at_cons in Hpath.
    destruct (astep av FsImg.ROOTINO s) as [c |] eqn:Hst; [| discriminate].
    cbn in Hpath. apply Some_inj in Hpath. subst c.
    econstructor; [exact Hst | constructor].
  Qed.

  (* ---- 1b.  ...and the era-0 producer, which needs NO one-element side
     condition: [era0_pins]' own third conjunct IS the chain. ---- *)
  Lemma kxp_run_pin_era0_init Γ :
    era0_view Γ -∗ kxp_run_pin Γ pin_init [FsImg.ROOTINO; INIT_INO].
  Proof.
    rewrite /era0_view /kxp_run_pin.
    iIntros "#Hv". iSplitR.
    { iPureIntro. split; reflexivity. }
    iIntros "!>" (av) "Hst".
    iDestruct ("Hv" $! av with "Hst") as "[Hst %Hs]".
    destruct Hs as (S & HS & ->).
    iFrame "Hst". iPureIntro.
    pose proof (era0_pins_of_snap S HS) as Hp.
    split; [exact (era0_kxp_pins_init _ Hp) |].
    destruct Hp as (_ & _ & Hrun). exact Hrun.
  Qed.

  (* =================================================================== *)
  (*  2.  THE TWO PURE READINGS OFF THE RAW AUTHORITY                     *)
  (*                                                                      *)
  (*  Both conclusions are [⌜ ⌝], so the [ghost_map_auth] the caller       *)
  (*  passes is NOT spent and [ftopN] closes at the very same [I].  This   *)
  (*  is the whole reason the hop below never calls [ftop_astate_ro].      *)
  (* =================================================================== *)

  Lemma kxp_run_pin_read Γ (pb : kx_pin) (ds : list Z)
      (I : gmap Z fs_node) :
    kxp_run_pin Γ pb ds -∗ ghost_map_auth (γtop Γ) 1 I -∗
      ⌜kxp_pins (abs_view I) pb
       /\ arun (abs_view I) FsImg.ROOTINO (kxp_path pb) ds⌝.
  Proof.
    rewrite /kxp_run_pin. iIntros "[_ #Hv] Hta".
    iDestruct (astate_intro with "Hta") as "Hst".
    iDestruct ("Hv" $! (abs_view I) with "Hst") as "[_ $]".
  Qed.

  Lemma kxt_elend_aents Γ (I : gmap Z fs_node) (d : Z) (dq : dfrac)
      (ents : gmap fname Z) :
    ghost_map_auth (γtop Γ) 1 I -∗ elend Γ d dq ents -∗
      ⌜aents (abs_view I) d = Some ents⌝.
  Proof.
    iIntros "Hta HF".
    iDestruct (astate_intro with "Hta") as "Hst".
    iApply (elend_aents with "Hst HF").
  Qed.

  (*  ...and the pinned FILE row, the same way: the payload's fragment
      against the raw authority, [SpecKexecPin.kxp_pins_frag_bytes] with
      [astate] built and never given back (the conclusion is pure).        *)
  Lemma kxt_frag_bytes Γ (pb : kx_pin) (I : gmap Z fs_node) (dq : dfrac)
      (n : fs_node) :
    kxp_pins (abs_view I) pb ->
    ghost_map_auth (γtop Γ) 1 I -∗ top_frag_q Γ dq (kxp_ino pb) n -∗
      ⌜fn_file_bytes n = kxp_bytes pb⌝.
  Proof.
    intros Hpins. iIntros "Hta Hf".
    iDestruct (astate_intro with "Hta") as "Hst".
    iApply (kxp_pins_frag_bytes Γ pb (abs_view I) dq n Hpins with "Hst Hf").
  Qed.

  (* =================================================================== *)
  (*  3.  THE CURSOR, THE HOP, THE FAMILY, THE START                      *)
  (* =================================================================== *)

  (*  PURE, hence persistent: nothing is carried from one instant to the
      next, which is [SpecKexecPin] sect. 4's own argument at the cursor's
      altitude.  [Pmiss] is the SAME predicate -- the walk's failure arm
      hands the cursor straight back, and the pinned run never misses
      anyway (the hop below proves the entry is there). *)
  Definition kxt_P (ds : list Z) (k : nat) (d : Z) : iProp Σ :=
    (⌜ds !! k = Some d⌝)%I.

  (*  ONE HOP.  [ftopN] is opened INSIDE the hop's own [={⊤}=∗], the two
      readings above are taken off the raw authority, the invariant closes
      at the same [I], and the step is [FsAbs.arun_step].                  *)
  Lemma kxt_hop (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (k : nat) (s : fname) :
    kxp_path pb !! k = Some s ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
      ex_hop γfs (kxt_P ds) (kxt_P ds) k s.
  Proof.
    intros Hk. iIntros "#Hi #Hp".
    rewrite /ex_hop /ax_hop. iIntros (d ents dq) "%Hd HF".
    iMod (inv_acc ⊤ ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (kxp_run_pin_read (fs_gamma_L γfs) pb ds I with "Hp Hta")
      as %[_ Hrun].
    iDestruct (kxt_elend_aents (fs_gamma_L γfs) I d dq ents with "Hta HF")
      as %Hents.
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A.
      iFrame "Hta Hla Hpark". iPureIntro. exact Hcl. }
    iModIntro.
    (* the step, purely *)
    destruct (arun_step _ _ _ _ _ _ Hrun Hk) as (c1 & c2 & H1 & H2 & H3).
    assert (Hc1 : c1 = d) by (rewrite Hd in H1; by apply Some_inj in H1).
    subst c1. rewrite /astep Hents /= in H3.
    rewrite H3 /kxt_P. iFrame "HF". iPureIntro. exact H2.
  Qed.

  (*  THE FAMILY, at any suffix index.  [big_sepL_intro] applies because
      the two resources the hop needs are both persistent.                 *)
  Lemma kxt_hops (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (pl : list (bv 8)) (n : nat) :
    path_elems pl = kxp_path pb ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
      ex_hops_from γfs (kxt_P ds) (kxt_P ds) pl n.
  Proof.
    intros Hpl. iIntros "#Hi #Hp".
    rewrite /ex_hops_from /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj).
    rewrite lookup_drop in Hj.
    assert (Hk : kxp_path pb !! (n + j)%nat = Some s)
      by (rewrite -Hpl; exact Hj).
    iApply (kxt_hop γfs pb ds (n + j)%nat s Hk with "Hi Hp").
  Qed.

  (*  THE START ([FsAbsStart.ex_start]): the deferred one-shot.  The tie is
      discharged from the contract's own [pfun 0 = SLASH] premise, through
      [FsAbsStart.bview_head_slash_intro] at the call site.                *)
  Lemma kxt_start (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (pl : list (bv 8)) :
    path_elems pl = kxp_path pb ->
    pl !! 0%nat = Some SLASH ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
      ex_start γfs (kxt_P ds) (kxt_P ds) pl.
  Proof.
    intros Hpl Hsl. iIntros "#Hi #Hp".
    iDestruct (kxp_run_pin_ends with "Hp") as %[Hd0 _].
    rewrite /ex_start. iIntros (r Hr).
    rewrite (Hr Hsl). iModIntro.
    iSplitR.
    { rewrite /kxt_P. iPureIntro. rewrite -kxt_rootino. exact Hd0. }
    iApply (kxt_hops γfs pb ds pl 0%nat Hpl with "Hi Hp").
  Qed.

  (*  THE ANSWER.  What the walk's success arm hands back is [P L iL] at
      [L = length (path_elems pl)]; the chain's far endpoint says what it
      is.                                                                  *)
  Lemma kxt_answer (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (pl : list (bv 8)) (iL : Z) :
    path_elems pl = kxp_path pb ->
    kxp_run_pin (fs_gamma_L γfs) pb ds -∗
    kxt_P ds (length (path_elems pl)) iL -∗ ⌜iL = kxp_ino pb⌝.
  Proof.
    intros Hpl. iIntros "#Hp %HiL".
    iDestruct (kxp_run_pin_ends with "Hp") as %[_ Hlast].
    iPureIntro. rewrite Hpl in HiL. rewrite HiL in Hlast.
    apply Some_inj in Hlast. exact Hlast.
  Qed.

  (* =================================================================== *)
  (*  4.  THE HEADER VERDICT, ASSEMBLED (the oracle's body)               *)
  (*                                                                      *)
  (*  [SpecKexecPin] sect. 8 (2): what the oracle must answer is           *)
  (*  [kxq_hdr_ok (Some (kxp_ef pb)) (fun j => file_byte data j)], and the *)
  (*  route is [kxp_hdr_of_fv] fired at [fv_of dn data = kxp_bytes pb].    *)
  (*  THAT tie is a fact about the AUTHORITY's row at the payload's inum,  *)
  (*  which is why the oracle premise carries the payload's TOP FRAG       *)
  (*  beside its ride (the seam widening, ProofKexecA).                    *)
  (* =================================================================== *)

  Lemma kxt_pin_bytes (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (dq : dfrac) (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok fsc_cov fsc_logst dn bm data ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
    top_frag_q (fs_gamma_L γfs) dq (kxp_ino pb) (era_node dn bm data) ={⊤}=∗
      top_frag_q (fs_gamma_L γfs) dq (kxp_ino pb) (era_node dn bm data)
      ∗ ⌜fv_of dn data = kxp_bytes pb⌝.
  Proof.
    intros Hok. iIntros "#Hi #Hp Hf".
    iMod (inv_acc ⊤ ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (kxp_run_pin_read (fs_gamma_L γfs) pb ds I with "Hp Hta")
      as %[Hpins _].
    (* the row the payload's fragment names, off the SAME authority -- pure
       conclusion, so [Hta] is not spent and [ftopN] closes at [I]. *)
    iDestruct (kxt_frag_bytes (fs_gamma_L γfs) pb I dq _ Hpins with "Hta Hf")
      as %Hbytes.
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A.
      iFrame "Hta Hla Hpark". iPureIntro. exact Hcl. }
    iModIntro. iFrame "Hf". iPureIntro.
    rewrite -(fv_of_file_bytes_era fsc_cov fsc_logst dn bm data Hok).
    exact Hbytes.
  Qed.

  (*  ...at the WHOLE element, which is the share the payload carries from
      its [ilock] to its [iunlockput] (kexec holds the write arm).         *)
  Lemma kxt_pin_bytes_1 (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok fsc_cov fsc_logst dn bm data ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
    top_frag (fs_gamma_L γfs) (kxp_ino pb) (era_node dn bm data) ={⊤}=∗
      top_frag (fs_gamma_L γfs) (kxp_ino pb) (era_node dn bm data)
      ∗ ⌜fv_of dn data = kxp_bytes pb⌝.
  Proof.
    intros Hok. rewrite !top_frag_1.
    exact (kxt_pin_bytes γfs pb ds (DfracOwn 1) dn bm data Hok).
  Qed.

  (*  THE ORACLE'S BODY, at the pinned inum: [ProofKexecA]'s widened row
      with [HD := Some (kxp_ef pb)] and [XCH := ⌜False⌝] -- there is no
      lost arm ([SpecKexecPin] sect. 4: the premise is not a cancellable
      resource, so nothing can invalidate it mid-walk).  The verdict is
      [SpecKexecPin.kxp_hdr_of_fv] fired at the tie above.                 *)
  Lemma kxt_hdr_verdict (γfs : fs_names) (pb : kx_pin) (ds : list Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok fsc_cov fsc_logst dn bm data ->
    (64 <= length (kxp_bytes pb))%nat ->
    ftop_inv γfs -∗ kxp_run_pin (fs_gamma_L γfs) pb ds -∗
    fv_ride (kxp_ino pb) (fv_of dn data)
    ∗ top_frag (fs_gamma_L γfs) (kxp_ino pb) (era_node dn bm data) ={⊤}=∗
      fv_ride (kxp_ino pb) (fv_of dn data)
      ∗ top_frag (fs_gamma_L γfs) (kxp_ino pb) (era_node dn bm data)
      ∗ □ (⌜kxq_hdr_ok (Some (kxp_ef pb)) (fun j => file_byte data j)⌝
           ∨ ⌜False⌝).
  Proof.
    intros Hok Hlen. iIntros "#Hi #Hp [Hride Htop]".
    iMod (kxt_pin_bytes_1 γfs pb ds dn bm data Hok with "Hi Hp Htop")
      as "[Htop %Hb]".
    iModIntro. iFrame "Hride Htop". iModIntro. iLeft. iPureIntro.
    exact (kxp_hdr_of_fv pb dn data Hb Hlen).
  Qed.

End KexecPinTrace.
