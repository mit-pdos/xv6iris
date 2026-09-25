(* ===================================================================== *)
(* UTreeAdequacy.v -- THE SECOND APPLICATION, CLOSED (lane TL-5).         *)
(*                                                                       *)
(* [App.xv6_app_adequacy] at [AppTree.app_tree]: every obligation of the *)
(* record discharged, the functor list fixed at a concrete [treeAppΣ],    *)
(* the disk at the literal mkfs image, and NOTHING left as a premise but  *)
(* the hardware setup.  [UInitBootAdequacy.v] is the mould, one           *)
(* application over.                                                     *)
(*                                                                       *)
(* WHAT CLOSES [Hinit_boot], AND IT IS THE HAND-DOWN                      *)
(* (design/user-tree.md section 8.4, as amended by 9.1).  The tree        *)
(* claim's taint had no mint that a process could reach: the counter sat  *)
(* in the ledger and [app_turn] was [emp], so [AppInv.app_sup] was        *)
(* unobtainable and every route to the first process's exec bundle was    *)
(* dead.  Lane TL-5's hand-down fixes exactly that -- [AppTree]'s fixed   *)
(* part is now an ERA-LICENCE REGISTRY whose authority the ledger keeps   *)
(* and whose rows [al_pow] files one per era, and [App.app_turn] carries  *)
(* one to <init>.  [tree_Hinit_boot] below spends it: the licence mints   *)
(* the taint ([AppTree.tree_sup_of_bump]), the taint IS the supply at     *)
(* this claim ([AppTree.tree_sup_of_taint]), and the supply buys the      *)
(* generic bundle ([SystemAdequacy.init_boot_of_sup]).                    *)
(*                                                                       *)
(* SO THE ERA'S FIRST PROCESS IS NOT VERIFIED AGAINST THE TREE CLAIM, AND *)
(* THE CLAIM RECORDS IT -- that is the honest arm section 8.4 named, and  *)
(* it is what makes the tree application a real second instance of the    *)
(* whole-system theorem rather than a definition with no theorem.  A      *)
(* VERIFIED <init> at this claim (section 9.2) moves the mint from this   *)
(* file to <init>'s own exec of /sh; the header of section 7 of           *)
(* [AppTree.v] and the lane note say what that costs.                     *)
(*                                                                       *)
(* WHY THE CONCLUSION IS [True], AND IT IS NOT A PLACEHOLDER THAT A       *)
(* VERIFIED <init> WOULD FILL.  [App.app_phi] is a [Prop] over the        *)
(* machine state and the OBSERVABLE TRACE, and the tree claim's break --  *)
(* an unpaid file-system move -- is witnessed by NO trace event (design   *)
(* section 8.2's own finding, which is why the taint is a resource and    *)
(* not a ledger reading).  So “the namespace is a rooted partition, or    *)
(* the taint has been minted” is not a proposition [app_phi] can state:   *)
(* the left disjunct is readable off the claim at [Hphi] (the route is    *)
(* recorded in the lane note -- the durable snapshot's view, through      *)
(* [SystemAdequacy.xv6_slot]'s two halves) and the right one is a ghost   *)
(* fact about [c], which [app_phi] does not even take.  What a verified   *)
(* <init> buys is therefore a stronger DISCHARGE, not a stronger [φ].     *)
(*                                                                       *)
(* WHY IT IS ITS OWN FILE and not the bottom of [AppTree.v]:              *)
(* [UInitBootAdequacy.v]'s reason verbatim -- this statement needs the    *)
(* adequacy cone ([RiscvAdequacy.boot_fixedGS], [SystemAdequacy.          *)
(* xv6_slot], [FsImgDisk.fsimg_P]) and [AppTree.v] is a proofmode-heavy   *)
(* file that must not import it.                                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.             (* [cons_licence] / [cons_licence_triv] *)
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
Require Import UserFd.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import InitBoot.           (* [init_boot_bundle] *)
Require Import SystemAdequacy.     (* [init_boot_of_sup], [xv6_slot] *)
Require Import SpecConsoleintr.    (* [cons_echo_shift_triv] *)
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.                (* [xv6_app_adequacy] and the record *)
Require Import AppTree.            (* [app_tree] and its obligations *)
Require Import TreeImg.            (* [tree_Happ_init] -- TL-4's era-0 mint *)
Require Import InodeInv.           (* [ROOTINO] *)

Local Open Scope Z_scope.

Section TreeAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  (* the tree claim's own cameras (lane TL-5: four, the fourth being the
     era-licence registry the hand-down files its rows in) *)
  Context `{!treeG Σ}.

  (* =================================================================== *)
  (*  1.  [Hinit_boot] AT THE TREE CLAIM                                  *)
  (* =================================================================== *)

  (* [App.al_programs] at [app_tree], and it is three lines of content:
     the era's licence is spent for the taint, the taint is the supply,
     and the supply buys the generic bundle.  The two equations the
     theorem hands over are used exactly as [App.app_triv_init_boot] uses
     them -- to read the machine's kill credential and console claim off
     THIS application's interface, which is the generic one. *)
  Lemma tree_Hinit_boot
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (c : app_fixed app_tree) (r : app_names app_tree) :
    @file_app Σ HF = MkAppcfg (app_names app_tree) (app_pred app_tree c) r ->
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_tree c ->
    @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
    ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_tree c (S gen_id) r -∗
      app_turn app_tree c (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0.
  Proof using ufdG0.
    intros Heq Hiface _.
    (* the console claim and the kill credential, off the one equation:
       both are the GENERIC slot's at this record ([AppTree]'s
       [app_iface_triv]) *)
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = cons_res_triv).
    { rewrite /riscv_cons_res Hiface.
      by cbn [app_tree app_ifc app_iface_triv ai_cons]. }
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR) = kill_cred_triv).
    { rewrite /app_taint Hiface.
      by cbn [app_tree app_ifc app_iface_triv ai_kill]. }
    iIntros "_ _ Hturn".
    (* THE LICENCE IS SPENT HERE, and this is the only place the tree
       application ever reaches [AppInv.app_sup]. *)
    iEval (cbn [app_tree app_turn]) in "Hturn".
    iMod (tree_sup_of_bump c r with "Hturn") as "#Hsup".
    iModIntro.
    iApply (init_boot_of_sup (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0).
    - (* the supply, at the era's record equation *)
      rewrite /AppInv.app_sup Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names
           app_tree app_pred app_names].
      iExact "Hsup".
    - (* the kill credential, free at the trivial interface *)
      rewrite Hkill /kill_cred_triv. done.
  Qed.

  (* =================================================================== *)
  (*  2.  THE RECORD'S LAWS, AS THE INSTANCE                              *)
  (*                                                                      *)
  (*  [UInitBootAdequacy.echo_laws]'s shape: eleven fields, each checked   *)
  (*  against a type that is already known.  Nine of them are [AppTree.v]  *)
  (*  section 6's lemmas; the two written out are the UART ledger steps,   *)
  (*  which are [App.app_triv]'s at a ledger that is not [emp] -- this     *)
  (*  application's ledger is the registry's authority and does not read   *)
  (*  the history, so both steps hand it straight back.                    *)
  (* =================================================================== *)
  Global Instance tree_laws : App.xv6_app_laws app_tree.
  Proof using ufdG0.
    split.
    - exact app_tree_birth.
    - exact app_tree_Rt.
    - exact app_tree_kill.
    - exact app_tree_cons_sup.
    - exact app_tree_R0.
    - exact app_tree_pow.
    - (* [al_tx]: the console claim is [emp], the tag is trivial, and the
         ledger is history-free, so the drain returns its three inputs *)
      intros HRg GEN HFi c r i γ _ _.
      cbn [app_tree app_R app_ifc app_iface_triv ai_cons app_cons].
      iIntros "!>" (h b u u' ho H) "_ _ _ _ _ _ _ _ Ho Hg HR".
      iModIntro. iFrame "Ho Hg HR".
    - (* [al_rx]: likewise, and the tag says nothing *)
      intros HRg GEN HFi c r i γ _ _. rewrite /app_tag.
      cbn [app_tree app_R app_ifc app_iface_triv ai_tag].
      iIntros "!>" (h b u u') "_ _ _ Hg HR". iModIntro. iFrame "Hg HR".
    - exact app_tree_boot.
    - exact @tree_Hinit_boot.
    - (* [al_echo]: the shift justifies itself at the trivial console
         claim, exactly as the generic application's does *)
      intros HRg c Hiface. iIntros (GEN XI).
      iApply (SpecConsoleintr.cons_echo_shift_triv (XI := XI)).
      rewrite /riscv_cons_res Hiface.
      by cbn [app_tree app_ifc app_iface_triv ai_cons].
  Qed.

  (* =================================================================== *)
  (*  3.  THE THEOREM, over an abstract [Σ] and at the image's facts      *)
  (* =================================================================== *)

  Theorem tree_adequacy_at_img
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_tree g2 κs.
  Proof using bioslotGpreS0 fdslotGpreS0 fileGpreS0 irefslotGpreS0 pavGpreS0 riscvGpreS0 ufdG0 wchGpreS0 xv6G0.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE ([UInitBootAdequacy]'s measured
       rule): handing [xv6_app_adequacy] its arguments at once makes the
       elaborator unify each against a record field whose type it is still
       solving. *)
    refine (xv6_app_adequacy Σ g sb nib cov app_tree
              (tree_Happ_init g sb nib cov Himg Hdk Hsb Hcov)
              _ Hgen0 Hpow0 Himg n κs t2 g2 Hn).
    (* [Hphi]: the conclusion is [True] -- see the header for why it is not
       a placeholder *)
    intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h.
    iIntros "_ _ _ _ _". iModIntro. iPureIntro.
    cbn [app_tree app_phi]. exact Logic.I.
  Qed.

End TreeAdequacy.

(* ===================================================================== *)
(*  4.  THE CLOSED COROLLARY                                             *)
(*                                                                       *)
(*  [UInitBootAdequacy.echo_adequacy_echoΣ]'s two closures, one           *)
(*  application over: the FUNCTOR LIST is a concrete one, so “the ghost   *)
(*  state is realisable” is CHECKED and the statement is not vacuous      *)
(*  (durable-notes, the Vacuity section); and the IMAGE facts follow from *)
(*  the one hardware equation by [SystemAdequacy.fsimg_image_wf] and the  *)
(*  definitional [fs_blocks fsimg_dk = fsimg_P].                          *)
(*                                                                       *)
(*  WHAT IT DOES NOT CLOSE, and cannot: [Hdisk] -- the machine is         *)
(*  switched on with the disk mkfs wrote.                                 *)
(*                                                                       *)
(*  THE CONCLUSION IS SPELLED OUT rather than left behind the record, and *)
(*  the record is deliberately NOT named in it ([App.                     *)
(*  xv6_app_adequacy_triv_xv6Σ]'s own rule: [app_phi app_tree] would      *)
(*  unfold through the record at the functor list and put the whole ghost *)
(*  layer into the STATEMENT's trusted base).  What the theorem SAYS is   *)
(*  therefore reducibility; what it CHECKS is that the tree application   *)
(*  -- [AppTree.tree_pred], “the live namespace is a rooted tree          *)
(*  partitioned among its owners, or the taint records an unpaid mover”   *)
(*  -- pays every obligation of the whole-system theorem at the real      *)
(*  image, era 0's claim included ([TreeImg.tree_Happ_init]).             *)
(* ===================================================================== *)

Definition treeAppΣ : gFunctors :=
  #[ xv6Σ                (* the system theorem's own list                 *)
   ; bioslotΣ            (* not in [xv6Σ]: the bio escrow's slot camera   *)
   ; treeΣ               (* the tree claim's four cameras                 *)
   ].

Corollary tree_adequacy_treeΣ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2.
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                   fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (proj1 (tree_adequacy_at_img (Σ := treeAppΣ) g fsimg_sb fsimg_nib
                  fsimg_cov Hgen0 Hpow0 Himg Hdk eq_refl eq_refl
                  n κs t2 g2 Hn)).
Qed.
