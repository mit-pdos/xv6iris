(* UexecExecMint.v -- THE GENERIC MINT AT THE ENRICHED SLOT: what the U-mode
   trap loop needs of the kernel to run on [UexecRetExec.uslot_x], and it is
   ONE persistent fact -- the application-side abstract-state invariant
   [FirstTok.fsabs_env], projected off the residue the loop already holds.

   WHAT IS MINTED, AND WHY IT IS FREE.  The exec bundle a process hands over
   at its exec ecall ([UexecExecInst.exec_xbundle]) is
   [SpecSysExecAU.sys_exec_au_pre] at the trapping key: open's walk premise
   and open's commit -- both at [True] receipts out of [fsabs_inv] alone
   ([FsAbsInvFire.fsabs_exec_half]) -- beside the slot wand the kernel fires
   for the NEW image.  A generic slot family ([∀ W', uslot_x W']) pays that
   wand at every key, so a generic bundle costs nothing but the invariant.

   THE LIFT.  UexecRetExec.v's header says [uslot W -∗ uslot_x W] is not
   provable outright: lifting a plain program would have to conjure a bundle
   at every future exec trap.  WITH the generic bundle in hand it is, by Loeb
   through the ▷ in [ukont_x]: under the later, the enriched kernel promise
   is met from the plain one by converting the incoming plain return with
   [uexec_ret_x_of_bundle], the bundle minted here and the slot upgrader
   being the Loeb hypothesis itself.  So the loop's mint ([uslot_x_mint]) is
   the plain generic slot ([UexecCond.cond_entry_slot]) lifted once. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import Xv6Cameras.
Require Import BioDefs.
Require Import LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.
Require Import ByteBuf.
Require Import FsBlocks.
Require Import FsTree.
Require Import PathElems.
Require Import SpecKexec.
Require Import SpecSysExec.
Require Import ElfFile.
Require Import UmodeAbi.
Require Import UserFd.
Require Import UexecSlot.
Require Import UexecWp.
Require Import UexecRet.
Require Import UmodeText.
Require Import UexecRetExec.
Require Import UexecCond.       (* [cond_entry_slot] -- the plain generic slot *)
Require Import SpecSysOpenAU.
Require Import SpecKexecAU.
Require Import SpecSysExecAU.
Require Import FsAbsInvFire.    (* [fsabs_exec_half] *)
Require Import FirstTok.        (* [FirstTok.fsabs_env] -- spelled QUALIFIED below:
                                   [FsAbsInv] (imported after it) exports a
                                   Γ-indexed [fsabs_env] of its own *)
Require Import UexecExecInst.   (* the [xbundle] instance, [xbundle_intro] *)
Require Import FsAbsInv.
Require Import FsAbs.
Require Import FsBytesGamma.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section UexecExecMint.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  (* exec's AU bundle at a generic slot family: the fs half out of the
     invariant, the slot half out of the family *)
  Lemma fsabs_exec_pre (S : uvis -> iProp Σ) :
    FirstTok.fsabs_env -∗
    (∀ W' : uvis, S W') -∗
    ∀ (cw : Z) (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate),
      sys_exec_au_pre S (fs_gamma_L fsc_fs) fsc_fs cw
        (fun _ _ => True%I) (fun _ _ => True%I) (fun _ _ _ => True%I) M av sts.
  Proof.
    iIntros "#Henv Hs" (cw M av sts).
    iDestruct "Henv" as (γa) "[#Hinv #Hlic]".
    iDestruct (fsabs_exec_half (fs_gamma_L fsc_fs) _ fsc_fs cw with "Hinv Hlic")
      as "[#Hwalk #Hcommit]".
    rewrite /sys_exec_au_pre.
    iSplitR; [iExact "Hwalk" |].
    iSplitR; [iExact "Hcommit" |].
    rewrite /sys_exec_slot_pre. iIntros (na alen afun) "_".
    rewrite /exec_slot_pre. iIntros (av' i f nl W') "_ _ _".
    iApply "Hs".
  Qed.

  (* the process's exec bundle, at any key *)
  Lemma xbundle_mint (W : uvis) :
    FirstTok.fsabs_env -∗ (∀ W' : uvis, uslot_x W') -∗ xbundle uslot_x W.
  Proof.
    iIntros "#Henv Hs".
    iApply (xbundle_intro uslot_x W (fun _ _ => True%I) (fun _ _ => True%I)
              (fun _ _ _ => True%I)).
    iApply (fsabs_exec_pre uslot_x with "Henv Hs").
  Qed.

  (* THE LIFT (header): a plain slot is an enriched one, given a generic
     plain family to mint the bundle's slot wand from.  Loeb through the
     ▷ in [ukont_x]. *)
  Lemma uslot_x_lift_of :
    FirstTok.fsabs_env -∗
    □ (∀ W : uvis, uslot W) -∗
    □ (∀ W : uvis, uslot W -∗ uslot_x W).
  Proof.
    iIntros "#Henv #Hgen".
    iLöb as "IH".
    iIntros "!>" (W) "Hs".
    rewrite uslot_x_unfold.
    iEval (rewrite uslot_unfold) in "Hs".
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    iApply ("Hs" $! h xi C pt Rfd Rut HRut with "[%] [%] [-]");
      [exact Hlo | exact Hpm |].
    rewrite /uvb /uvb_F.
    iEval (rewrite /uvb_x /uvb_x_F) in "Hb".
    iDestruct "Hb" as
      "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    (* the plain kernel promise, from the enriched one: precompose the
       return with the bundle-supplied injection *)
    rewrite /ukont_F.
    iEval (rewrite /ukont_x_F) in "Hk".
    iNext.
    rewrite /ukb_F.
    iEval (rewrite /ukb_x_F) in "Hk".
    iIntros (W' sc stv) "%Hp %Hs' %Hf' %Hc' (Htm & Hfr & Hret)".
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [%] [Htm Hfr Hret]");
      [exact Hp | exact Hs' | exact Hf' | exact Hc' |].
    iFrame "Htm Hfr".
    iApply (uexec_ret_x_of_bundle with "IH [] Hret").
    iApply (xbundle_mint with "Henv").
    iIntros (W''). iApply "IH". iApply "Hgen".
  Qed.

  Lemma uslot_x_lift :
    FirstTok.fsabs_env -∗ □ uexec_wp -∗ □ (∀ W : uvis, uslot W -∗ uslot_x W).
  Proof.
    iIntros "#Henv #Hgen".
    iApply (uslot_x_lift_of with "Henv").
    iIntros "!>" (W). iApply (UexecCond.cond_entry_slot W with "Hgen").
  Qed.

  (* the loop's mint: the plain generic slot, lifted *)
  Lemma uslot_x_mint :
    FirstTok.fsabs_env -∗ □ uexec_wp -∗ □ (∀ W : uvis, uslot_x W).
  Proof.
    iIntros "#Henv #Hgen".
    iDestruct (uslot_x_lift with "Henv Hgen") as "#Hlift".
    iIntros "!>" (W). iApply "Hlift".
    iApply (UexecCond.cond_entry_slot W with "Hgen").
  Qed.

  (* ...and the return channel lifted with it: what the loop's ENTRY
     needs, where userret's dovetail hands it a plain return *)
  Lemma uexec_ret_x_lift :
    FirstTok.fsabs_env -∗ □ uexec_wp -∗
    □ (∀ (sc : mword 64) (W : uvis), uexec_ret sc W -∗ uexec_ret_x sc W).
  Proof.
    iIntros "#Henv #Hgen".
    iDestruct (uslot_x_lift with "Henv Hgen") as "#Hlift".
    iDestruct (uslot_x_mint with "Henv Hgen") as "#Hmk".
    iIntros "!>" (sc W) "Hret".
    iApply (uexec_ret_x_of_bundle with "Hlift [] Hret").
    iApply (xbundle_mint with "Henv").
    iIntros (W''). iApply "Hmk".
  Qed.

End UexecExecMint.
