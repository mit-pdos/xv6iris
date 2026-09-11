(* UexecExecMint.v -- THE GENERIC MINT: the U-mode trap loop's own slot at
   every key, and it costs the kernel nothing.

   WHAT IT COSTS: THE SUPPLY, AND NOTHING ELSE.  Since the ARM the returning
   arm demands the process's bundle for the number it is at
   ([UexecSG.sbundle]).  At the kernel's instance ([UexecExecInst]) the only
   number with a bundle is exec, and exec's is
   [SpecSysExec.sys_exec_au_pre] at the trapping key: open's walk premise
   and open's commit -- both handed back at [True] receipts by
   [FsAbsInvFire.fsabs_exec_half], which is a closed fact -- beside the slot
   wand the kernel fires for the NEW image.  A generic slot family pays that
   wand at every key, so exec's bundle spends nothing.  What the two lemmas
   below take is the class's [ssupply] itself ([AppInv.app_sup]): a generic
   process may make ANY syscall, and the numbers whose bundles move the
   abstract state are paid out of that credential.  It is a PREMISE and not
   a closed fact -- see [UexecSG.v]'s "[ssupply] IS NOT IN [uvb]" and
   [AppInv]'s [app_sup_raw]: it is born at boot as a Coq hypothesis of the
   generic system theorem and handed to each mint site.

   SO THERE IS NO LIFT LEFT.  The exec channel was once a SECOND parallel
   fixpoint and this file's work was carrying a plain slot up to it by Loeb.
   The two tiers are one: what remains is [UexecCond.cond_entry_slot] with
   its two premises discharged from the instance -- [psok] is [True] at every
   number, and [UkRun.udep]'s key-free law is the class's
   [UexecSG.sbundle_of_supply_ne]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UexecSlot.
Require Import UexecWp.
Require Import UexecRet.
Require Import UexecCond.       (* [cond_entry_slot] -- the plain generic slot *)
Require Import FirstTok.        (* in the require block for FsAbsInvFire's
                                   sake; nothing here names its [fsabs_env] *)
Require Import UexecExecInst.   (* the class INSTANCE: [uexecSG_xv6] / [uprogSG_gen] *)
Require Import UkRun.           (* [udep] -- the supplier and its key-free law *)
Require Import AppInv.          (* [app_sup] -- the credential both mints take *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UexecExecMint.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* THE PROGRAM-SIDE DEPOSIT DATA the generic slot runs on: the supplier IS
     the supply ([UexecExecInst.uprogSG_gen]'s [Dsup]) and the key-free
     minting law is the class's own [sbundle_of_supply_ne], which admits
     every number but exec. *)
  Lemma udep_gen : app_sup -∗ udep.
  Proof.
    rewrite /udep /Dsup /= /xv6_ssupply.
    iIntros "#Hsup". iSplitR; [ iModIntro; iExact "Hsup" | ].
    iPureIntro. intros n W _ Hne.
    exact (sbundle_of_supply_ne uslot n W Hne).
  Qed.

  (* the loop's mint: the generic slot at every key, out of the supply.
     [UexecCond.cond_entry_slot]'s [psok] premise is the instance's own
     (every number is admitted); its [□ ssupply] is the credential. *)
  (* THE FAMILY IS INDEXED BY THE PAY FACT ([UexecCond.cond_entry_slot]'s
     own premise): a slot at EVERY key is a slot that may trap at exit at
     every key, and exit's deposit is a payment.  At the trivial payload,
     which is the only one a generic process has. *)
  Lemma uslot_mint :
    app_sup -∗ □ uexec_wp -∗
    □ (∀ W : uvis, my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W).
  Proof.
    iIntros "#Hsup #Hgen".
    iDestruct (udep_gen with "Hsup") as "#Hdep".
    iIntros "!>" (W) "#Hpay".
    iApply (UexecCond.cond_entry_slot W ltac:(intros k _; exact I)
              with "Hdep [] Hgen Hpay").
    rewrite /ssupply /= /xv6_ssupply. iModIntro. iExact "Hsup".
  Qed.
End UexecExecMint.
