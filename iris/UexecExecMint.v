(* UexecExecMint.v -- THE GENERIC MINT: the U-mode trap loop's own slot at
   every key, and it costs the kernel nothing.

   WHY IT IS FREE.  Since the ARM the returning arm demands the process's
   bundle for the number it is at ([UexecSG.sbundle]).  At the kernel's
   instance ([UexecExecInst]) the only number with a bundle is exec, and
   exec's is [SpecSysExecAU.sys_exec_au_pre] at the trapping key: open's walk
   premise and open's commit -- both handed back at [True] receipts by
   [FsAbsInvFire.fsabs_exec_half], which is a closed fact -- beside the slot
   wand the kernel fires for the NEW image.  A generic slot family pays that
   wand at every key.  So the class's [ssupply] is [True] there and its
   [sbundle_of_supply] asks for nothing.

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
Require Import SpecKexecAU.
Require Import SpecSysExecAU.
Require Import FsAbsInvFire.    (* [fsabs_exec_half] *)
Require Import FirstTok.        (* [FirstTok.fsabs_env] -- spelled QUALIFIED below:
                                   [FsAbsInv] (imported after it) exports a
                                   Γ-indexed [fsabs_env] of its own *)
Require Import PieceFam.       (* [pfam]/[pfam_triv]: the one-shot piece's pair *)
Require Import UexecExecInst.   (* the class INSTANCE: [uexecSG_xv6] / [uprogSG_gen] *)
Require Import UkRun.           (* [udep] -- the supplier and its key-free law *)
Require Import FsBytesGamma.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UexecExecMint.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* THE PROGRAM-SIDE DEPOSIT DATA the generic slot runs on, and at this
     instance it costs nothing: the supplier is [True] and the key-free
     minting law is the class's own [sbundle_of_supply_ne]. *)
  Lemma udep_gen : ⊢ udep.
  Proof.
    rewrite /udep /Dsup /= /xv6_ssupply.
    iSplitR; [ done | ].
    iPureIntro. intros n W _ Hne.
    exact (sbundle_of_supply_ne uslot n W Hne).
  Qed.

  (* the loop's mint: the generic slot at every key.  Both of
     [UexecCond.cond_entry_slot]'s premises are the instance's own --
     every number is admitted, and the supply is free. *)
  Lemma uslot_mint : □ uexec_wp -∗ □ (∀ W : uvis, uslot W).
  Proof.
    iIntros "#Hgen".
    iDestruct udep_gen as "#Hdep".
    iIntros "!>" (W).
    iApply (UexecCond.cond_entry_slot W ltac:(intros k _; exact I)
              with "Hdep [] Hgen").
    rewrite /ssupply /= /xv6_ssupply. done.
  Qed.
End UexecExecMint.
