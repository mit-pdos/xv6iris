(* ===================================================================== *)
(*  UShCatPay.v -- LANE EXEC-CAT, THE SUPPLY: sh's forked RIGHT child     *)
(*  runs /cat on the paid entry.                                          *)
(*                                                                       *)
(*  [UShEchoPay.v] is the mould: the U-tier exec rule                     *)
(*  ([ExecRun.udepw_at_refR_of_sup]) with sh's own supply plugged in --   *)
(*  the node read off the lent heap, the PIN as (W)'s supplier            *)
(*  ([ExecRun.exec_walk_of_pin] at [FsCatPin.era0_cat_pins], which        *)
(*  [AppPipeCons.pipe_cat_pins_acc] hands the pipeline claim), the        *)
(*  resolving arm as (E), the taint arm at the chosen payload, and the    *)
(*  refund -- the ledger fragment and the lend, WHOLE.                    *)
(*                                                                       *)
(*  WHAT LEFT (lane user-once, C2).  The supply at a caller's entry      *)
(*  ([sh_exec_sup_cat_of_entry]) and the paid arm it fed                 *)
(*  ([wp_kshr_exec_cat_paid_of_entry], through [UkShCat]'s twin of       *)
(*  echo's exec arm), with the right command's readings over [ExecArgs],  *)
(*  had no consumer: the union's pipe stages exec cat through the ONE     *)
(*  arm [UkShEcho.wp_kshr_exec_x_at] at the shifted base, and take their  *)
(*  entry from the tree route.  What stays is cat's path and the pin that *)
(*  resolves it (section 1) and the slot ingredients (section 2), which   *)
(*  the union's rounds and the boot read.  (A word-list reading at one    *)
(*  word is vacuous: [UkShCat.cat_line_premises_absurd] /                 *)
(*  [UkShCat.cat_line_head_absurd].)                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import UexecSlot UexecRet.
Require Import UserFd.
Require Import ChildTok.
Require Import ElfUser.
Require Import PathElems ArgPath.
Require Import FsCfg.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import FsCatPin.
Require Import FileFsPure.
Require Import PinnedExec.
Require Import UexecSG.
Require Import CtxIdDefs.
Require User.ShSyms.
Require Import UkShCat.            (* the (W) half this supply feeds *)
Require User.CatSyms.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  CAT'S PATH, AND THE PIN THAT RESOLVES IT                          *)
(*                                                                       *)
(*  [UShEcho]'s sections 1-2 at /cat.  argv[0] is the pipe line's right   *)
(*  word, whose three bytes are "cat"; the pin speaks of                  *)
(*  [FsCatPin.cat_path], a list of NAMES, and [PathElems.path_elems]      *)
(*  joins them.                                                          *)
(* ===================================================================== *)
Definition cat_pl : list (bv 8) := FsImgCheck.fname_cat.

Lemma cat_path_elems : path_elems cat_pl = FsCatPin.cat_path.
Proof using . vm_compute. reflexivity. Qed.

Lemma cat_pl_len : length cat_pl = 3%nat.
Proof using . reflexivity. Qed.

(* ...and the bytes ARE the command name the pipe line's right side
   spells ([UkShPipeLex.ushq_cat], through [UkShCat.cmd_cat]) -- which is
   what ties the pin to what sh actually passes to exec. *)
Lemma cat_pl_line (j : nat) :
  (j < 3)%nat -> cat_pl !!! j = UkShCat.cmd_cat !!! j.
Proof using .
  intro Hj.
  do 3 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

Lemma cat_pl_shape : arg_path_shape cat_pl.
Proof using .
  split; [ vm_compute; reflexivity | ].
  intros j b Hj.
  destruct j as [| [| [| j]]]; cbn in Hj; try discriminate Hj;
    injection Hj as <-;
    (intro Hc; apply (f_equal bv_unsigned) in Hc;
     vm_compute in Hc; discriminate Hc).
Qed.

(* no byte of the command name is a NUL, which is what pins argv[0]'s
   LENGTH: a [bb_cstr] that stopped early would have to find one *)
Lemma cmd_cat_nonul (j : nat) :
  (j < 3)%nat -> UkShCat.cmd_cat !!! j <> (mword_of_int 0 : mword 8).
Proof using .
  intro Hj.
  do 3 (destruct j as [| j];
        [ intro Hc; apply (f_equal bv_unsigned) in Hc;
          vm_compute in Hc; discriminate Hc | ]). lia.
Qed.

Lemma sh_cat_pin_resolves :
  pin_resolves FsCatPin.era0_cat_pins FsImg.ROOTINO cat_pl
    [FsImg.ROOTINO; FsCatPin.CAT_INO] FsCatPin.CAT_INO
    ElfUser.cat_elf 1%nat.
Proof using .
  split_and!.
  - (* "cat" is RELATIVE, so the walk starts at the cwd -- the root *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (cat_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite cat_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite cat_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsCatPin.cat_bytes_elf. reflexivity.
Qed.

Section UShCatPay.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here, exactly as in [UShEcho] and [UShEchoPay]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  (* ...EXCEPT [uprogSG], WHICH IS A SECTION VARIABLE (design SS4.3z item
     2, lane SH-PIPE-ROUND-11 finding (3)).  The entry this file's
     supply takes is the ENTERED PROGRAM's, and a verified
     program runs at its own deposit data ([UexecExecInst.uprogSG_free]),
     not at the ambient generic instance whose only [udep] producer is the
     taint.  Nothing is pinned here: the round instantiates at
     [uprogSG_free], the file era at its own, and every landed statement is
     byte-identical after [(PS := _)].  The DEPOSIT RULE this file applies
     ([ExecRun.udepw_at_refR_of_sup]) is [uprogSG]-FREE -- [UkRun.
     udepw_at_ref] names only [uslot] and [sbundle_pay_ref] -- so the
     conclusion [UkShCat.sh_exec_sup_cat_at] does not move either.
     [sh_cat_slot] below reads no instance at all and is unchanged. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  2.  THE INGREDIENTS -- [UShEcho.sh_echo_slot] at /cat               *)
  (* =================================================================== *)
  Definition sh_cat_slot (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FsCatPin.era0_cat_pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Global Instance sh_cat_slot_persistent T : Persistent (sh_cat_slot T).
  Proof using . rewrite /sh_cat_slot. apply _. Qed.

  (* ...AND THE ONE SEAM A PIPELINE ERA HAS TO MEET.  The claim's law is
     stated at the WHOLE of [FileFsPure.file_fs_pure] (that is what
     [AppPipeCons.pipe_fs_pure_acc] hands out, and [pipe_cat_pins_acc] is
     the same projection one level up), so this is the projection under
     the law's own box. *)
  Definition sh_cat_slot_of_fs_pure (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FileFsPure.file_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Lemma sh_cat_slot_of_fs_pure_holds (T : iProp Σ) :
    sh_cat_slot_of_fs_pure T -∗ sh_cat_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)".
    rewrite /sh_cat_slot. iFrame "Hinv Hgen".
    iModIntro. iIntros (v) "Hp".
    iDestruct ("Hcl" $! v with "Hp") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (FileFsPure.file_fs_pure_cat v Hpure).
    - iRight. iExact "HT".
  Qed.

End UShCatPay.
