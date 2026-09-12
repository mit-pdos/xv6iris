(* ===================================================================== *)
(* UInitBoot.v -- THE FIRST PROCESS'S EXEC BUNDLE, FOR A CONSTRAINING    *)
(* APPLICATION (lane E2, ARM-c (1b)).                                    *)
(*                                                                       *)
(* [InitBoot.init_boot_bundle] is what the whole-system theorem asks its  *)
(* application for ([App.xv6_app_adequacy]'s [Hinit_boot]): the kernel's  *)
(* own caller-side bundle for [kexec("/init")] at forkret's boot arm.     *)
(* The GENERIC application discharges it from the trivial mint            *)
(* ([InitBoot.init_boot_bundle_triv]); this file is the other             *)
(* discharge -- a PINNED exec at "/init", whose slot piece answers with   *)
(* /init's OWN verified entry ([UInitKernel.init_slot_of_kexec]) rather   *)
(* than with a generic family.                                           *)
(*                                                                       *)
(* WHY IT IS A SEPARATE FILE FROM [UInitSh.v], which is the same assembly *)
(* one level up (init execing sh): the two differ in exactly ONE place    *)
(* and it is not the pin -- it is WHERE THE ARGUMENTS COME FROM.  sh's    *)
(* exec is a SYSCALL, so its path and argument vector are readings of the *)
(* calling image ([SpecSysExec.exec_path_of] / [exec_args_of]) and the    *)
(* bundle is [sys_exec_au_pre]; /init's is the KERNEL's own call, with a  *)
(* literal path and a literal vector, and the bundle is                   *)
(* [SpecKexec.exec_au_pre].  [PinnedExec.pinned_exec_bundle_boot] is that *)
(* second shape, and [PinnedExec.pex_slot_at] is the identifying step the *)
(* two share.                                                            *)
(*                                                                       *)
(* WHAT IS STILL A PREMISE HERE, and what discharges it:                  *)
(*   the CLAIM LAW at [FsInitPinBoot.era0_pins] -- [AppEcho]'s, through   *)
(*     the era's record equation (the pin is one of the three conjuncts   *)
(*     of [AppEcho.echo_fs_pure], so [echo_fs_pure_acc] gives it);        *)
(*   the CONSTRUCTOR WAND -- [UInitKernel.init_slot_of_kexec] at /init's  *)
(*     own entry premises;                                               *)
(*   the TAINT ARM -- [UexecExecMint.uslot_mint_all] on                   *)
(*     [AppEcho.echo_sup_of_taint];                                       *)
(*   [Pay] -- the LINEAR half: the console reader token the bundle's own  *)
(*     wand hands in ([InitBoot.init_boot_bundle] is a wand from          *)
(*     [ConsoleInv.cons_reader]) beside the era's console credential      *)
(*     (the KEY or the FLAG, [AppEcho.echo_boot]'s two arms).             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedExec.v]'s note: a field instance is inert wherever its
   module is not imported). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.          (* [uslot] -- REQUIRED DIRECTLY (the seal) *)
Require Import UexecSG.
Require Import ElfFile.
Require Import PathElems.
Require Import FsTree.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.             (* [fsc_fs] / [fsc_cons] *)
Require Import ConsoleInv.        (* [cons_reader] *)
Require Import SpecKexec.         (* [exec_au_pre] / [kexec_image_ok] *)
Require Import PieceFam.
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PinnedObs.
Require Import PinnedExec.
Require Import UexecExecInst.     (* the class INSTANCE: [uexecSG_xv6].  This
                                     file is E2's assembly for THE xv6
                                     application, so its [uexecSG] is the
                                     kernel's own -- which is also what
                                     [App.xv6_app_adequacy] instantiates
                                     [InitBoot.init_boot_bundle]'s at, and
                                     what [UexecExecMint]'s supply laws are
                                     stated over. *)
Require Import UkRun.             (* [udepw_law] -- the named deposits *)
Require Import UkInit.            (* [init_deps] / [init_cons_sup] *)
Require Import UexecExecMint.     (* [udepw_law_of_sup] / [udep_free] *)
Require Import UInitKernel.       (* [init_slot_of_kexec] / the dance *)
Require Import UInitCons.         (* [init_cons_fd] / [init_cons_cred] *)
Require Import UInitConsK.        (* the two arms' discharges at echo's era *)
Require Import UInitSh.           (* [init_cons_sup_of_sh_slot] *)
Require Import AppEcho.           (* [echo_boot] / [echo_taint] *)
Require Import UserConsole.       (* [ucons_reader_eq] *)
Require Import UserFd.            (* [NSTD] *)
Require Import KexecDefs.         (* [kxc_sp_final] *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import InitBoot.          (* [init_boot_bundle] and its path *)
Require Import DirentEnc.
Require Import ElfUser.           (* [init_elf] *)
Require Import ElfLoadable.       (* [init_elf_loadable] *)
Require Import FsInitPin.         (* [INIT_INO] / [init_path] / [init_bytes] *)
Require Import FsInitPinBoot.     (* [era0_pins] *)
Require FsImg.                    (* [FsImg.ROOTINO] *)
Require InodeInv.                 (* [InodeInv.ROOTINO] -- the theorem's cwd *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PATH, AS THE WALK READS IT                                    *)
(*                                                                        *)
(*  [InitBoot.init_boot_path] is the six bytes of "/init" the kernel      *)
(*  calls kexec with; [FsInitPin.init_path] is the one name the pin is    *)
(*  stated at.  The first is ABSOLUTE, so the walk ignores the cwd -- and *)
(*  /init's cwd IS the root anyway, which is what makes the [um_start_of] *)
(*  case split below a [reflexivity] on both arms.                        *)
(* ===================================================================== *)
Lemma init_boot_path_elems : path_elems init_boot_path = init_path.
Proof. vm_compute. reflexivity. Qed.

(* the theorem's own working directory, as the pin's number: [Hinit_boot]
   is stated at [bv_unsigned InodeInv.ROOTINO] and every file-system pin
   at [FsImg.ROOTINO], and they are the same 1. *)
Lemma init_boot_cw : bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
Proof. vm_compute. reflexivity. Qed.

(* THE TIE TO THE ELF LAYER, [FsShPin.sh_bytes_elf]'s twin, and it is not
   optional: [ElfUser.init_elf] is [pstring_hex_bytes] APPLIED to the raw
   hex string, so leaving [FsInitPin.init_bytes = init_elf] to unification
   sends the conversion into that computation and the kernel's stack goes
   at [Qed].  Named, the delta happens once, here. *)
Lemma init_bytes_elf : init_bytes = ElfUser.init_elf.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES                                                  *)
(* ===================================================================== *)
Lemma init_boot_pin_resolves :
  pin_resolves era0_pins FsImg.ROOTINO init_boot_path
    [FsImg.ROOTINO; INIT_INO] INIT_INO ElfUser.init_elf 1%nat.
Proof.
  split_and!.
  - (* "/init" is ABSOLUTE, so the walk starts at the root; /init's cwd is
       the root too, so both arms of [um_start_of] agree *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (init_boot_path !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - rewrite init_boot_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite init_boot_path_elems. split.
    + exact Hrun.
    + rewrite Hnode init_bytes_elf. reflexivity.
Qed.

Section UInitBoot.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  (* =================================================================== *)
  (*  3.  THE ASSEMBLY                                                    *)
  (*                                                                      *)
  (*  [InitBoot.init_boot_bundle]'s four existential families ARE          *)
  (*  [PinnedExec]'s: [P := PinnedObs.pobs_P T [ROOTINO; INIT_INO]] (the   *)
  (*  cursor that says which inums THIS walk stands on), [Pmiss :=         *)
  (*  pobs_Pmiss T] (a walk that misses is the taint -- a pinned file is   *)
  (*  there), [Fo := pobs_Fo era0_pins T] (the terminal observation, which *)
  (*  hands the lent row back and yields the pin at the observed view) and *)
  (*  [R := Pay] (the refund: exec can fail, and what the construction     *)
  (*  spent has to come back).                                            *)
  (*                                                                      *)
  (*  THE PAYLOAD IS THE TRIVIAL ONE, and that is not a simplification:    *)
  (*  <init> has no parent, so its exit owes nobody anything -- userinit's *)
  (*  own choice, which [InitBoot.init_boot_bundle] writes into its        *)
  (*  statement as [fun _ => True] and which [UInitKernel.init_uexec_slot] *)
  (*  reads back.  So the [Q (-1)] both slot wands carry is [True] and the *)
  (*  constructor below drops it.                                         *)
  (*                                                                      *)
  (*  THE READER TOKEN IS THE BUNDLE'S OWN ARGUMENT (app-echo.md,          *)
  (*  "SH-LINE RULING", R3): it is the KERNEL's to hand, born with the     *)
  (*  ring at boot, and it reaches this wand from forkret's boot arm.  So  *)
  (*  what the application supplies is a WAND from it into the linear      *)
  (*  [Pay] -- which is where /init's console credential travels beside    *)
  (*  it.                                                                 *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  3a.  THE SEAM (lane LAZY-FLAG-2)                                    *)
  (*                                                                      *)
  (*  /init's entry is stated at [uvis_cwd W' = FsImg.ROOTINO] -- its exec *)
  (*  of the RELATIVE name "sh" is only about a file because its cwd is    *)
  (*  the root -- and [SpecKexec.kexec_image_ok] does not carry the        *)
  (*  working directory: exec does not chdir, so the key's [uvis_cwd] is   *)
  (*  the block's, and only the kernel can see it                          *)
  (*  ([SpecKexec.v]'s [exec_key_cwd]).  Lane LAZY-FLAG-2 puts the row on  *)
  (*  both wands of [SpecKexec.exec_slot_pre]; until it lands, THIS IS THE *)
  (*  ONE UNPROVED STEP OF E2 and it is isolated here, at the bottom of    *)
  (*  the tree, so nothing above it is affected.  When the row lands,      *)
  (*  [PinnedExec.exec_slot_pre_at] and this bridge are deleted and the    *)
  (*  two [pinned_exec_bundle_boot] call sites are restated at             *)
  (*  [SpecKexec.exec_au_pre] -- no proof moves.                           *)
  (* =================================================================== *)
  Definition boot_cw_row (cw : Z) (W' : uvis) : Prop := uvis_cwd W' = cw.

  (* The bridge [exec_au_pre_at (boot_cw_row cw) … -∗ exec_au_pre …] is
     what the kernel row makes free; it is NOT stated here, because a
     statement nobody can prove is a premise in disguise.  The rebase onto
     the main tree that carries the row is where the two
     [pinned_exec_bundle_boot] call sites below are closed. *)

  (* ------------------------------------------------------------------- *)
  (*  3b.  THE ROOM: /init's frames fit under its argument block           *)
  (* ------------------------------------------------------------------- *)
  (* [UInitSh.init_sh_room]'s twin at /init's own image: [kexec_sz
     init_elf] is 0x4000 (one page of text, one of data, one guard, one
     stack) and the argument block is the six bytes of "/init" rounded to
     sixteen plus a two-word pointer vector, so [kxc_sp_final] lands at
     0x3FE0 -- 0xFE0 above the stack page's base, which is what /init's
     frames have to fit in. *)
  Lemma init_boot_sp_final :
    kxc_sp_final 0x4000 (fun _ => 5%nat) 1%nat = 0x3FE0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma init_boot_room (n0 : nat) :
    8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0))))) <= 0xFE0 ->
    kexec_sz ElfUser.init_elf - PGSIZE
      + 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= kxc_sp_final (kexec_sz ElfUser.init_elf) (fun _ => 5%nat) 1%nat.
  Proof.
    intros Hn0. rewrite init_kexec_sz init_boot_sp_final.
    unfold PGSIZE. lia.
  Qed.

  (* =================================================================== *)
  (*  3c.  /init's OWN ENTRY, AS THE BOOT BUNDLE'S CONSTRUCTOR WAND        *)
  (*                                                                      *)
  (*  [PinnedExec.pinned_exec_bundle_boot]'s first [□] argument: at every  *)
  (*  key the kernel's image fact admits, and at the extra row the kernel  *)
  (*  relays, /init's verified entry answers.  The two LINEAR things --    *)
  (*  the console dance (with its credential) and the console reader token *)
  (*  -- ride the bundle's [Pay], which is the one linear slot a pinned    *)
  (*  exec has and which exec's failure arm gives back.                    *)
  (* =================================================================== *)
  (* [3c] /init's entry as the bundle's constructor wand and [3d] the
     console dance out of [AppEcho.echo_boot] are written against the
     REBASED tree (main carries the cwd/lazy rows on
     [SpecKexec.exec_slot_pre], which is what closes the boot bundle);
     their drafts live in the lane's scratch and are re-elaborated with
     the [uprogSG]/[uexecSG] instances named explicitly -- leaving them
     implicit here makes the statement's elaboration diverge. *)

  (* =================================================================== *)
  (*  4.  /init's THREE DEPOSITS, AND WHO OWES WHICH                      *)
  (*                                                                      *)
  (*  [UkInit.init_deps T] is [udepw_law 16] beside [□ (T -∗ udepw_law    *)
  (*  15)] and [□ (T -∗ udepw_law 17)], and the split is the lane         *)
  (*  boundary: open(15) and mknod(17) are owed only on the TAINT arms    *)
  (*  (with its credential in hand /init walks both through the PINNED    *)
  (*  leaves, which [UInitConsK] discharges at the era), so the era pays  *)
  (*  them out of the supply the taint gives                              *)
  (*  ([AppEcho.echo_sup_of_taint] composed with                          *)
  (*  [UexecExecMint.udepw_law_of_sup]).  write(16) is owed               *)
  (*  UNCONDITIONALLY -- every line /init prints is one ecall of it -- and *)
  (*  it is THE ONE PREMISE E2 LEAVES OPEN, for E5's output lane.         *)
  (* =================================================================== *)
  Lemma init_deps_of_sup `{PSx : uprogSG Σ} (T : iProp Σ) :
    udepw_law (PS := PSx) 16 -∗
    □ (T -∗ app_sup) -∗
    UkInit.init_deps (PS := PSx) T.
  Proof.
    iIntros "#Hw16 #Hsup". rewrite /UkInit.init_deps.
    iSplitR; [ iExact "Hw16" | iSplit ].
    - iIntros "!> HT". iDestruct ("Hsup" with "HT") as "#Hs".
      iApply (udepw_law_of_sup (PSx := PSx) 15 (or_introl eq_refl) with "Hs").
    - iIntros "!> HT". iDestruct ("Hsup" with "HT") as "#Hs".
      iApply (udepw_law_of_sup (PSx := PSx) 17 (or_intror eq_refl) with "Hs").
  Qed.

End UInitBoot.
