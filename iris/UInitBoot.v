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
(*     of [EchoFsPure.echo_fs_pure], so [echo_fs_pure_acc] gives it);        *)
(*   the CONSTRUCTOR WAND -- [UInitKernel.init_slot_of_kexec] at /init's  *)
(*     own entry premises;                                               *)
(*   the TAINT ARM -- [UexecExecMint.uslot_mint_all] on                   *)
(*     [AppEcho.echo_sup_of_taint];                                       *)
(*   [Pay] -- the LINEAR half: the console reader token the bundle's own  *)
(*     wand hands in ([InitBoot.init_boot_bundle] is a wand from          *)
(*     [ConsoleInv.cons_reader]) beside the era's console credential      *)
(*     (the KEY or the FLAG, [AppEcho.echo_boot]'s two arms).             *)
(*                                                                       *)
(* SINCE UNION CUT C9h the echo era's own discharge ([echo_cc],          *)
(* [echo_Hinit_boot]) is gone with the echo application; what is left is *)
(* the record-generic assembly ([init_boot_bundle_of_pinned],            *)
(* [init_boot_room]) that the union's and the tree's /init apply.         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.   (* [mono_nat_lb_own_get]: the era's turn at 0 is the reader's receipt residue (step 4) *)
(* [mono_list] AND [ghost_var] ARE REQUIRED HERE FOR A REASON, and so is
   [TsoCtx] below: a [Context] binder naming a class whose defining module
   is not in scope does not fail -- the backtick generalisation invents a
   FRESH VARIABLE for the name ([mono_listR : ofe -> cmra], [ghost_varG :
   gFunctors -> Set -> Type], [CurCtx : Type]) and the binder is then about
   something no real instance can ever match.  The symptom is not a missing
   instance where you wrote it; it is an elaboration that never comes back
   somewhere else (measured here at 47 GB RSS in 94 seconds, in the
   STATEMENT of [ush_cons_in_of_Cns], because [AppEcho.cons_never]'s [own]
   is at the real [mono_listR] and the section's was not).  See
   [UShConsK.v]'s header note. *)
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.            (* [cons_licence]: the generic slot's output licence *)
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedExec.v]'s note: a field instance is inert wherever its
   module is not imported). *)
Require Import CtxIdDefs.            (* [CurCtx] -- see the note above *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.          (* [uslot] -- REQUIRED DIRECTLY (the seal) *)
Require Import UexecSG.
Require Import PathElems.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.             (* [fsc_fs] / [fsc_cons] *)
Require Import ConsoleInv.        (* [cons_reader] *)
Require Import SpecKexec.         (* [exec_au_pre] / [kexec_image_ok] *)
Require Import FsAbsDefs.
Require Import FsAbsEra.
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
Require Import UkWriteClosed.     (* [kinit_w1_of_closed_l0]: init's write on a closed fd 1 (lane EXEC-SEAM, (D)) *)
Require Import UInitKernel.       (* [init_slot_of_kexec] / the dance *)
Require Import LineWords.         (* [wl_nl] / [rest_of] *)
Require Import EchoLinks.         (* [echo_links] -- E5's four links as one
                                     persistent law *)
Require Import UInitDiag.         (* [kinit_pro] and the three laws /init's
                                     walk is handed (lane M6b): the banner's
                                     leaving the round-open credential, and
                                     the two diagnostics paid from it *)
Require Import UInitBanner.       (* [kinit_banner0_holds] -- the era's
                                     credential as init's banner payment *)
Require Import UInitCons.         (* [init_cons_fd] / [init_cons_cred] *)
Require Import UInitConsK.        (* the two arms' discharges at echo's era *)
Require Import UInitSh.           (* [init_cons_sup_of_sh_slot] *)
Require Import UShPanic.          (* [sh_prompt_law_holds_line]: the prompt's law at the tight family (step 4) *)
Require Import EchoLinksPro.      (* [ewc_pro]: the round-open shape /init lends *)
Require Import EchoLinksLine.     (* [ewc_lcred]: the loop's tight credential family (step 4) *)
Require Import EchoLinksBan.      (* [ewc_ban_line]: the banner-owed credential is a boundary credential *)
Require Import UShLine.           (* sh's console read-leaf file.  Its
                                     discharge [ush_read_recv_leaf_holds]
                                     is GONE (lane ECHO-OUT part 5): the
                                     leaf is a premise here now.  The
                                     [Require] stays because the cone it
                                     brings is what this file's own
                                     statements elaborate against. *)
Require Import AppEcho.           (* [echo_boot] / [echo_taint] *)
Require Import EchoOut.            (* [echoOutG]: the class [AppEcho]'s claims
                                      and its ledger are stated at (lane
                                      ECHO-OUT part 5).  It CARRIES
                                      [mono_natG], so it is the taint's one
                                      instance here too. *)
Require Import UserConsole.       (* [ucons_reader_eq] *)
Require Import UserFd.            (* [NSTD] *)
Require Import LinkUserinit.      (* [UG.uexec_wp_gen]: the generic user WP,
                                     the module route SystemAdequacy uses --
                                     the application tier does not Require a
                                     Proof*.v *)
Require Import UkSh.              (* [sh_deps] / [ush_tag_law] / the two
                                     console leaves sh's entry is told *)
Require Import UShConsK.          (* sh's two console leaf discharges at
                                     echo's era (lane SH-OPEN) *)
(* THE ADEQUACY LAYER IS DELIBERATELY NOT REQUIRED HERE.  This file is a
   proofmode-heavy u-tier assembly; pulling [RiscvAdequacy] /
   [SystemAdequacy] / [FsCfgBoot] into it -- which is what the B3 theorem
   [echo_adequacy_modulo_phi] needs, since [Require Import App] is not a
   [Require Export] and brings none of them -- makes the elaboration blow
   up (measured at 54 GB RSS in 64 seconds, and 489 GB in nine minutes
   before the cap was tightened).  The B3 theorem therefore lives in its
   own file, [UInitBootAdequacy.v], which carries the adequacy cone and
   takes only [echo_Hinit_boot] from this one. *)
Require Import KexecDefs.         (* [kxc_sp_final] *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import InitBoot.          (* [init_boot_bundle] and its path *)
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
  (* the console FLAG and KEY's camera ([AppEcho.cons_made] / [cons_key] /
     [cons_never], which the dance's assembly names).  NOT [mono_natG]:
     the taint's camera is [riscvFixedGS]'s own and a second binder here
     would be a second instance that prints alike, which is what makes the
     era's record equation unusable ([UInitConsK.v]'s note).  It is not
     optional -- a lemma naming a resource over a class its section does
     not bind makes Coq SYNTHESISE the instance, and through [solve_inG]
     the elaboration explodes (durable-notes, "A lemma's binder list must
     match the definition it is about"). *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class (lane ECHO-OUT part 5): [AppEcho.echo_taint] and
     everything built over it is stated at [EchoOut.echoOutG] now, not at a
     bare [mono_natG] -- and that class CARRIES [mono_natG], which is why
     the note above still holds: there is exactly one binder for it here. *)
  Context `{!echoOutG Σ}.
  (* ...and the rest of [UInitSh.v]'s list, because this file now carries
     its era-specific seam.  COPIED VERBATIM from that file: a shorter
     list is what makes Coq synthesise an instance and blow the
     elaboration up (durable-notes; measured here at 8.6 GB RSS). *)
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  (* NO [Context {SG}] / [Context {PS}] -- [UInitSh.v]'s rule, and this
     file learned it the expensive way.  [UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] GLOBALLY, and a section variable of
     the same class standing beside a global instance is two [sbundle]s
     that print identically: the statements below name [UkSh]'s leaves,
     which are elaborated at the ambient pair, and asking Coq to reconcile
     them with a local one blows the elaboration up in the STATEMENT --
     measured here at 47 GB RSS in 94 seconds, before the proof runs.
     Where a lemma has to speak about a DIFFERENT [uprogSG] (the free
     instance /init runs at, [UexecExecInst.uprogSG_free]) it binds one
     itself, as [init_deps_of_laws] does, and the caller passes it. *)

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
  (*  3a.  THE CWD ROW IS THE KERNEL'S NOW (lane LAZY-FLAG-2, landed)      *)
  (*                                                                      *)
  (*  /init's entry is stated at [uvis_cwd W' = FsImg.ROOTINO] -- its exec *)
  (*  of the RELATIVE name "sh" is only about a file because its cwd is    *)
  (*  the root -- and [SpecKexec.kexec_image_ok] does not carry the        *)
  (*  working directory: exec does not chdir, so the key's [uvis_cwd] is   *)
  (*  the block's, and only the kernel can see it                         *)
  (*  ([SpecKexec.v]'s [exec_key_cwd]).  Lane LAZY-FLAG-2 put that row,    *)
  (*  and the lazy bit beside it, on BOTH wands of                        *)
  (*  [SpecKexec.exec_slot_pre]; [PinnedExec.pinned_exec_bundle_boot]      *)
  (*  relays the two, so the constructor below receives them and there is  *)
  (*  no bridge left to state.                                            *)
  (* =================================================================== *)

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
  Proof using . vm_compute. reflexivity. Qed.

  Lemma init_boot_room (n0 : nat) :
    8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0))))) <= 0xFE0 ->
    kexec_sz ElfUser.init_elf - PGSIZE
      + 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= kxc_sp_final (kexec_sz ElfUser.init_elf) (fun _ => 5%nat) 1%nat.
  Proof using .
    intros Hn0. rewrite init_kexec_sz init_boot_sp_final.
    unfold PGSIZE. lia.
  Qed.

  (* =================================================================== *)
  (*  3e.  THE BOOT BUNDLE                                                *)
  (* =================================================================== *)
  (*  [InitBoot.init_boot_bundle]'s four existential families ARE          *)
  (*  [PinnedExec]'s: [P := PinnedObs.pobs_P T [ROOTINO; INIT_INO]] (the   *)
  (*  cursor that says which inums THIS walk stands on), [Pmiss :=         *)
  (*  pobs_Pmiss T] (a walk that misses is the taint -- a pinned file is   *)
  (*  there), [Fo := pobs_Fo era0_pins T] (the terminal observation) and   *)
  (*  [R := Pay] (the refund: exec can fail and what the construction      *)
  (*  spent comes back).                                                   *)
  (*                                                                      *)
  (*  THE PAYLOAD IS THE TRIVIAL ONE, and that is not a simplification:    *)
  (*  <init> has no parent, so its exit owes nobody anything -- userinit's *)
  (*  own choice, which [InitBoot.init_boot_bundle] writes into its        *)
  (*  statement as [fun _ => True].                                        *)
  (*                                                                      *)
  (*  THE READER TOKEN IS THE BUNDLE'S OWN ARGUMENT (app-echo.md,          *)
  (*  "SH-LINE RULING", R3): it is the KERNEL's to hand, born with the     *)
  (*  ring at boot, and it reaches this wand from forkret's boot arm.      *)
  (* =================================================================== *)
  Lemma init_boot_bundle_of_pinned (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Pay : iProp Σ) :
    (* the pin, as a law over the application's claim *)
    □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                      AppCfg.app_pred AppCfg.app_run v ∗ (⌜era0_pins v⌝ ∨ T)) -∗
    app_inv fsc_fs -∗
    (* /init's OWN entry, at every key the kernel's image fact admits and
       at the two rows it relays beside it.  ABSTRACT HERE: the wand is
       [UInitKernel.init_boot_con]'s, stated where its vocabulary lives,
       and the caller applies that lemma with the [ctokG] instance given
       explicitly -- see the note at [init_boot_con]. *)
    □ (∀ W' : uvis,
         ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
            (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
         ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
         ⌜uvis_lazy W' = false⌝ -∗
         my_pay (uvis_gen W') (fun _ => True)%I -∗ Pay -∗ uslot W') -∗
    (* the taint's generic slot at the (trivial) payload *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W') -∗
    (* the linear half, as a wand from the token the kernel hands in *)
    (cons_reader fsc_cons 0%nat -∗ Pay) -∗
    init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof using .
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    rewrite /init_boot_bundle.
    iIntros "Hrd".
    iDestruct ("HPay" with "Hrd") as "HPay".
    rewrite init_boot_cw.
    iDestruct (pinned_exec_bundle_boot fsc_fs uslot era0_pins T
                 FsImg.ROOTINO init_boot_path [FsImg.ROOTINO; INIT_INO]
                 INIT_INO ElfUser.init_elf 1%nat Pay (fun _ => True)%I
                 1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0
                 init_boot_pin_resolves init_elf_loadable
                 with "Hcl Hinv [] [] HPay") as (P Pmiss Fo R) "Hb".
    - iModIntro. iIntros (W') "%Hok %Hcw %Hlz #Hp HP".
      iApply ("Hcon" $! W' with "[%] [%] [%] Hp HP");
        [ exact Hok | exact Hcw | exact Hlz ].
    - (* the taint arm takes the key and nothing else (lane OFF-HAND-6,
         H3): [ExecEntry.image_entry_taint] carries no all-parked row. *)
      iModIntro. iIntros (W') "#HT #Hp". iApply ("Hgen" $! W' with "HT Hp").
    - iExists P, Pmiss, Fo, R. iExact "Hb".
  Qed.

End UInitBoot.

