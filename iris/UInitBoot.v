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
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedExec.v]'s note: a field instance is inert wherever its
   module is not imported). *)
Require Import TsoCtx.            (* [CurCtx] -- see the note above *)
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
Require Import UexecWp.           (* [uexec_wp] *)
Require Import LinkUserinit.      (* [UG.uexec_wp_gen]: the generic user WP,
                                     the module route SystemAdequacy uses --
                                     the application tier does not Require a
                                     Proof*.v *)
Require Import UkSh.              (* [sh_deps] / [ush_tag_law] / the two
                                     console leaves sh's entry is told *)
Require Import UShConsK.          (* sh's two console leaf discharges at
                                     echo's era (lane SH-OPEN) *)
Require Import FsConsPin.         (* [cons_absent] / [cons_present_at] *)
Require Import App.               (* [xv6_app_adequacy] and the record *)
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

  (* ------------------------------------------------------------------- *)
  (*  3c.  /INIT'S THREE DEPOSITS, BOXED ONCE                              *)
  (*                                                                       *)
  (*  [UkInit.init_deps T] is [udepw_law 16] beside two [T]-guarded laws,   *)
  (*  and 15 (open) and 17 (mknod) are FREE off the era's supply            *)
  (*  ([UexecExecMint.udepw_law_of_sup]): only the banner write is owed     *)
  (*  (E5's [udepw_law 16], the caller's hypothesis).                       *)
  (*                                                                       *)
  (*  THE CONCLUSION CARRIES ITS OWN [□], and every consumer's premise does *)
  (*  too ([UInitKernel.init_boot_con]).  Handing the bundle round unboxed  *)
  (*  and asking the proofmode to notice it is persistent is what wedges    *)
  (*  the elaboration: the [Persistent] search unfolds [UkRun.udepw]'s wand *)
  (*  chain and does not return (durable-notes; measured as a 40-minute     *)
  (*  UInitKernel.vo at a flat 1.1 GB).  Paying the box HERE, once, at the  *)
  (*  one place that builds the bundle, keeps every later intro structural. *)
  (* ------------------------------------------------------------------- *)
  (*  IT IS PURE PLUMBING, and the supply is NOT read here: this section
      binds [uexecSG] as a VARIABLE, while [UexecExecMint.udepw_law_of_sup]
      is stated at the kernel's own instance ([UexecExecInst.uexecSG_xv6]),
      so a proof mixing the two cannot unify ("cannot apply (app_sup -∗
      udepw_law 15)").  The two free laws are therefore premises, and the
      ASSEMBLY -- whose section has no [uexecSG] variable, so both sides
      resolve to the kernel's instance -- reads them off the supply. *)
  Lemma init_deps_of_laws `{PSx : uprogSG Σ} (T : iProp Σ) :
    □ UkRun.udepw_law (PS := PSx) 16 -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 15) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 17) -∗
    □ UkInit.init_deps (PS := PSx) T.
  Proof.
    iIntros "#Hwr #H15 #H17 !>". rewrite /UkInit.init_deps.
    iSplit; [ iExact "Hwr" | ]. iSplit.
    - iModIntro. iExact "H15".
    - iModIntro. iExact "H17".
  Qed.


  (* ...AND THE SEAM SH-OPEN CONSUMES.  [UShConsK] states sh's two console
     leaves against an abstract credential; these are its two discharges,
     chosen by the credential /init's own mknod left.  At the SEAL the
     credential is [AppEcho.cons_never] and sh's first open MISSES (its
     repair arm runs); at the FLAG it is [cons_made r i] and sh's first
     open is the pinned one; under the taint sh proves nothing. *)
  Lemma ush_cons_in_of_Cns (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗ init_cons_cred (echo_taint γ) r -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N (echo_taint γ))
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N
               (echo_taint γ) (cons_never r))
        ∗ cons_never r)
     ∨ echo_taint γ).
  Proof.
    intros Heq. iIntros "#Hinv #Hc".
    rewrite /init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (sh_cons_absent_echo γ r (cons_never r)
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (echo_cons_never_law γ r).
    - iLeft. iApply (sh_cons_console_echo γ r i Heq with "Hm Hinv").
    - iRight. iRight. iExact "HT".
  Qed.

  (* AT THE FREE INSTANCE, NAMED, all the way through: /init and the shell
     it execs both run at [UexecExecInst.uprogSG_free], which is what keeps
     their [UkRun.udep] clear of the application's supply.  See the note at
     [UInitSh.init_exec_sup_of_sh_slot]. *)
  Lemma init_cons_sup_of_sh_slot (γ : echo_fixed) (r : echo_names)
      (cn : cons_names) (st : fdstate)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    (exists wr : bool, st = FdOpen true wr (FdDevice ConsoleInv.CONSOLE)) ->
    udep (PS := uprogSG_free) -∗ UkSh.sh_deps (PS := uprogSG_free) -∗
    UInitSh.init_sh_slot (echo_taint γ) (UInitSh.sh_pay (echo_taint γ) Rsh n0) -∗
    UkInit.init_cons_sup (PS := uprogSG_free) cn (echo_taint γ)
      (init_cons_cred (echo_taint γ) r) st.
  Proof.
    intros Heq Hpsok_free Hn0 Hst.
    iIntros "#Hdep #Hdp #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct "Hcore" as "#Hcore'".
      (* [Persistent K] is an INSTANCE binder there, so it is not passed
         positionally; [cons_never_persistent] answers it. *)
      iApply (UInitSh.init_exec_sup_of_sh_slot (echo_taint γ) cn st
                (cons_never r) Rsh n0 Hpsok_free Hn0 Hst
                with "Hdep Hdp [] Hcore'").
      iApply (ush_cons_in_of_Cns γ r Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (init_cons_cred_of_taint (echo_taint γ) r with "HT").
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
  Proof.
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    rewrite /init_boot_bundle. iIntros "Hrd".
    iDestruct ("HPay" with "Hrd") as "HPay".
    rewrite init_boot_cw.
    iDestruct (pinned_exec_bundle_boot fsc_fs uslot era0_pins T
                 FsImg.ROOTINO init_boot_path [FsImg.ROOTINO; INIT_INO]
                 INIT_INO ElfUser.init_elf 1%nat Pay (fun _ => True)%I
                 1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0
                 init_boot_pin_resolves init_elf_loadable
                 with "Hcl Hinv [] [] HPay") as (P Pmiss Fo R) "Hb".
    - iModIntro. iIntros (W') "%Hok %Hcw %Hlz #Hp _ HP".
      iApply ("Hcon" $! W' with "[%] [%] [%] Hp HP");
        [ exact Hok | exact Hcw | exact Hlz ].
    - iModIntro. iIntros (W') "#HT #Hp _". iApply ("Hgen" $! W' with "HT Hp").
    - iExists P, Pmiss, Fo, R. iExact "Hb".
  Qed.

End UInitBoot.

(* ===================================================================== *)
(*  5.  THE THEOREM SIDE (B3): echo's [Hinit_boot].                       *)
(*                                                                       *)
(*  Stated at [App.xv6_app_adequacy]'s own binders -- the era's classes   *)
(*  are quantified there because they are born by the boot mint -- and    *)
(*  carrying, BESIDES the two equations the theorem hands over, ONLY the  *)
(*  arc's remaining obligations, one per owning lane:                     *)
(*                                                                       *)
(*    [Hwr16]     write(16)'s deposit                          -- E5      *)
(*    [Hsh_deps]  sh's three ([UkSh.sh_deps]: 5, 15, 16)                  *)
(*                          -- SH-LINE 2b (5), SH-OPEN (15), E5 (16)      *)
(*    [Hsh_state] sh's static state out of the data below the frame -- E4 *)
(*    [Hsh_rest]  sh's tail ([UkSh.ush_rest])         -- SH-LINE 2b       *)
(*                                                                       *)
(*  [UkSh.ush_tag_law] -- the third conjunct of [UInitSh.sh_pay] -- is    *)
(*  NOT among them: it is E2's, and it is immediate from the theorem's    *)
(*  own [riscv_rx_tag = app_tag] equation, because echo's tag IS the      *)
(*  discipline-or-taint disjunction.                                      *)
(* ===================================================================== *)
Section EchoInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.

  (* ===================================================================== *)
  (*  WHICH DEPOSIT INSTANCE THIS ASSEMBLY RUNS AT, and why it is written   *)
  (*  down rather than resolved.                                           *)
  (*                                                                       *)
  (*  /init runs at [UexecExecInst.uprogSG_free] and it MUST: its           *)
  (*  [UkRun.udep] is a premise of [UInitKernel.init_slot_of_kexec], and at *)
  (*  the ambient [uprogSG_gen] that deposit is [box Dsup] with [Dsup :=    *)
  (*  xv6_ssupply := AppInv.app_sup] -- the application's supply, which for *)
  (*  the echo era is interderivable with the taint                        *)
  (*  ([AppEcho.echo_sup_of_taint] / [echo_taint_of_sup]).  A slot built at *)
  (*  [gen] outside the taint arm would therefore be a VACUOUS ARM, which   *)
  (*  the lane's ruling forbids.  The same holds one level up for the       *)
  (*  shell: [UInitSh.init_exec_sup_of_sh_slot] and                         *)
  (*  [UShKernel.sh_slot_of_kexec] are at the free instance too.            *)
  (*                                                                       *)
  (*  SO EVERY DEPOSIT POSITION NAMES IT: [UexecExecMint.udep_free],        *)
  (*  [UkInit.init_deps (PS := uprogSG_free)], [UkSh.sh_deps (PS :=         *)
  (*  uprogSG_free)], [UkInit.init_cons_sup (PS := uprogSG_free)],          *)
  (*  [UInitKernel.init_boot_con (PS := uprogSG_free)].  Per-lemma, never a *)
  (*  section binder and never a [Local Existing Instance]: [uprogSG_gen]   *)
  (*  stays the one instance resolution finds, because the GENERIC slot --  *)
  (*  the safety net the taint arm falls back on -- is that instance by     *)
  (*  design.                                                               *)
  (*                                                                       *)
  (*  At [uprogSG_free], [psok] IS [UexecSG.free_num], which is why the     *)
  (*  [(fun k H => H)] below is the identity rather than a proof.           *)
  (* ===================================================================== *)
  Lemma echo_Hinit_boot
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (Rsh : gname -> gname -> gname -> iProp Σ)
      (γ : echo_fixed) (r : echo_names) :
    (* ---- the arc's remaining obligations, by lane ---- *)
    (⊢ UkRun.udepw_law (PS := uprogSG_free) 16) ->
    (⊢ UkSh.sh_deps (PS := uprogSG_free)) ->
    (⊢ UInitSh.sh_pay_state Rsh 0%nat) ->
    (⊢ UInitSh.sh_pay_rest Rsh) ->
    (* ---- and the two equations [Hinit_boot] hands over ---- *)
    @file_app Σ HF = MkAppcfg echo_names (echo_pred γ) r ->
    riscv_rx_tag = echo_tag γ ->
    ⊢ app_inv fsc_fs -∗ echo_boot γ r -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof.
    intros Hwr16 Hsh_deps Hsh_state Hsh_rest Heq Htag.
    iIntros "#Hinv Hb". iModIntro.
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iAssert (□ (echo_taint γ -∗ app_sup))%I as "#Hsup".
    { rewrite /app_sup. rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!> #Ht". iApply (echo_sup_of_taint γ r with "Ht"). }
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iAssert (□ (∀ (R : iProp Σ) (W : uvis),
                  echo_taint γ -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
                  R -∗ uslot W))%I as "#Hmint".
    { iIntros "!>" (R W) "#Ht Hp HR".
      iDestruct ("Hsup" with "Ht") as "#Hs".
      iApply (uslot_mint_all with "Hs Hwp Hp HR"). }
    (* ---- the pins law, and /init's own row out of it ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint γ)))%I
      as "#Hfs".
    { rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!>" (v) "Hp". iApply (echo_fs_pure_acc γ r v with "Hp"). }
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v ∗ (⌜era0_pins v⌝ ∨ echo_taint γ)))%I
      as "#Hcl".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    (* ---- /init's three deposits ---- *)
    iAssert (□ UkInit.init_deps (PS := uprogSG_free) (echo_taint γ))%I
      as "#Hdp".
    { iApply (init_deps_of_laws (PSx := uprogSG_free) (echo_taint γ)
                with "[] [] []").
      - iModIntro. iApply Hwr16.
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 15
                  (or_introl eq_refl)).
        iApply ("Hsup" with "HT").
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 17
                  (or_intror eq_refl)).
        iApply ("Hsup" with "HT"). }
    (* ---- the tag's reading: E2's own, off the theorem's equation ---- *)
    iAssert (UkSh.ush_tag_law (echo_taint γ)) as "#Htg".
    { rewrite /UkSh.ush_tag_law. iIntros "!>" (h) "Hr".
      rewrite Htag /echo_tag. iExact "Hr". }
    (* ---- the shell's slot, and the exec supply as a wand from the
           console credential ---- *)
    iAssert (UInitSh.init_sh_slot (echo_taint γ)
               (UInitSh.sh_pay (echo_taint γ) Rsh 0%nat))%I as "#Hsh".
    { rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | ].
      iSplitR; [ iExact "Hmint" | ].
      iApply (UInitSh.sh_pay_of_parts (echo_taint γ) Rsh 0%nat
                with "[] [] Htg"); [ iApply Hsh_state | iApply Hsh_rest ]. }
    iAssert (UkInit.init_cons_sup (PS := uprogSG_free) fsc_cons (echo_taint γ)
               (init_cons_cred (echo_taint γ) r) init_cons_fd)%I as "#Hxs".
    { iApply (init_cons_sup_of_sh_slot γ r fsc_cons init_cons_fd
                Rsh 0%nat Heq (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(exists true; reflexivity)
                with "[] [] Hsh").
      - iApply (udep_free).
      - iApply Hsh_deps. }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided
           ([AppEcho.echo_boot]).  Built through [UInitKernel]'s two intro
           lemmas, which is the one place this file names its vocabulary:
           the [ctokG] instance is [Xv6G.xv6_ctok] here and a section
           VARIABLE there, and that unification happens at THESE
           applications rather than inside [UkInit]'s wand tower. ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (echo_taint γ) (init_cons_cred (echo_taint γ) r)
               init_cons_fd)%I with "[Hb]" as "Hdn".
    { rewrite /echo_boot. iDestruct "Hb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (echo_taint γ) (init_cons_cred (echo_taint γ) r)
                  (cons_key r) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_echo γ r Heq with "Hinv").
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (echo_taint γ) (init_cons_cred (echo_taint γ) r)
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_echo γ r i Heq with "Hm Hinv").
        + iApply (init_cons_cred_made_echo γ r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (echo_taint γ) (init_cons_cred (echo_taint γ) r)
                    fsc_cons init_cons_fd -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free) (echo_taint γ)
                (init_cons_cred (echo_taint γ) r) init_cons_fd fsc_cons
                1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
                init_cons_fd_ne (init_boot_room 0%nat
                                   ltac:(vm_compute; discriminate))
                fdt0_length eq_refl (fun k H => H)
                with "[] [] Hxs").
      - iModIntro. iExact "Hdp".
      - iApply (udep_free). }
    iApply (init_boot_bundle_of_pinned (echo_taint γ)
              (UInitKernel.init_boot_pay (PS := uprogSG_free) (echo_taint γ)
                 (init_cons_cred (echo_taint γ) r) fsc_cons init_cons_fd)
              with "Hcl Hinv Hcon [] [Hdn]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp"). done.
    - iIntros "Hrd". rewrite /UInitKernel.init_boot_pay.
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      rewrite ucons_reader_eq. iExact "Hrd".
  Qed.

End EchoInitBoot.

