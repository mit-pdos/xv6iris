(* ===================================================================== *)
(* UPipeBootAdequacy.v -- THE PIPELINE APPLICATION'S TOP-LEVEL THEOREM   *)
(* (lane SH-PIPE-ROUND, deliverable C / lane PIPE-ADEQUACY folded in).   *)
(*                                                                       *)
(* [App.xv6_app_adequacy] at [AppPipe.app_pipe]: every obligation of the *)
(* record discharged, the functor list fixed at a concrete [pipeSigma],  *)
(* the disk at the literal mkfs image, and NOTHING left as a premise but *)
(* the hardware setup AND [Hprog] -- [App.al_programs], the first        *)
(* process's exec bundle.                                                *)
(*                                                                       *)
(* MOULD: [UFileBootAdequacy.v], file for file (which is                 *)
(* [UInitBootAdequacy.v] one application over).  Everything its header   *)
(* says about [Hprog] holds here verbatim and is not repeated: it is a   *)
(* PREMISE and not an [Axiom], a theorem's premises never appear in a    *)
(* [Print Assumptions], and the binder list of the closed corollary is   *)
(* the complementary check.                                              *)
(*                                                                       *)
(* WHAT IS DIFFERENT FROM THE FILE TWIN, and it is worth recording: the  *)
(* pipeline claim carries NO per-era state, so the functor list loses    *)
(* both of the file application's own entries ([fileAppSigma] -- the     *)
(* deed and the typed-line list -- and [fileOutSigma] -- the per-era     *)
(* boot-state map).  [pipeSigma] is the ECHO application's list plus the *)
(* pipe protocol's cameras ([PipeProto.pipeProtoSigma]) and the N-stage  *)
(* round's registry and mode ghosts ([UkPipesIface]): the pipeline stage *)
(* is [EchoOut]'s ghost algebra at the line model [PipesDisc.pipes_lmE]  *)
(* and the claim is echo's with a PERSISTENT, instance-free /cat         *)
(* conjunct (lane PIPE-CLAIM).                                           *)
(*                                                                       *)
(* IS [Hprog] SATISFIABLE?  The file twin's two witnesses are this       *)
(* file's as well ([App.app_triv_init_boot] at the generic application   *)
(* and [UInitBoot.echo_Hinit_boot] at [AppEcho.app_echo], a fully        *)
(* verified /init and /sh), and this campaign has added a third half:    *)
(* [AppPipeCons]/[UInitConsPipe] land /init's WHOLE console dance at     *)
(* [AppPipeClaim.pipe_pred], which is the part of [Hprog] that is about  *)
(* the CLAIM.  What is left of it is sh's round at the pipeline line.    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
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
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.                (* [xv6_app_adequacy] and the record *)
Require Import InodeInv.           (* [ROOTINO] *)
Require Import EchoOut.            (* [echoOutG] / [echoOutSigma] *)
Require Import PipeProto.          (* [pipeProtoSigma]: the pipe protocol's cameras -- every round mints a pipe's ghosts *)
Require Import PipeOut.            (* [pipeOutG] / [pipeOutSigma] -- NOT dead:
                                      the section below generalises over
                                      [pipeOutG] and a missing import makes it
                                      an unbound variable, not an error *)
Require Import PipeProto.          (* [pipeProtoSigma]: the protocol's functors *)
Require Import AppPipe.            (* [app_pipe] and its ten discharged laws *)
Require Import ObsTrace.           (* [cycles_of] *)
Require Import LineModel.          (* [lm_disc] / [lm_good_out]: the conclusion, spelled out *)
Require Import PipesDisc.          (* [pipes_lmE]: the model the claim is born at *)
Require UkPipesIface.              (* [pnsRegSig] / [pipesNSig]: the N-stage round's registry and mode ghosts *)

Local Open Scope Z_scope.

Section PipeAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  (* the pipeline application's own class (lane PIPE-2W-2): [app_pipe]'s
     fixed part is [PipeOut.pipe_gn] and its claim is [pecl], so the
     record does not even elaborate without it. *)
  Context `{!pipeOutG Σ}.

  (* =================================================================== *)
  (*  1.  THE ONE LAW THAT IS OWED, NAMED                                 *)
  (*                                                                     *)
  (*  [App.al_programs] at [app_pipe], VERBATIM from the class -- and     *)
  (*  verbatim from [AppPipe]'s own [Context (Hprog : ...)], so that the  *)
  (*  instance below is the section hypothesis applied and not a          *)
  (*  restatement of it.                                                  *)
  (* =================================================================== *)
  Definition pipe_prog_law : Prop :=
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_pipe (Σ := Σ)))
           (r : app_names (app_pipe (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_pipe) (app_pred app_pipe c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_pipe c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_pipe c (S gen_id) r -∗
        app_turn app_pipe c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.

  Context (Hprog : pipe_prog_law).

  (* THE ELEVEN LAWS, AS THE INSTANCE (the file twin's rule, verbatim):
     [AppPipe.pipe_laws] is already the class instance with ten fields
     discharged and the eleventh as its own section hypothesis; here it is
     simply applied to [Hprog], at priority 0 so that resolution never
     reaches [AppPipe.pipe_laws] itself. *)
  #[local] Instance pipe_laws_at : App.xv6_app_laws (app_pipe (Σ := Σ)) | 0 :=
    AppPipe.pipe_laws (Σ := Σ) Hprog.

  (* =================================================================== *)
  (*  2.  THE THEOREM, over an abstract [Σ] and at the image's facts      *)
  (* =================================================================== *)
  Theorem pipe_adequacy_at_img
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
      /\ app_phi app_pipe g2 κs.
  Proof using Hprog bioslotGpreS0 echoOutG0 fdslotGpreS0 fileGpreS0 inG0
              irefslotGpreS0 pavGpreS0 riscvGpreS0 ufdG0 wchGpreS0 xv6G0.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE ([UInitBootAdequacy]'s measured
       rule), for its measured reason. *)
    refine (xv6_app_adequacy Σ g sb nib cov app_pipe
              (pipe_Happ_init g sb nib cov Himg Hdk Hsb Hcov)
              _ Hgen0 Hpow0 Himg n κs t2 g2 Hn).
    (* [Hphi]: a PURE reading of the application's trace ledger, so the
       crash slot and the power interpretation are dropped and what is left
       is [RiscvAdequacy.obs_ledger_at_phi] at [AppPipe.pipe_Hphi_R] --
       the ledger's own [PipeOut.pipe_led_phi]. *)
    intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h.
    iIntros "_ Hauth _ _ Hled".
    iApply (obs_ledger_at_phi (app_R app_pipe c) (al_Rt c)
              (app_phi app_pipe g') (fun h' => pipe_Hphi_R c g' h')
              γobs h with "Hauth Hled").
  Qed.

End PipeAdequacy.

(* ===================================================================== *)
(*  3.  THE CLOSED COROLLARY                                             *)
(*                                                                       *)
(*  The file twin's two closures at the pipeline application: the FUNCTOR *)
(*  LIST is a concrete one, so the claim that the ghost state is          *)
(*  realisable is CHECKED and the statement is not vacuous; and the IMAGE *)
(*  facts follow from the one hardware equation.                          *)
(*                                                                       *)
(*  WHAT IT DOES NOT CLOSE, and cannot: [Hdisk] and [Hprog].              *)
(*                                                                       *)
(*  THE CONCLUSION MENTIONS NO IRIS: [LineModel.lm_disc] and              *)
(*  [lm_good_out] at [PipesDisc.pipes_lmE] do not depend on [Sigma], so   *)
(*  they are spelled out here rather than left behind the record.  What   *)
(*  it says: IF the console input kept the PIPELINE discipline (the user  *)
(*  types lines [echo w1 .. wn] and [echo w1 .. wn | cat | .. | cat] with *)
(*  any number of cats, waiting for the prompt and for each byte's echo), *)
(*  THEN each cycle's console output is a prefix of the transcript its    *)
(*  input calls for.  [LineModel.v] and [PipesDisc.v] are the whole       *)
(*  specification.                                                        *)
(* ===================================================================== *)

(* the shell's line-choice list *)
Definition pipeLineΣ : gFunctors := #[ GFunctor (mono_listR (leibnizO Z)) ].

Global Instance subG_pipeLineΣ {Σ} :
  subG pipeLineΣ Σ -> inG Σ (mono_listR (leibnizO Z)).
Proof. solve_inG. Qed.

Definition pipeΣ : gFunctors :=
  #[ xv6Σ                (* the system theorem's own list                  *)
   ; bioslotΣ            (* not in [xv6Σ]: the bio escrow's slot camera    *)
   ; echoOutΣ            (* the console stage's ghosts -- echo's, verbatim *)
   ; pipeOutΣ            (* the pipeline's own: the era map and [pe_cur]     *)
   ; pipeProtoΣ          (* the pipe protocol's ghosts (lane PIPE-PROTO)     *)
   ; pipeLineΣ           (* the shell's line-choice list                   *)
   ; PipeProto.pipeProtoΣ (* the pipe PROTOCOL's cameras: cursors, the shots,
                            the side tokens -- every round mints one pipe's
                            (lane SH-PIPE-ROUND-14 found them missing)     *)
   ; UkPipesIface.pnsRegΣ (* the N-stage round's per-process registry (C6) *)
   ; UkPipesIface.pipesNΣ (* the N-writer family's mode ghosts (C5) *)
   ].

Corollary pipe_adequacy_pipeΣ
    (Hprog : pipe_prog_law (Σ := pipeΣ))
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ (lm_disc pipes_lmE κs -> Forall (lm_good_out pipes_lmE tt) (cycles_of κs)).
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                   fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (pipe_adequacy_at_img (Σ := pipeΣ) Hprog g fsimg_sb fsimg_nib
           fsimg_cov Hgen0 Hpow0 Himg Hdk eq_refl eq_refl n κs t2 g2 Hn).
Qed.
