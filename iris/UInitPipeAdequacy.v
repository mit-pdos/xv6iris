(* ===================================================================== *)
(*  UInitPipeAdequacy.v -- [App.al_programs] AT [AppPipe.app_pipe], AND   *)
(*  THE PIPELINE APPLICATION'S CLOSED THEOREM (lane PIPE-CC).             *)
(*                                                                       *)
(*  A SEPARATE FILE from the assembly, for a measured reason:             *)
(*  [UInitPipe.v] is a proofmode-heavy u-tier assembly, and pulling       *)
(*  [RiscvAdequacy] / [SystemAdequacy] / [FsCfgBoot] -- which             *)
(*  [UPipeBootAdequacy.pipe_prog_law] needs to even ELABORATE (its class  *)
(*  binders are [riscvGpreS] and the five [*GpreS]) -- into that one      *)
(*  blows the elaboration up.  So this file carries the adequacy cone     *)
(*  and takes exactly ONE thing from the assembly:                        *)
(*  [UInitPipe.pipes_Hinit_boot] (cut C8: the round's child law is        *)
(*  proved, so /init's bundle has no premise left).                       *)
(*                                                                       *)
(*  WHY [UPipeBootAdequacy.v] IS NOT EDITED INSTEAD.  It DEFINES          *)
(*  [pipe_prog_law], which this file discharges; making it take the child *)
(*  law instead would need it to [Require] its own discharger.  The       *)
(*  restated corollary therefore lives here, and                          *)
(*  [iris/PipeAssumptions.v] audits THIS one -- a cone strictly larger    *)
(*  than the old target's, since it now walks the whole program tier.     *)
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
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang ObsTrace RiscvPtsto.
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
Require Import InitBoot.
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.
Require Import InodeInv.
Require Import LineModel.           (* [lm_disc] / [lm_good_out]: the conclusion *)
Require Import PipesDisc.           (* [pipes_lmE]: the model the claim is born at *)
Require Import EchoOut.
Require Import PipeOut.
Require Import AppPipe.
Require Import PipeProto.           (* [pipeProtoG]: the protocol's ghosts *)
Require Import UPipeBootAdequacy.   (* [pipe_prog_law] / [pipeSigma] *)
Require Import UInitPipe.           (* [pipes_Hinit_boot] *)
Require Import UkPipesIface.        (* [pnsRegG] / [pipesNG]: the N-stage round's classes *)

Local Open Scope Z_scope.

Section PipeProgLaw.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{HU : !ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ}.
  (* the round's ghosts: the pipe protocol, the per-process registry and
     the N-writer family's modes *)
  Context `{HpP : !PipeProto.pipeProtoG Σ, HpR : !pnsRegG Σ, HpN : !pipesNG Σ}.

  Theorem pipe_prog_law_holds : pipe_prog_law (Σ := Σ).
  (* POINTWISE, and through the record's [cbn], for a measured reason: the
     record's fields ARE [AppPipe]'s definitions, but unification does not
     delta-unfold a record literal for them. *)
  Proof using HU HpP HpR HpN.
    intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface Hgen.
    cbn [app_pipe app_names app_pred app_ifc] in Heq, Hiface.
    iIntros "#Hinv Hb Hturn".
    iApply (pipes_Hinit_boot HR GEN c r Heq Hiface
              with "Hinv [Hb] [Hturn]").
    - cbn [app_pipe app_boot]. iExact "Hb".
    - cbn [app_pipe app_turn pipe_turn]. iExact "Hturn".
  Qed.

End PipeProgLaw.

(* ===================================================================== *)
(*  THE THEOREM -- [UPipeBootAdequacy.pipe_adequacy_pipeSigma] with its    *)
(*  [Hprog] discharged ([pipe_prog_law_holds]): no premise of its own, the *)
(*  functor list the concrete [pipeSigma] (so every ghost class is         *)
(*  realised by [subG] and the statement is not vacuous), the disk the     *)
(*  literal mkfs image, and a conclusion that mentions no Iris --          *)
(*  [LineModel.lm_disc] / [lm_good_out] at [PipesDisc.pipes_lmE] are the   *)
(*  whole specification: IF the console input kept the pipeline            *)
(*  discipline (typed lines [echo w1 .. wn] and                            *)
(*  [echo w1 .. wn | cat | .. | cat], any number of cats), THEN every      *)
(*  cycle's console output is a prefix of the transcript its input calls   *)
(*  for.                                                                   *)
(* ===================================================================== *)
Theorem pipe_adequacy_pipeΣ_final
    (gst : gstate)
    (Hgen0 : gst.(ggen) = 0%nat) (Hpow0 : gst.(gpow) = false)
    (Hdisk : v_disk (gst.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], gst)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ (lm_disc pipes_lmE κs -> Forall (lm_good_out pipes_lmE tt) (cycles_of κs)).
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio)))
                   XV6_DISK_BYTES fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (pipe_adequacy_at_img (Σ := pipeΣ)
           (pipe_prog_law_holds (Σ := pipeΣ))
           gst fsimg_sb fsimg_nib fsimg_cov Hgen0 Hpow0 Himg Hdk
           eq_refl eq_refl n κs t2 g2 Hn).
Qed.
