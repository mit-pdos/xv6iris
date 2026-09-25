(* ===================================================================== *)
(* UUnionBootAdequacy.v -- THE UNION APPLICATION'S TOP-LEVEL THEOREM     *)
(* (cut C9g; design: claude-notes/design/union.md section 4).           *)
(*                                                                       *)
(* [App.xv6_app_adequacy] at [AppUnionRec.app_union]: every obligation   *)
(* of the record discharged, the functor list fixed at a concrete        *)
(* [unionΣ], the disk at the literal mkfs image, and nothing left as a   *)
(* premise but the hardware setup and [Hprog] -- [App.al_programs] at    *)
(* this record, NAMED [union_prog_law] so that [UInitUnion.v] discharges *)
(* it by name ([UInitUnion.union_Hinit_boot]) and the closed corollary   *)
(* [UInitUnion.union_adequacy_closed] is one line.  [UFileBootAdequacy]  *)
(* is the mould; see its header for why the premise is a named law and   *)
(* not an axiom.                                                         *)
(*                                                                       *)
(* THE FUNCTOR LIST is the file application's ([UFileBootAdequacy.fileΣ]) *)
(* with the pipeline round's cameras beside it: the byte ledger's era    *)
(* map ([PipeOut.pipeOutΣ]), the pipe protocol ([PipeProto.pipeProtoΣ]), *)
(* the N-stage round's per-process registry ([UkPipesIface.pnsRegΣ]), the *)
(* N-writer family's modes ([UkPipesIface.pipesNΣ]) and the producer's   *)
(* registry ([UkCatFIface.cifRegΣ]).  The file handler's registry        *)
(* ([UkFileIface.fifRegΣ]) STAYS: the union round's file children still *)
(* run the file entries, which allocate it.                              *)
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
Require Import FileDisc.
Require Import AppFile.            (* [fileAppG] / [fileAppSig] *)
Require Import EchoOut.            (* [echoOutG] / [echoOutSig] *)
Require Import FileOut.            (* [fileOutG] / [fileOutSig] *)
Require Import PipeOut.            (* [pipeOutG] / [pipeOutΣ] *)
Require Import UnionDisc.
Require Import UnionOutPure.       (* [union_phi] -- the conclusion, spelled out *)
Require Import UnionOut.
Require Import AppUnionRec.        (* [app_union] and its ten discharged laws *)
Require UkFileIface.               (* [fifRegΣ]: the file handler's registry *)
Require UkPipesIface.              (* [pnsRegΣ] / [pipesNΣ] *)
Require UkCatFIface.               (* [cifRegΣ] *)
Require PipeProto.                 (* [pipeProtoΣ] *)

Local Open Scope Z_scope.

Section UnionAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  (* =================================================================== *)
  (*  1.  THE ONE LAW THAT IS OWED, NAMED: [App.al_programs] at           *)
  (*      [app_union], verbatim from [AppUnionRec]'s own [Hprog]          *)
  (* =================================================================== *)
  Definition union_prog_law : Prop :=
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_union (Σ := Σ)))
           (r : app_names (app_union (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_union) (app_pred app_union c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_union c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_union c (S gen_id) r -∗
        app_turn app_union c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0.

  Context (Hprog : union_prog_law).

  (* THE ELEVEN LAWS, AS THE INSTANCE, at priority 0 so that resolution
     never reaches [AppUnionRec.union_laws] itself *)
  #[local] Instance union_laws_at : App.xv6_app_laws (app_union (Σ := Σ)) | 0 :=
    AppUnionRec.union_laws (Σ := Σ) Hprog.

  (* =================================================================== *)
  (*  2.  THE THEOREM, over an abstract [Σ] and at the image's facts      *)
  (* =================================================================== *)
  Theorem union_adequacy_at_img
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
      /\ app_phi app_union g2 κs.
  Proof using Hprog bioslotGpreS0 echoOutG0 fdslotGpreS0 fileAppG0 fileGpreS0
              fileOutG0 inG0 irefslotGpreS0 pavGpreS0 pipeOutG0 riscvGpreS0 ufdG0
              wchGpreS0 xv6G0.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE ([UInitBootAdequacy]'s measured
       rule) *)
    refine (xv6_app_adequacy Σ g sb nib cov app_union
              (union_Happ_init g sb nib cov Himg Hdk Hsb Hcov)
              _ Hgen0 Hpow0 Himg n κs t2 g2 Hn).
    (* [Hphi]: a PURE reading of the application's trace ledger *)
    intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h.
    iIntros "_ Hauth _ _ Hled".
    iApply (obs_ledger_at_phi (app_R app_union c) (al_Rt c)
              (app_phi app_union g') (fun h' => union_Hphi_R c g' h')
              γobs h with "Hauth Hled").
  Qed.

End UnionAdequacy.

(* ===================================================================== *)
(*  3.  THE CLOSED FUNCTOR LIST                                           *)
(*                                                                       *)
(*  A concrete list, so the claim that the ghost state is realisable is   *)
(*  CHECKED and the statement is not vacuous.  The conclusion mentions no *)
(*  Iris: [UnionOutPure.union_phi] reads the trace alone, and             *)
(*  [UnionDisc.v] with [LineModel.v] is the whole specification.          *)
(* ===================================================================== *)

(* the shell's line-choice list *)
Definition unionLineΣ : gFunctors := #[ GFunctor (mono_listR (leibnizO Z)) ].

Global Instance subG_unionLineΣ {Σ} :
  subG unionLineΣ Σ -> inG Σ (mono_listR (leibnizO Z)).
Proof. solve_inG. Qed.

Definition unionΣ : gFunctors :=
  #[ xv6Σ                  (* the system theorem's own list                *)
   ; bioslotΣ              (* the bio escrow's slot camera                 *)
   ; echoOutΣ              (* the console stage's ghosts                   *)
   ; unionLineΣ            (* the shell's line-choice list                 *)
   ; fileAppΣ              (* the deed and the typed-line list             *)
   ; fileOutΣ              (* the per-era boot-state map and its bound     *)
   ; UkFileIface.fifRegΣ   (* the file handler's device registry           *)
   ; pipeOutΣ              (* the byte ledger's era map                    *)
   ; PipeProto.pipeProtoΣ  (* the pipe protocol's cameras                  *)
   ; UkPipesIface.pnsRegΣ  (* the N-stage round's per-process registry     *)
   ; UkPipesIface.pipesNΣ  (* the N-writer family's mode ghosts            *)
   ; UkCatFIface.cifRegΣ   (* the producer's registry                      *)
   ].

Corollary union_adequacy_unionΣ
    (Hprog : union_prog_law (Σ := unionΣ))
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ UnionOutPure.union_phi κs.
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                   fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (union_adequacy_at_img (Σ := unionΣ) Hprog g fsimg_sb fsimg_nib
           fsimg_cov Hgen0 Hpow0 Himg Hdk eq_refl eq_refl n κs t2 g2 Hn).
Qed.
