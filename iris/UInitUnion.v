(* ===================================================================== *)
(*  UInitUnion.v -- THE UNION APPLICATION'S [al_programs] AND ITS TOP     *)
(*  THEOREM (cut C9g; design: claude-notes/design/union.md section 4).    *)
(*                                                                        *)
(*  [UUnionBootAdequacy.union_prog_law] is proved by NAME -- its body is  *)
(*  [UInitUnionBoot.union_Hinit_boot_at] at the record's own equations -- *)
(*  and the closed corollary [union_adequacy_closed] is                   *)
(*  [UUnionBootAdequacy.union_adequacy_unionΣ] with that premise          *)
(*  discharged.  [iris/UnionAssumptions.v] audits it.                     *)
(*                                                                        *)
(*  WHAT IT SAYS, with no Iris in the statement: IF the console input     *)
(*  kept the UNION discipline ([LineModel.lm_disc] at                     *)
(*  [UnionDisc.ulmG]: the user types lines of the shapes [echo ws],       *)
(*  [echo ws > f], [cat f], and [p | F1 | .. | Fn] for a producer [p]     *)
(*  ([echo ws] or [cat f]) and filter stages [cat] or [grep w] ([w] one   *)
(*  alphanumeric word), and [seccomp ws] ([ws] non-empty file-name       *)
(*  words; seccomp lane S4 -- the line ends the era's discipline, D4),    *)
(*  waiting for the prompt and for each byte's echo), THEN there is one   *)
(*  boot state per power cycle such that the FIRST cycle boots with no    *)
(*  [f], every later cycle boots at a chunk subsequence of an             *)
(*  [echo ... > f] line typed in a STRICTLY EARLIER cycle, and each       *)
(*  cycle's console output is a prefix of the transcript its input calls  *)
(*  for from that state ([LineModel.lm_good_out] at the union model).     *)
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
Require Import RiscvLang.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import RiscvAdequacy.
Require Import UserFd.
Require Import FsImgDisk.
Require Import AppFile.
Require Import EchoOut.
Require Import FileOut.
Require Import PipeOut.
Require Import App.                      (* [app_names] / [app_pred] / [app_boot] / [app_turn] *)
Require Import UnionOutPure.             (* [union_phi] *)
Require Import UnionOut.
Require Import UUnionBootAdequacy.       (* [union_prog_law], [unionΣ] *)
Require Import AppUnionRec.              (* [app_union]'s projections *)
Require Import UInitUnionBoot.           (* [union_Hinit_boot_at]: the assembly *)
Require UShURoundDefs.                   (* [ush_rdwild_of_shape] *)
Require PipeProto.                       (* [pipeProtoG]: the binders below need them in scope *)
Require UkPipesIface.
Require UkCatFIface.
Require UkFileIface.
Local Open Scope Z_scope.

Section UInitUnion.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{HU : !ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{HPP : !PipeProto.pipeProtoG Σ, HPR : !UkPipesIface.pnsRegG Σ,
            HPN : !UkPipesIface.pipesNG Σ, HCR : !UkCatFIface.cifRegG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  (* THE OPEN PREMISE (seccomp design 10.12, owner's ruling): the wild
     shape buys the era's reader-side credential, at every instance the
     law quantifies.  At the union [ai_rdwild] is [wild_none], so this is
     STATED AND NOT DISCHARGED; the law below is proved under it. *)
  Definition union_rdwild_premise : Prop :=
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ) (c : union_gn),
      UShURoundDefs.ush_rdwild_of_shape c.

  (* THE LAW, BY ITS NAME, under the open premise *)
  Theorem union_Hinit_boot_rd : union_rdwild_premise -> union_prog_law (Σ := Σ).
  Proof using HU HfifR HPP HPR HPN HCR.
    intros Hrdw HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface Hgen.
    cbn [app_union app_names app_pred app_ifc] in Heq, Hiface.
    iIntros "#Hinv Hb Hturn".
    iApply (union_Hinit_boot_at HR GEN c r Heq Hiface
              (Hrdw HR GEN HBs HFd HIr HPav HWc HF c) with "Hinv [Hb] [Hturn]").
    - cbn [app_union app_boot]. iExact "Hb".
    - cbn [app_union app_turn union_turn]. iExact "Hturn".
  Qed.

End UInitUnion.

(* ===================================================================== *)
(*  THE COROLLARY -- ONE LINE.                                           *)
(* ===================================================================== *)
(* FIRST, green, the conclusion under the open premise: what the audit
   reads while [union_adequacy_closed] waits on it *)
Corollary union_adequacy_closed_rd
    (Hrdw : union_rdwild_premise (Σ := unionΣ))
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ UnionOutPure.union_phi κs.
Proof.
  exact (union_adequacy_unionΣ (union_Hinit_boot_rd (Σ := unionΣ) Hrdw)
           g Hgen0 Hpow0 Hdisk).
Qed.

Corollary union_adequacy_closed
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ UnionOutPure.union_phi κs.
Proof.
  refine (union_adequacy_unionΣ (union_Hinit_boot_rd (Σ := unionΣ) _)
            g Hgen0 Hpow0 Hdisk).
  (* THE OPEN PREMISE, [union_rdwild_premise] at [unionΣ]: NOT discharged
     (seccomp design 10.12).  This proof is the one red spot. *)
Qed.
