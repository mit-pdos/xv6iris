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
Require Import UnionOutPure.             (* [union_phi_sync] *)
Require Import UUnionBootAdequacy.       (* [union_prog_law], [unionΣ] *)
Require Import AppUnionRec.              (* [app_union]'s projections *)
Require Import UInitUnionBoot.           (* [union_Hinit_boot_at]: the assembly *)
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

  (* THE LAW, BY ITS NAME.  The wild shape's reader-side credential is
     the union's own [ai_rdwild] ([UnionOut.urdwild]; seccomp design 10.12,
     lane S5b), so [UInitUnionBoot.union_Hinit_boot_at] needs nothing more. *)
  Theorem union_Hinit_boot : union_prog_law (Σ := Σ).
  Proof using HU HfifR HPP HPR HPN HCR.
    intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface Hgen Hhk.
    cbn [app_union app_names app_pred app_ifc app_hk] in Heq, Hiface, Hhk.
    iIntros "#Hinv Hb Hturn".
    iApply (union_Hinit_boot_at HR GEN c r Heq Hiface Hhk with "Hinv [Hb] [Hturn]").
    - cbn [app_union app_boot]. iExact "Hb".
    - cbn [app_union app_iturn union_turn]. iExact "Hturn".
  Qed.

End UInitUnion.

(* ===================================================================== *)
(*  THE COROLLARY -- ONE LINE.                                           *)
(* ===================================================================== *)
Corollary union_adequacy_closed
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ UnionOutPure.union_phi_sync κs.
Proof.
  exact (union_adequacy_unionΣ (union_Hinit_boot (Σ := unionΣ))
           g Hgen0 Hpow0 Hdisk).
Qed.

(* ===================================================================== *)
(*  THE SYNC'S CUT, REFUTED (sync SY3-A4): the negative demo's trace --  *)
(*  [echo a > a.txt; echo b > a.txt; sync], a power cut, then [cat       *)
(*  a.txt] printing [a] ([UnionAdmDemo.h_sa]) -- is no run of the        *)
(*  machine: the trace is disciplined ([UnionAdmDemo.sa_disc]), so the   *)
(*  theorem's conclusion holds of it, which the demo refutes at every    *)
(*  choice of boot states and records ([demo_sync_cut_neg]).             *)
(* ===================================================================== *)
Require Import UnionAdmDemo.

Corollary union_sync_cut_neg
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = fsimg_dk) :
  forall (n : nat) t2 g2,
    ~ language.nsteps n ([PowerLoopE : language.expr riscv_lang], g) h_sa (t2, g2).
Proof.
  intros n t2 g2 Hn.
  destruct (union_adequacy_closed g Hgen0 Hpow0 Hdisk n h_sa t2 g2 Hn) as [_ Hphi].
  destruct (Hphi sa_disc) as (W & H1 & H2 & H3 & H4).
  exact (demo_sync_cut_neg W (conj H1 (conj H2 (conj H3 H4)))).
Qed.

(* ===================================================================== *)
(*  THE TWO RESULTS AS ONE TERM, for the assumption audit             *)
(*  ([UnionAssumptions.v]): one [Print Assumptions] walks both cones,  *)
(*  the corollary's [sa_disc] and [demo_sync_cut_neg] included.        *)
(* ===================================================================== *)
Definition union_results := conj union_adequacy_closed union_sync_cut_neg.
