(* ===================================================================== *)
(*  UkShPipesFork.v -- TWO LEAVES OF THE N-STAGE FORK RE-ENTRY           *)
(*                                                                       *)
(*  What the union's round still takes from the pipeline application's   *)
(*  fork re-entry after union cut C9h deleted its [adm_echo] instance:   *)
(*  [big_sepL_exist_fun] (a big separating conjunction of existentials   *)
(*  over a duplicate-free list is one existential function) and          *)
(*  [alt_forkc_prompt] (the prompt's two bytes are positions 5 and 6 of  *)
(*  the fork-failure alternative).                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import LineModel.
Require Import LineModelLinks.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import PipesFire.
Require Import UkPipesIface.      (* [pnsN], [pipesNG] *)
Require Import GenLinksLine.
Require Import LinkRec.
Require Import FdSlots UserFd.
Require Import UkRun.
Require Import UkSh.
Require Import UkShFork.
Require Import Xv6G Xv6Cameras.
Require Import EchoOutPure.
Require Import IrefSlots ProcAvail FileInvDefs.
Require Import ConsoleInv.
Require Import UCodeShK.
Require Import UShPanic.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import UexecExecInst.
Require Import CtxIdDefs.
Local Open Scope list_scope.
Require PipeDisc.
Local Notation alt_forkc := PipeDisc.alt_forkc.

Local Notation fcE := (fun _ : bytes => @None bytes).

(* a list of per-writer existentials, at a duplicate-free list, is one
   existential function *)
Lemma big_sepL_exist_fun {PROP : bi} {A B : Type} `{!EqDecision A} (d : B)
    (l : list A) (Φ : A -> B -> PROP) :
  stdpp.base.NoDup l ->
  ([∗ list] x ∈ l, ∃ y, Φ x y) ⊢ ∃ f : A -> B, [∗ list] x ∈ l, Φ x (f x).
Proof using.
  induction l as [| x l IH]; intros Hnd.
  - iIntros "_". iExists (fun _ => d). done.
  - pose proof (NoDup_cons_1_1 x l Hnd) as Hx. pose proof (NoDup_cons_1_2 x l Hnd) as Hnd'. clear Hnd. rename Hnd' into Hnd.
    rewrite big_sepL_cons. iIntros "[Hx Hl]". iDestruct "Hx" as (y) "Hx".
    iDestruct (IH Hnd with "Hl") as (f) "Hl".
    iExists (fun z => if decide (z = x) then y else f z).
    rewrite big_sepL_cons decide_True //. iFrame "Hx".
    iApply (big_sepL_impl with "Hl"). iIntros "!>" (i z Hz) "H".
    rewrite decide_False; [done |]. intros ->. apply Hx.
    by eapply elem_of_list_lookup_2.
Qed.

(* ===================================================================== *)
(*  S3  THE TWO PROMPT BYTES AT THE TERMINAL ARM                          *)
(* ===================================================================== *)
Lemma alt_forkc_prompt (p : nat) (b : bv 8) :
  u_prompt !! p = Some b -> alt_forkc !! (5 + p)%nat = Some b.
Proof using.
  intros Hb. rewrite alt_forkc_fork lookup_app_r; [| rewrite dg_fork_b_len; lia].
  by rewrite dg_fork_b_len Nat.add_sub_swap // Nat.sub_diag Nat.add_0_l.
Qed.
