(* ===================================================================== *)
(*  UShURoundShapes.v -- THE UNION ROUND AT THE PIPELINE'S OWN SHAPES     *)
(*  (cut C9f1; design: claude-notes/design/union.md section 3, review B3). *)
(*                                                                        *)
(*  The two shapes the union's pipeline rounds leave ([UkShPipesFork.     *)
(*  pterm_shapeN] / [pdone_shapeN] at the union's view: the family's      *)
(*  runs at the round's state [sR], its credential [UnionOut.pwc_blkU]).  *)
(*  They are EXACTLY what the right spine's [Qtop] reads into (C9f2,      *)
(*  [UShUPipes.ufin]): a fork failed at node [i] with the waited stages'  *)
(*  halves, or every writer committed.  B3: the terminal shape carries NO *)
(*  deed; the committed one gets the deed at its PRE tie through          *)
(*  [UShURoundDefs.uWcu]'s index-0 arm (the block is not filed yet).      *)
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
Require Import RiscvPtsto.
Require Import WpUart.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import LineModel.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import UkPipesIface.      (* [pnsN], [pipesNG] *)
Require Import UnionDisc.
Require Import UnionView.
Require Import UnionOut.
Require Import CtxIdDefs.
Require PipeDisc.
Local Open Scope list_scope.

Local Notation U := ulmU.

Section UShURoundShapes.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ, !pipesNG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).

  (* A FORK FAILED at node [i] of the right spine: the family's writer
     [WSh i] wrote [fork], the waited stages' halves at their sources *)
  Definition upterm_shape (I : list (bv 8)) (c : nat) : iProp Σ :=
    (∃ (v : era_pins) (γc γm : wid -> gname) (dep : wid -> list (bv 8) -> iProp Σ)
       (i : nat) (sw : nat -> list (bv 8)) (sR : fstate) (lR : pline'),
       ⌜(forall w s, Timeless (dep w s))
        /\ pv_line pview_unionU (lineV U I) = Some lR /\ adm_u_f lR = true
        /\ pl_ok lR /\ (i < lcats lR)%nat /\ (1 <= nlines I)%nat⌝
       ∗ era_pin (fgn_echo gf) (S gen_id) v
       ∗ inp_lb v I
       ∗ pwc_fork_exitN (wids (lcats lR)) (runN (files_of sR) lR)
           (pwc_blkU ug v I sR) (ptkU ug v I) termw (tokN (files_of sR) lR)
           dep pnsN (S gen_id) γc γm (WSh i) PipeDisc.alt_forkc c
       ∗ [∗ list] x ∈ heldN i sw,
           wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2))%I.

  (* THE ROUND COMMITTED BUT NOT FILED: every writer at its whole source *)
  Definition updone_shape (I : list (bv 8)) : iProp Σ :=
    (∃ (v : era_pins) (γc γm : wid -> gname) (dep : wid -> list (bv 8) -> iProp Σ)
       (sR : fstate) (lR : pline'),
       ⌜(forall w s, Timeless (dep w s))
        /\ pv_line pview_unionU (lineV U I) = Some lR /\ adm_u_f lR = true
        /\ pl_ok lR⌝
       ∗ era_pin (fgn_echo gf) (S gen_id) v
       ∗ inp_lb v I
       ∗ blkN_inv (wids (lcats lR)) (runN (files_of sR) lR)
           (pwc_blkU ug v I sR) termw (tokN (files_of sR) lR) dep pnsN (S gen_id) γc γm
       ∗ [∗ list] w ∈ wids (lcats lR),
           ∃ s, wcurN γc w (1/2) (length s) ∗ wmodeN γm w (1/2) (Some s)
                ∗ ⌜termw w s = false⌝)%I.
End UShURoundShapes.
