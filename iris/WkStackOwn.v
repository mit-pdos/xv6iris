(** * WkStackOwn.v — the weak-tier stack ownership bundle (M4 batch 4)

    The [↦w₈]/[wpt8] respell of [StackOwn.stack_own_phys], for the weak
    ports of the M-mode boot functions ([wwp_timerinit]/[wwp_start] and the
    composed entry cone): the porting-table swap
    [a ↦ₚ₈{dq} w  →  vwp_hold (wpt8 a dq w) ws] applied to the whole
    [stack_own_phys] suite.

    The bundle is a [vProp] ([wstack_own_phys]), consumed by the chains under
    [vwp_hold] at the hart's current [wstate]; because [vProp]s are monotone
    in the view, [vwp_hold_mono] carries it across every step for free
    ([wstack_own_mono] below is that instance).  The lemma suite mirrors
    [StackOwn]'s scripts verbatim — the only change is the BI it lives in.

    NOTE (recorded porting-table delta): [phys_word_pointsto] lives in the
    era [gen_heap], whose domain is RAM by construction, so the SC chains
    never state [addr_is_ram] for stack slots.  [wpt8] is [Z]-keyed ghost
    state with no RAM tie, so the weak chains carry explicit
    [addr_is_ram (pa_add (pa_stk sp k) j)] PREMISES over the symbolic frame
    slots — that pure side is deliberately NOT bundled here. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost.
Require Import WeakView WeakVProp.
Require Import WeakInstr WeakWord8.
Require Import RiscvLang RiscvPtsto.
Require Import StackOwn.

Local Open Scope Z_scope.

Section wstack_own_phys.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** The weak stack bundle: [StackOwn.stack_own_phys] with [↦ₚ₈] swapped
      for [wpt8], at the vProp altitude. *)
  Definition wstack_own_phys (sp : Arch.pa) (n : nat) : vProp Σ :=
    (∃ ws : list (bv 64), ⌜length ws = n⌝ ∗
       [∗ list] i ↦ w ∈ ws, wpt8 (pa_stk sp (S i)) (DfracOwn 1) w)%I.

  Lemma wstack_own_phys_0 (sp : Arch.pa) : wstack_own_phys sp 0 ⊣⊢ emp.
  Proof.
    rewrite /wstack_own_phys. iSplit.
    - iIntros "H". done.
    - iIntros "_". iExists []. by iSplit.
  Qed.

  Lemma wstack_own_phys_app (sp : Arch.pa) (n1 n2 : nat) :
    wstack_own_phys sp (n1 + n2)
    ⊣⊢ wstack_own_phys sp n1 ∗ wstack_own_phys (pa_stk sp n1) n2.
  Proof.
    rewrite /wstack_own_phys. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      rewrite -(take_drop n1 ws) big_sepL_app.
      iDestruct "H" as "[H1 H2]".
      assert (Hle : (n1 ≤ length ws)%nat) by lia.
      iSplitL "H1".
      + iExists (take n1 ws). iFrame "H1". iPureIntro.
        rewrite length_take. lia.
      + iExists (drop n1 ws). iSplitR.
        { iPureIntro. rewrite length_drop. lia. }
        rewrite length_take_le; [| exact Hle].
        iApply (big_sepL_proper with "H2").
        intros i w _. by rewrite pa_stk_shift.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (ws1) "[%Hlen1 H1]".
      iDestruct "H2" as (ws2) "[%Hlen2 H2]".
      iExists (app ws1 ws2). iSplitR.
      { iPureIntro. rewrite length_app. lia. }
      rewrite big_sepL_app. iFrame "H1".
      rewrite Hlen1.
      iApply (big_sepL_proper with "H2").
      intros i w _. by rewrite pa_stk_shift.
  Qed.

  Lemma wstack_own_phys_split (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    wstack_own_phys sp n
    ⊣⊢ wstack_own_phys sp a ∗ wstack_own_phys (pa_stk sp a) (n - a).
  Proof.
    intro Hle. replace n with (a + (n - a))%nat at 1 by lia.
    apply wstack_own_phys_app.
  Qed.

  Lemma wstack_own_phys_1 (sp : Arch.pa) :
    wstack_own_phys sp 1
    ⊣⊢ ∃ w : bv 64, wpt8 (pa_stk sp 1) (DfracOwn 1) w.
  Proof.
    rewrite /wstack_own_phys. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      destruct ws as [| w [| ??]]; simpl in Hlen; try lia.
      iExists w. iDestruct "H" as "[$ _]".
    - iIntros "H". iDestruct "H" as (w) "H".
      iExists [w]. iSplitR; [done|]. simpl. iFrame.
  Qed.

  Lemma wstack_own_phys_1_intro (sp : Arch.pa) (w : bv 64) :
    wpt8 (pa_stk sp 1) (DfracOwn 1) w ⊢ wstack_own_phys sp 1.
  Proof. rewrite wstack_own_phys_1. iIntros "H". by iExists w. Qed.

  Lemma wstack_own_phys_split_1 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    wstack_own_phys sp n
    ⊢ wstack_own_phys sp a ∗ wstack_own_phys (pa_stk sp a) (n - a).
  Proof. intro Hle. by rewrite (wstack_own_phys_split sp a n Hle). Qed.

  Lemma wstack_own_phys_split_2 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    wstack_own_phys sp a ∗ wstack_own_phys (pa_stk sp a) (n - a)
    ⊢ wstack_own_phys sp n.
  Proof. intro Hle. by rewrite (wstack_own_phys_split sp a n Hle). Qed.

  Lemma wstack_own_phys_2_elim (sp : Arch.pa) :
    wstack_own_phys sp 2 ⊢ ∃ w1 w2 : bv 64,
      wpt8 (pa_stk sp 1) (DfracOwn 1) w1 ∗
      wpt8 (pa_stk sp 2) (DfracOwn 1) w2.
  Proof.
    rewrite (wstack_own_phys_app sp 1 1) wstack_own_phys_1.
    iIntros "[H1 H2]". iDestruct "H1" as (w1) "H1".
    rewrite wstack_own_phys_1 (pa_stk_assoc sp 1 1).
    iDestruct "H2" as (w2) "H2". iExists w1, w2. iFrame.
  Qed.

  Lemma wstack_own_phys_2_intro (sp : Arch.pa) (w1 w2 : bv 64) :
    wpt8 (pa_stk sp 1) (DfracOwn 1) w1 -∗
    wpt8 (pa_stk sp 2) (DfracOwn 1) w2 -∗
    wstack_own_phys sp 2.
  Proof.
    iIntros "H1 H2". rewrite (wstack_own_phys_app sp 1 1). iSplitL "H1".
    - by iApply wstack_own_phys_1_intro.
    - rewrite -(pa_stk_assoc sp 1 1). by iApply wstack_own_phys_1_intro.
  Qed.

  (* ==================================================================== *)
  (** ** The [vwp_hold] side: what the chains actually thread.

      An entailment between [vProp]s holds at every index, so it transports
      under [vwp_hold] pointwise; and the bundle crosses a step by
      [vwp_hold_mono].  These two lemmas are all a chain needs to open,
      carry and re-close the bundle. *)

  Lemma vwp_hold_ent (P Q : vProp Σ) (ws : wstate) :
    (P ⊢ Q) -> vwp_hold P ws ⊢ vwp_hold Q ws.
  Proof. intros HPQ. rewrite /vwp_hold HPQ. done. Qed.

  Lemma wstack_own_mono (sp : Arch.pa) (n : nat) (ws ws' : wstate) :
    ws_le ws ws' ->
    vwp_hold (wstack_own_phys sp n) ws ⊢ vwp_hold (wstack_own_phys sp n) ws'.
  Proof. apply vwp_hold_mono. Qed.

End wstack_own_phys.

Print Assumptions wstack_own_phys_app.
Print Assumptions wstack_own_phys_2_elim.
Print Assumptions wstack_own_mono.
