(** * WeakLeafO.v — leaves with the [wstate] HIDDEN.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §4 / obligation
    §5.2, done WITHOUT re-basing [wmstate_interp].

    THE RESIDUE THIS REMOVES.  [WeakGhost.hart_ws] is an EXACT-valued
    [ghost_var], so a leaf can only step it by naming both states — which
    is why every caller above a leaf carried an [ws] binder, an
    [⌜ws_le ws ws'⌝] and an [hart_ws] in and out.  [WeakGhost.hart_view]
    pairs that exact half with the monotone authority under one
    existential, so the value is hidden outside and still exactly known
    inside; [hart_view_close] consumes the [ws_le] the leaf hands back, and
    it never reaches the caller.

    NOTHING BELOW THIS FILE CHANGES.  [WeakGhost]'s interpretation, and all
    twenty existing [WeakLeaf*.v] files, are untouched; so are the ~48
    [hart_ws_update] call sites.  Every wrapper here is the underlying leaf
    plus [hart_view_open] / [hart_view_close].

    THE FRAME.  A leaf carries its caller's other resources as
    [vwp_hold F ws] — indexed by the very [wstate] we are hiding.
    [WeakObj.wobj_to_hold] / [wobj_of_hold] convert, for ARBITRARY [F] and
    with no unfolding, so a wrapper takes [wobj F] in and hands [wobj F]
    back.  (An earlier draft discharged the frame at [⌜True⌝ ]; that made
    the statement look clean by throwing away the thing callers actually
    need.) *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop own.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RegFile.
Require Import RiscvFetchExec InstrBytes WpGpr WpMmodeLeafBase.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakPtOwn WeakPtPub WeakObj WeakLeafM.

Section leafo.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (** ** 1. THE GENERIC CONVERSION.

      Every ws-threading leaf in the tree has this shape once its curried
      resources are bundled into [Pre] / [Post] (check any of the twenty
      [WeakLeaf*.v] files: none of them mentions a [wstate] in [Pre] or
      [Post]).  So one lemma is the whole conversion, and the per-leaf
      sweep is bundling — mechanical, no new proof content.

      The frame [F] rides through as [wobj F]; [Pre] / [Post] are the
      leaf's own resources. *)
  Lemma leaf_hide (Pre Post : iProp Σ) (F : vProp Σ) :
    (∀ ws : wstate,
        ⊢ Pre -∗ hart_ws cpu_id ws -∗ vwp_hold F ws -∗
          (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ Post -∗ hart_ws cpu_id ws' -∗
             vwp_hold F ws' -∗ WWP Loop) -∗
          WWP Loop) ->
    Pre -∗ hart_view cpu_id -∗ wobj F -∗
    (Post -∗ hart_view cpu_id -∗ wobj F -∗ WWP Loop) -∗ WWP Loop.
  Proof.
    iIntros (Hleaf) "HPre [%ws [Hws Hauth]] HF Hcont".
    iDestruct (wobj_to_hold with "Hauth HF") as "[Hauth HF]".
    iApply (Hleaf ws with "HPre Hws HF").
    iIntros (ws') "%Hle HPost Hws HF".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iDestruct (wobj_of_hold with "Hauth HF") as "[Hauth HF]".
    iApply ("Hcont" with "HPost [Hws Hauth] HF").
    iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The worked leaf.

      Compare with [WeakLeafM.wwp_lui]: no [ws] parameter, no [∀ ws'], no
      [⌜ws_le ws ws'⌝], [hart_view cpu_id] in place of [hart_ws cpu_id ws]
      / [hart_ws cpu_id ws'], and [wobj F] in place of [vwp_hold F ws] /
      [vwp_hold F ws'].  What is left is [WpMmodeUtype.wp_lui_gpr]'s
      statement plus two names, both of which ride inside lines the SC
      proof already has.

      WHAT THE MEASUREMENT SAYS THIS IS WORTH (WkStartNew vs WpStartNew,
      34 instructions and 40 leaf applications each, code lines only):
      1612 vs 1337, i.e. 1.21x — and the [ws] threading accounts for ZERO
      of that gap.  It is 270 inline mentions spread over lines that exist
      in the SC proof too, so what this file buys is not lines.  It is
      that a caller's resources stop being indexed by a [wstate] at all,
      which is what lets them go in an invariant ([WeakObj]) — and that
      was never a line-count question. *)
  Lemma wwp_lui_o (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    hart_view cpu_id -∗
    wobj F -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      hart_view cpu_id -∗
      wobj F -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] HF Hcont".
    iDestruct (wobj_to_hold with "Hauth HF") as "[Hauth HF]".
    iApply (wwp_lui pc is_rvc rd imm m pmpcfg0 q ws F
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws HF".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iDestruct (wobj_of_hold with "Hauth HF") as "[Hauth HF]".
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile [Hws Hauth] HF").
    iExists ws'. iFrame.
  Qed.

End leafo.
