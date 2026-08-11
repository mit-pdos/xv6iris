(** * WeakLeafO.v — PROTOTYPE: leaves with the [wstate] HIDDEN.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §4 and obligation
    §5.2, done WITHOUT re-basing [wmstate_interp] — see "the cheap route"
    below.

    THE RESIDUE THIS REMOVES.  After [WeakLeafM]'s [winstr_m] token and the
    frame threading, instruction 35 of [WkStartNew] was 11 lines against SC's
    6, and what was left was exactly three things: the [ws] binder, the
    [⌜ws_le ws ws'⌝], and the [hart_ws] in and out.  All three exist for one
    reason — [WeakGhost.hart_ws] is an EXACT-valued [ghost_var], so a leaf
    can only step it by naming both states.

    THE CHEAP ROUTE.  [wmstate_interp] holds [wws_auth cpu_id σ.(wm_ws)], the
    other half of that [ghost_var].  It would be a large change to re-base
    it.  It is also unnecessary: BOTH halves of what a client needs are
    already client-side, so the monotone authority can be bundled with the
    client's [hart_ws] half and the interpretation left alone.

      [hart_view := ∃ ws, hart_ws cpu_id ws ∗ ws_auth γv ws]

    The existential is the whole trick — the value is hidden from the caller
    but still exactly known INSIDE, which is what lets [hart_view] be passed
    to an unmodified leaf.  Nothing in [WeakGhost], [WeakInterp] or any of
    the twenty existing leaf files changes; the ~48 [hart_ws_update] call
    sites are untouched.

    WHAT THIS BUYS AND WHAT IT DOES NOT.  It buys the SC-shaped leaf
    interface, and hence SC-shaped call sites, which is the whole point.  It
    does NOT by itself make [γv] implicit — that needs [weak_view_name] as a
    [weakGS] field and one new per-hart allocation in [WeakAdequacy], which
    changes the initial resource the boot composition receives.  Until then
    [γv] is a section parameter; making it implicit is a rename, not a
    reproof. *)
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
Require Import WeakViewMono WeakPtOwn WeakLeafM.

Section leafo.
  Context `{!riscvGS Σ, !weakGS Σ, !weakViewG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** In the eventual wiring, [weak_view_name cpu_id]. *)
  Context (γv : wview_names).

  (* ------------------------------------------------------------------ *)
  (** ** 1. The opaque token *)

  Definition hart_view : iProp Σ :=
    (∃ ws : wstate, hart_ws cpu_id ws ∗ ws_auth γv ws)%I.

  (** Snapshotting a floor: the only thing a caller can learn from the
      token, and being persistent it never has to be given back.  Code that
      does NOT care about views — every lock-disciplined function — never
      calls this. *)
  Lemma hart_view_lb : hart_view -∗ ∃ ws, hart_view ∗ ws_lb γv ws.
  Proof.
    iIntros "[%ws [Hws Hauth]]".
    iDestruct (ws_lb_get with "Hauth") as "#Hlb".
    iExists ws. iFrame "Hlb". iExists ws. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. THE GENERIC CONVERSION.

      Every ws-threading leaf in the tree has this shape, with [Pre] and
      [Post] mentioning no [wstate] (check any of the twenty
      [WeakLeaf*.v] files).  So one lemma converts all of them, and the
      remaining sweep is bundling each leaf's curried resources into the
      [Pre]/[Post] slots — mechanical, no new proof content. *)
  Lemma leaf_hide (Pre Post : iProp Σ) :
    (∀ ws : wstate,
        ⊢ Pre -∗ hart_ws cpu_id ws -∗
          (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ Post -∗ hart_ws cpu_id ws' -∗
             WWP Loop) -∗
          WWP Loop) ->
    Pre -∗ hart_view -∗ (Post -∗ hart_view -∗ WWP Loop) -∗ WWP Loop.
  Proof.
    iIntros (Hleaf) "HPre [%ws [Hws Hauth]] Hcont".
    iApply (Hleaf ws with "HPre Hws").
    iIntros (ws') "%Hle HPost Hws".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "HPost"). iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The worked leaf.

      Compare with [WeakLeafM.wwp_lui]: no [ws] parameter, no [F] frame, no
      [∀ ws'], no [⌜ws_le ws ws'⌝], and [hart_view] in place of [hart_ws
      cpu_id ws] / [hart_ws cpu_id ws'].  What is left is
      [WpMmodeUtype.wp_lui_gpr]'s statement plus ONE extra name in the
      [with "…"] and [iIntros] patterns — a name that rides inside lines the
      SC proof already has.  That is the 1.0x target from §4 of the design.

      The [F] frame [WeakLeafM.wwp_lui] carries is discharged here at
      [⌜True⌝]: with the caller's resources objective ([WeakPtOwn]) there is
      nothing left for it to carry, which is why it disappears rather than
      being threaded. *)
  Lemma wwp_lui_o (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    hart_view -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      hart_view -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_lui pc is_rvc rd imm m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

End leafo.
