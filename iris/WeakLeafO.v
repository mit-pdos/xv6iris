(** * WeakLeafO.v — leaves with the [wstate] HIDDEN.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §4 / obligation
    §5.2, done WITHOUT re-basing [wmstate_interp].

    THE RESIDUE THIS REMOVES.  [WeakGhost.hart_ws] is an EXACT-valued
    [ghost_var], so a leaf can only step it by naming both states — which
    is why every caller above a leaf carried an [ws] binder, an
    [⌜ws_le ws ws'⌝] and an [hart_ws] in and out.  Hiding the value under an
    existential is what removes that residue: it is unknown outside and
    still exactly known inside, so the [ws_le] the leaf hands back is
    consumed at the seam and never reaches the caller.

    (HISTORICAL: this file was first written against
    [WeakGhost.hart_view_open]/[_close], which paired the exact half with a
    per-hart MONOTONE authority.  The wrappers below go through
    [WeakCtx.wrunning] instead — the authority is indexed by a CONTEXT, not
    a hart — and those lemmas, and the [weak_view_name] field behind them,
    are deleted.)

    NOTHING BELOW THIS FILE CHANGES.  [WeakGhost]'s interpretation, and all
    twenty existing [WeakLeaf*.v] files, are untouched; so are the ~48
    [hart_ws_update] call sites.  Every wrapper here is the underlying leaf
    plus the context-token open/close pair.

    THE FRAME IS GONE, AND THAT IS THE POINT.  [WeakLeafM]'s leaves take
    the caller's other resources as [vwp_hold F ws] and hand back
    [vwp_hold F ws'].  That plumbing existed for ONE reason: a [vProp]
    frame is indexed by the hart's view, so when the leaf moved [ws] to
    [ws'] the frame had to be carried along to be re-indexed.

    An objective frame does not.  [WeakObj.wobj F] is an [iProp] whose only
    view-dependence is a PERSISTENT floor ([view_lb]), and floors only
    grow — so [wobj F] is still true after the step without anyone having
    touched it.  It therefore stays in the Iris context across the leaf,
    exactly as an SC caller's resources do, and the wrappers below
    instantiate [F := ⌜True⌝ ] and take no frame argument at all.

    A caller that wants to USE the frame (do a load out of it) converts at
    that point with [wobj_to_hold], which needs the authority inside
    [hart_view] — once, where the load is, not once per instruction.

    AND THE LAST NAME GOES INTO THE AMBIENT BUNDLE.  [hart_view] itself
    cannot be hidden by bundling a VALUE — it is exclusive ownership, and
    somebody has to hand it to whoever updates it.  But it can be hidden by
    riding in the ambient per-hart bundle a leaf already takes and returns,
    which is [mmode_config] here and would be [IntrDefs.sie_cap_gpr] for
    S-mode kernel code.

    ONE OBSTACLE, and it is why [hart_view] is not simply added to
    [mmode_config]: that bundle is FRACTIONAL ([InstrBytes.mmode_config_split],
    used at [q/2] by ten files) and [hart_view] is exclusive — a fraction of
    it could not be updated.  So [whart_run] below wraps rather than
    extends: it takes the fraction as a parameter and is itself
    non-fractional.  Leaf proofs that need to split still can; they open the
    bundle first.

    THE RESULT IS A STEP SITE NAME-FOR-NAME IDENTICAL TO SC's, because the
    bundle occupies the slot [mmode_config] already occupied. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop own.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
(* the CSR numbers §6 names -- see [WeakLeafM]'s note: the write-side
   [WpGprCsrwA] redefines two of them, so only the read-side homes go here. *)
Require Import ExecCommon WpGprCsrrA WpGprCsrrB.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RegFile.
Require Import RiscvFetchExec InstrBytes WpGpr WpMmodeLeafBase.
Require Import RiscvExtras MinstretInv WpGprMretWp.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakCtx WeakPtPub WeakWord8 WeakLeafM.

Section leafo.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (** ** 0. THE AMBIENT BUNDLE.

      [mmode_config] plus this hart's view token.  Non-fractional on
      purpose (see the header); the [q] is [mmode_config]'s and is threaded
      exactly as before. *)
  Definition whart_run (ξ : CtxId) (q : Qp) : iProp Σ :=
    (mmode_config (DfracOwn q) ∗ wrunning ξ)%I.

  Lemma whart_run_open ξ q :
    whart_run ξ q -∗ mmode_config (DfracOwn q) ∗ wrunning ξ.
  Proof. iIntros "$". Qed.

  Lemma whart_run_close ξ q :
    mmode_config (DfracOwn q) -∗ wrunning ξ -∗ whart_run ξ q.
  Proof. iIntros "H1 H2". iFrame. Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 1. THE GENERIC CONVERSION.

      Every ws-threading leaf in the tree has this shape once its curried
      resources are bundled into [Pre] / [Post] (check any of the twenty
      [WeakLeaf*.v] files: none of them mentions a [wstate] in [Pre] or
      [Post]).  So one lemma is the whole conversion, and the per-leaf
      sweep is bundling — mechanical, no new proof content.

      No frame appears: see the header.  [Pre] / [Post] are the leaf's own
      resources, and the caller's stay in its context. *)
  Lemma leaf_hide (ξ : CtxId) (Pre Post : iProp Σ) :
    (∀ ws : wstate,
        ⊢ Pre -∗ hart_ws cpu_id ws -∗
          (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ Post -∗ hart_ws cpu_id ws' -∗
             WWP Loop) -∗
          WWP Loop) ->
    Pre -∗ wrunning ξ -∗ (Post -∗ wrunning ξ -∗ WWP Loop) -∗
    WWP Loop.
  Proof.
    iIntros (Hleaf) "HPre [%ws [Hws Hauth]] Hcont".
    iApply (Hleaf ws with "HPre Hws").
    iIntros (ws') "%Hle HPost Hws".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "HPost"). iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The worked leaf.

      Compare with [WeakLeafM.wwp_lui]: no [ws] parameter, no [∀ ws'], no
      [⌜ws_le ws ws'⌝], no frame in or out, and [wrunning ξ] in place
      of [hart_ws cpu_id ws] / [hart_ws cpu_id ws'].

      SO THE CALL SITE IS [WpMmodeUtype.wp_lui_gpr]'S PLUS EXACTLY ONE
      NAME.  Against [WkStartNew]'s instruction 35 as it stands today:

        SC     iApply (wp_lui_gpr … with "Hmm HpcfA Hpc Hfile Hi35").
               iIntros "Hmm HpcfA Hpc Hfile".
        NOW    iApply (wwp_lui … ws34 _ … with "… Hi35 Hhws Hstk").
               iIntros (ws35) "%Hwsle35 Hmm HpcfA Hpc Hfile Hhws Hstk".
        HERE   iApply (wwp_lui_o ξ … with "Hmm HpcfA Hpc Hfile Hi35 Hhws").
               iIntros "Hmm HpcfA Hpc Hfile Hhws".

      [ws34], [%Hwsle35] and [Hstk] are gone.  [Hhws] is NOT, and cannot be
      removed at this altitude: it is the client half of an exclusive
      [ghost_var], so it has to be passed to whoever updates it.  Deleting
      it means moving the whole cell into [wmstate_interp] — see the
      worklist entry "the last name". *)
  Lemma wwp_lui_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
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
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      wrunning ξ -∗
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
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The same leaf, against the bundle.

      THIS IS THE ONE TO COMPARE.  Every resource slot is [wp_lui_gpr]'s,
      and the hart's view rides inside the slot [mmode_config] already
      occupied — so a caller's step site is SC's, name for name:

        SC     iApply (wp_lui_gpr … with "Hmm HpcfA Hpc Hfile Hi35").
               iIntros "Hmm HpcfA Hpc Hfile".
        HERE   iApply (wwp_lui_run … with "Hmm HpcfA Hpc Hfile Hi35").
               iIntros "Hmm HpcfA Hpc Hfile".

      No [ws], no [ws_le], no frame, no view token.  The only difference
      left is the lemma's name and that [Hmm] is bound to [whart_run ξ q]
      rather than [mmode_config (DfracOwn q)]. *)
  Lemma wwp_lui_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_lui_o ξ pc is_rvc rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. [addi], both wrappers.

      Included to fix the TEMPLATE, since the remaining sweep is this pair
      per instruction and nothing else.  Neither proof does anything
      instruction-specific: [_o] is [WeakCtx]'s context open/update/close
      around the [winstr_m] leaf, and [_run] is [whart_run_open] /
      [whart_run_close] around [_o]. *)
  Lemma wwp_addi_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_addi pc is_rvc rs1 rd imm m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_addi_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_addi_o ξ pc is_rvc rs1 rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 5. The rest of the register-only ALU family.

      Five instructions, two wrappers each, and the template above filled in
      literally: the ONLY per-instruction text is the binder list, the AST,
      the post-state [gpr_file] expression and the pc bump.  These five are
      stated at a fixed encoding for the reason [WeakLeafM] §6 records --
      their leaves cover one encoding each -- so [if is_rvc then 2 else 4]
      becomes the constant the leaf proves. *)

  (** *** 5a. [c.or] *)
  Lemma wwp_or_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_or_rvc pc rs2 rs1 rd m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_or_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_or_rvc_o ξ pc rs2 rs1 rd m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5b. [c.add] / [c.mv] *)
  Lemma wwp_add_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_add_rvc pc rs2 rs1 rd m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_add_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_add_rvc_o ξ pc rs2 rs1 rd m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5c. [c.slli] *)
  Lemma wwp_slli_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_slli_rvc pc rs1 rd shamt m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_slli_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_slli_rvc_o ξ pc rs1 rd shamt m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5d. [c.addiw] *)
  Lemma wwp_addiw_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (immv : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (sign_extend' 64
                    (subrange_vec_dec
                       (add_vec (m !!! Regidx rs1)
                          (sign_extend' 64 immv)) 31 0))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_addiw_rvc pc rs1 rd immv m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_addiw_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (immv : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (sign_extend' 64
                    (subrange_vec_dec
                       (add_vec (m !!! Regidx rs1)
                          (sign_extend' 64 immv)) 31 0))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_addiw_rvc_o ξ pc rs1 rd immv m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5e. [ori] -- the uncompressed one, so the bump is 4. *)
  Lemma wwp_ori_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_ori pc rs1 rd imm m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_ori_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_ori_o ξ pc rs1 rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 6. The CSR-read family.

      Same two wrappers, two more resource slots.  [csrr_time]'s
      continuation keeps the leaf's [∀ tv]: the value read is not one the
      proof owns, and hiding it would be a lie, not a simplification. *)

  (** *** 6a. [csrr rd, menvcfg] *)
  Lemma wwp_csrr_menvcfg_o (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (menvcfg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg menvcfg_in -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hcsr Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_menvcfg pc rd menvcfg_in rd0 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrd Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrr_menvcfg_run (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (menvcfg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg menvcfg_in -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hcsr Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrr_menvcfg_o ξ pc rd menvcfg_in rd0 pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrd Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrd Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 6b. [csrr rd, mcounteren] *)
  Lemma wwp_csrr_mcounteren_o (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mcounteren ↦ᵣ mcen_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (zero_extend' 64 mcen_in) -∗
      mcounteren ↦ᵣ mcen_in -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hcsr Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_mcounteren pc rd mcen_in rd0 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrd Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrr_mcounteren_run (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mcounteren ↦ᵣ mcen_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (zero_extend' 64 mcen_in) -∗
      mcounteren ↦ᵣ mcen_in -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hcsr Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrr_mcounteren_o ξ pc rd mcen_in rd0 pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrd Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrd Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 6c. [csrr rd, mhartid] *)
  Lemma wwp_csrr_mhartid_o (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mhartid_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mhartid ↦ᵣ mhartid_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg mhartid_in -∗
      mhartid ↦ᵣ mhartid_in -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hcsr Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_mhartid pc rd mhartid_in rd0 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrd Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrr_mhartid_run (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mhartid_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mhartid ↦ᵣ mhartid_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg mhartid_in -∗
      mhartid ↦ᵣ mhartid_in -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hcsr Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrr_mhartid_o ξ pc rd mhartid_in rd0 pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hcsr Hrd Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrd Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrd Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 6d. [csrr rd, time] *)
  Lemma wwp_csrr_time_o (ξ : CtxId) (pc : mword 64) (rd : mword 5) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( ∀ tv : mword 64,
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg tv -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_time pc rd rd0 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrd Hi Hws HF").
    iIntros (tv ws') "%Hle Hmm Hpcf Hpc Hrd Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" $! tv with "Hmm Hpcf Hpc Hrd"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrr_time_run (ξ : CtxId) (pc : mword 64) (rd : mword 5) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( ∀ tv : mword 64,
      whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg tv -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrr_time_o ξ pc rd rd0 pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrd Hi Hview").
    iIntros (tv) "Hmm Hpcf Hpc Hrd Hview".
    iApply ("Hcont" $! tv with "[Hmm Hview] Hpcf Hpc Hrd").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 7. The CSR-write family.

      Same qualified-name discipline as [WeakLeafM] §8, and for the same
      reason: this file imports the READ-side CSR-number table, so the
      write-side numbers and legalisers are spelled out. *)

  (** *** 7a. [csrw menvcfg, rs1] *)
  Lemma wwp_csrw_menvcfg_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (menvcfg0 : type_of_register menvcfg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      menvcfg ↦ᵣ WpGprCsrwA.menvcfg_legalized menvcfg0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_menvcfg pc rs1 menvcfg0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_menvcfg_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (menvcfg0 : type_of_register menvcfg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      menvcfg ↦ᵣ WpGprCsrwA.menvcfg_legalized menvcfg0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_menvcfg_o ξ pc rs1 menvcfg0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 7b. [csrw mcounteren, rs1] *)
  Lemma wwp_csrw_mcounteren_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mcounteren0 : type_of_register mcounteren) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_mcounteren pc rs1 mcounteren0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_mcounteren_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mcounteren0 : type_of_register mcounteren) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_mcounteren_o ξ pc rs1 mcounteren0 rs1v pmpcfg0 q
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 7c. [csrw stimecmp, rs1] *)
  Lemma wwp_csrw_stimecmp_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (stimecmp0 : type_of_register stimecmp) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      stimecmp ↦ᵣ WpGprCsrwB.stimecmp_legalized stimecmp0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_stimecmp pc rs1 stimecmp0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_stimecmp_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (stimecmp0 : type_of_register stimecmp) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      stimecmp ↦ᵣ WpGprCsrwB.stimecmp_legalized stimecmp0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_stimecmp_o ξ pc rs1 stimecmp0 rs1v pmpcfg0 q
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 8. Control flow. *)

  (** *** 8a. [jal rd, imm] *)
  Lemma wwp_jal_o (ξ : CtxId) (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (rdv0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rdv0 -∗
    winstr_m pc false (JAL (imm, Regidx rd)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      R_bitvector_64 (gpr_of_Z (uint rd))
        ↦ᵣ (regval_into_reg (add_vec_int pc 4)) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz Htgt.
    iIntros "Hmm Hpcf Hpc Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_jal pc rd imm rdv0 pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz Htgt with "Hmm Hpcf Hpc Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrd"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_jal_run (ξ : CtxId) (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (rdv0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rdv0 -∗
    winstr_m pc false (JAL (imm, Regidx rd)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      R_bitvector_64 (gpr_of_Z (uint rd))
        ↦ᵣ (regval_into_reg (add_vec_int pc 4)) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz Htgt.
    iIntros "Hrun Hpcf Hpc Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_jal_o ξ pc rd imm rdv0 pmpcfg0 q Hgid Hpmp Hnz Htgt
              with "Hmm Hpcf Hpc Hrd Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrd Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrd").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 8b. [c.jr ra] *)
  Lemma wwp_cjr_rvc_o (ξ : CtxId) (pc : mword 64) (ra : mword 5) (rav : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
    winstr_m pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (ret_pc rav) -∗
      R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hra #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_cjr_rvc pc ra rav pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hra Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hra Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hra"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_cjr_rvc_run (ξ : CtxId) (pc : mword 64) (ra : mword 5) (rav : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
    winstr_m pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (ret_pc rav) -∗
      R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hra #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_cjr_rvc_o ξ pc ra rav pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hra Hi Hview").
    iIntros "Hmm Hpcf Hpc Hra Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hra").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 8c. [mret] -- [_o] ONLY, and the absence of [_run] is the point.

      [whart_run] bundles [mmode_config], which asserts [cur_privilege ↦ᵣ
      Machine].  [mret] sets that cell to [Supervisor], so there is no
      [whart_run] to hand back: the bundle is not preserved by this
      instruction, it is DISSOLVED by it.  Writing a [_run] here would mean
      inventing an S-mode bundle to return, which is [sconf]'s job and is
      where the design notes say [hart_view] should live once the port
      reaches S-mode.  Until then [mret] stops at [_o], which is honest
      about what it has: the view token in and the view token out, with the
      five M-mode cells passing through individually. *)
  Lemma wwp_mret_o (ξ : CtxId) (pc : mword 64) (newpriv : Privilege)
      (ms_cur mepc0 menvcfg1 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms_cur) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms_cur) ('b"1") = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms_cur -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    menvcfg ↦ᵣ menvcfg1 -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_m pc false (MRET tt) -∗
    wrunning ξ -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ newpriv -∗
      mstatus ↦ᵣ cms5 ms_cur -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      menvcfg ↦ᵣ menvcfg1 -∗
      mepc ↦ᵣ mepc0 -∗
      pc_is (ret_pc mepc0) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp HmIE Hmprv Hfwd Hnew Hlpe.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hmenv Hmepc
             #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_mret pc newpriv ms_cur mepc0 menvcfg1 pmpcfg0 ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp HmIE Hmprv Hfwd Hnew Hlpe
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hmenv Hmepc Hi Hws HF").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc").
    iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 9. The load -- and where the sweep stops.

      [c.ld] is the first wrapper here whose frame is not [⌜True⌝, and it
      is the one that shows what [wobj] bought: the caller holds an
      OBJECTIVE eight-byte points-to, hands it in, and gets it back, with
      no [ws] anywhere in the statement.  [wobj_to_hold] / [wobj_of_hold]
      do the conversion generically, so this proof says nothing about
      [wpt8] in particular. *)
  Lemma wwp_ld8_tor_rvc_o (ξ : CtxId) (pc : mword 64) (rs1 rd : mword 5) (imm : mword 12)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rd0 : mword 64) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    wrunning ξ -∗
    cobj ξ (wpt8 ea dqv v) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
      wrunning ξ -∗
      cobj ξ (wpt8 ea dqv v) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnzd Hea Hram.
    iIntros "Hmm Hpcf Hpad Hpc Hrs Hrd #Hi [%ws [Hws Hauth]] Hpt Hcont".
    iDestruct (cobj_to_hold ξ ws with "Hauth Hpt") as "[Hauth Hpt]".
    iApply (wwp_ld8_tor_rvc pc rs1 rd imm ea v dqv q pmpcfg0 pmpaddrs
              rs1v rd0 ws Hgid Hpmp Htor Hnz1 Hnzd Hea Hram
              with "Hmm Hpcf Hpad Hpc Hrs Hrd Hi Hws Hpt").
    iIntros (ws') "%Hle Hmm Hpcf Hpad Hpc Hrs Hrd Hws Hpt".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iDestruct (cobj_of_hold ξ ws' with "Hauth Hpt") as "[Hauth Hpt]".
    iApply ("Hcont" with "Hmm Hpcf Hpad Hpc Hrs Hrd [Hws Hauth] Hpt").
    iExists ws'. iFrame.
  Qed.

  Lemma wwp_ld8_tor_rvc_run (ξ : CtxId) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rd0 : mword 64) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    cobj ξ (wpt8 ea dqv v) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
      cobj ξ (wpt8 ea dqv v) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnzd Hea Hram.
    iIntros "Hrun Hpcf Hpad Hpc Hrs Hrd #Hi Hpt Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_ld8_tor_rvc_o ξ pc rs1 rd imm ea v dqv q pmpcfg0 pmpaddrs
              rs1v rd0 Hgid Hpmp Htor Hnz1 Hnzd Hea Hram
              with "Hmm Hpcf Hpad Hpc Hrs Hrd Hi Hview Hpt").
    iIntros "Hmm Hpcf Hpad Hpc Hrs Hrd Hview Hpt".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpad Hpc Hrs Hrd Hpt").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** ** 10. [c.sd], THE RELEASE STORE -- the one wrapper with a payload.

      This was the file's open interface question, and it was open for a
      reason worth keeping on the record.  Every other wrapper here hides
      [ws'] behind the context; the release store could not be wrapped that
      way, because part of its result is a statement ABOUT [ws']:

        ⌜∀ j, (j < 8)%nat -> T ≤ flr (ws_view ws') (acc_addr ea j)⌝

      -- the released timestamp [T] sits below the post-state view at the
      eight stored bytes, which is what lets the acquirer of the lock
      recover the payload.  Hiding [ws'] erases it, so no amount of
      mechanical wrapping would do; what was missing was a CONSTRUCTOR
      taking the authority plus a bound at a finite set of addresses and
      returning an objective token.

      [WeakCtx] §8 is that constructor ([ctx_addrs_get] / [ctx_addrs_valid]),
      and the token is [ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T)].  Note
      it is NOT a per-byte family: [ctx_view_lb] bounds one view, and the
      eight byte-bounds collapse into a single view because a join of byte
      views is a view.  That collapse is the same one that made [cobj]
      possible at all, applied at the address axis rather than the hart
      axis -- which is the evidence that indexing by context was the right
      move rather than a lucky one for the load case.

      TWO OUTPUTS, AND ONLY ONE OF THEM IS NEW.  [monPred_at R (view_scl T)]
      -- the frozen lock payload -- was ALREADY objective at layer A (it is
      an [iProp], and for a points-to it is literally [WeakPtPub.wpt_pub T])
      so it passes through untouched.  The floor token is the one that had
      to be built.  Keeping both, rather than folding the floor into the
      payload, is deliberate: they are consumed by different parties -- the
      payload by whoever opens the invariant, the floor by whoever needs to
      know the store landed, and a client wanting the original pure
      inequality back against its own authority gets it from
      [ctx_addrs_valid]. *)

  Lemma wwp_sd8_tor_rvc_o (ξ : CtxId) (pc : mword 64) (rs1 rs2 : mword 5)
      (imm : mword 12) (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rs2v : mword 64) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    wrunning ξ -∗
    cobj ξ (wpt8 ea (DfracOwn 1) vold) -∗
    cobj ξ R -∗
    ( ∀ T : nat,
      ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T) -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      wrunning ξ -∗
      cobj ξ (wpt8 ea (DfracOwn 1) rs2v) -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnz2 Hea Hram.
    iIntros "Hmm Hpcf Hpad Hpc Hrs1 Hrs2 #Hi [%ws [Hws Hauth]] Hpt HR Hcont".
    iDestruct (cobj_to_hold ξ ws with "Hauth Hpt") as "[Hauth Hpt]".
    iDestruct (cobj_to_hold ξ ws with "Hauth HR") as "[Hauth HR]".
    iApply (wwp_sd8_tor_rvc pc rs1 rs2 imm ea vold R q pmpcfg0 pmpaddrs
              rs1v rs2v ws Hgid Hpmp Htor Hnz1 Hnz2 Hea Hram
              with "Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hi Hws Hpt HR").
    iIntros (ws' T) "%Hle %HT Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hws Hpt HR".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iDestruct (ctx_addrs_get ξ _ (acc_addr ea) 8 T HT with "Hauth") as "#Hlb".
    iDestruct (cobj_of_hold ξ ws' with "Hauth Hpt") as "[Hauth Hpt]".
    iApply ("Hcont" $! T with "Hlb Hmm Hpcf Hpad Hpc Hrs1 Hrs2 [Hws Hauth] Hpt HR").
    iExists ws'. iFrame.
  Qed.

  Lemma wwp_sd8_tor_rvc_run (ξ : CtxId) (pc : mword 64) (rs1 rs2 : mword 5)
      (imm : mword 12) (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rs2v : mword 64) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    cobj ξ (wpt8 ea (DfracOwn 1) vold) -∗
    cobj ξ R -∗
    ( ∀ T : nat,
      ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T) -∗
      whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      cobj ξ (wpt8 ea (DfracOwn 1) rs2v) -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnz2 Hea Hram.
    iIntros "Hrun Hpcf Hpad Hpc Hrs1 Hrs2 #Hi Hpt HR Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_sd8_tor_rvc_o ξ pc rs1 rs2 imm ea vold R q pmpcfg0 pmpaddrs
              rs1v rs2v Hgid Hpmp Htor Hnz1 Hnz2 Hea Hram
              with "Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hi Hview Hpt HR").
    iIntros (T) "#Hlb Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hview Hpt HR".
    iApply ("Hcont" $! T with "Hlb [Hmm Hview] Hpcf Hpad Hpc Hrs1 Hrs2 Hpt HR").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 11. THE [start()] FAMILIES -- [WeakLeafM] §12 at this altitude, so
      that the whole M-mode boot cone can be written with no [wstate] in
      sight.

      Eleven of the fourteen ride [mmode_config] and get the ordinary pair.
      THE OTHER THREE GET AN [_o] AND NO [_run], for the same reason [mret]
      does not get one (§8): their leaves take the CELLS [mmode_config] is
      built from rather than the bundle -- because each reads or writes one
      of them -- so there is no bundle for the view token to ride in.  A
      caller opens [whart_run] at those three sites, which is one line each
      and is where the SC chain opens the bundle anyway. *)

  (** *** 11a. [c.and] *)
  Lemma wwp_and_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (and_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_and_rvc pc rs2 rs1 rd m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_and_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (and_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_and_rvc_o ξ pc rs2 rs1 rd m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11b. [c.srli] *)
  Lemma wwp_srli_rvc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_srli_rvc pc rs1 rd shamt m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_srli_rvc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_srli_rvc_o ξ pc rs1 rd shamt m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11c. [auipc] *)
  Lemma wwp_auipc_o (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hfile #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_auipc pc rd imm m pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hfile Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_auipc_run (ξ : CtxId) (pc : SailStdpp.Values.mword 64)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_auipc_o ξ pc rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11d. [c.sdsp] with no PMP region -- §10's release interface over
      the [pmp_all_off] leaf.  Same two outputs, same reasons. *)
  Lemma wwp_sd8_off_rvc_o (ξ : CtxId) (pc : mword 64) (rs1 rs2 : mword 5)
      (imm : mword 12) (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n) (rs1v rs2v : mword 64) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    wrunning ξ -∗
    cobj ξ (wpt8 ea (DfracOwn 1) vold) -∗
    cobj ξ R -∗
    ( ∀ T : nat,
      ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T) -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      wrunning ξ -∗
      cobj ξ (wpt8 ea (DfracOwn 1) rs2v) -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz1 Hnz2 Hea Hram.
    iIntros "Hmm Hpcf Hpc Hrs1 Hrs2 #Hi [%ws [Hws Hauth]] Hpt HR Hcont".
    iDestruct (cobj_to_hold ξ ws with "Hauth Hpt") as "[Hauth Hpt]".
    iDestruct (cobj_to_hold ξ ws with "Hauth HR") as "[Hauth HR]".
    iApply (wwp_sd8_off_rvc pc rs1 rs2 imm ea vold R q pmpcfg0
              rs1v rs2v ws Hgid Hpmp Hnz1 Hnz2 Hea Hram
              with "Hmm Hpcf Hpc Hrs1 Hrs2 Hi Hws Hpt HR").
    iIntros (ws' T) "%Hle %HT Hmm Hpcf Hpc Hrs1 Hrs2 Hws Hpt HR".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iDestruct (ctx_addrs_get ξ _ (acc_addr ea) 8 T HT with "Hauth") as "#Hlb".
    iDestruct (cobj_of_hold ξ ws' with "Hauth Hpt") as "[Hauth Hpt]".
    iApply ("Hcont" $! T with "Hlb Hmm Hpcf Hpc Hrs1 Hrs2 [Hws Hauth] Hpt HR").
    iExists ws'. iFrame.
  Qed.

  Lemma wwp_sd8_off_rvc_run (ξ : CtxId) (pc : mword 64) (rs1 rs2 : mword 5)
      (imm : mword 12) (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n) (rs1v rs2v : mword 64) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    cobj ξ (wpt8 ea (DfracOwn 1) vold) -∗
    cobj ξ R -∗
    ( ∀ T : nat,
      ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T) -∗
      whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      cobj ξ (wpt8 ea (DfracOwn 1) rs2v) -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz1 Hnz2 Hea Hram.
    iIntros "Hrun Hpcf Hpc Hrs1 Hrs2 #Hi Hpt HR Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_sd8_off_rvc_o ξ pc rs1 rs2 imm ea vold R q pmpcfg0
              rs1v rs2v Hgid Hpmp Hnz1 Hnz2 Hea Hram
              with "Hmm Hpcf Hpc Hrs1 Hrs2 Hi Hview Hpt HR").
    iIntros (T) "#Hlb Hmm Hpcf Hpc Hrs1 Hrs2 Hview Hpt HR".
    iApply ("Hcont" $! T with "Hlb [Hmm Hview] Hpcf Hpc Hrs1 Hrs2 Hpt HR").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11e. [csrr rd, sie] *)
  Lemma wwp_csrr_sie_o (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (lower_mie mie_in mideleg_in) -∗
      mie ↦ᵣ mie_in -∗
      mideleg ↦ᵣ mideleg_in -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hmie Hmdl Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_sie pc rd mie_in mideleg_in rd0 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hmie Hmdl Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hmie Hmdl Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrd Hmie Hmdl"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrr_sie_run (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx rd, CSRRS)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (lower_mie mie_in mideleg_in) -∗
      mie ↦ᵣ mie_in -∗
      mideleg ↦ᵣ mideleg_in -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hmie Hmdl Hrd #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrr_sie_o ξ pc rd mie_in mideleg_in rd0 pmpcfg0 q
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hmie Hmdl Hrd Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrd Hmie Hmdl Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrd Hmie Hmdl").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11f. [csrw mepc, rs1] *)
  Lemma wwp_csrw_mepc_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mepc0 : type_of_register mepc) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mepc, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mepc ↦ᵣ WpGprCsrwA.mepc_val rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_mepc pc rs1 mepc0 rs1v pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_mepc_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mepc0 : type_of_register mepc) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mepc, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mepc ↦ᵣ WpGprCsrwA.mepc_val rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_mepc_o ξ pc rs1 mepc0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11g. [csrw satp, rs1] *)
  Lemma wwp_csrw_satp_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (satp0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    satp ↦ᵣ satp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      satp ↦ᵣ WpGprCsrwB.satp_legalized satp0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_satp pc rs1 satp0 rs1v pmpcfg0 q ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_satp_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (satp0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    satp ↦ᵣ satp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      satp ↦ᵣ WpGprCsrwB.satp_legalized satp0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_satp_o ξ pc rs1 satp0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11h. [csrw medeleg, rs1] *)
  Lemma wwp_csrw_medeleg_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (medeleg0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    medeleg ↦ᵣ medeleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_medeleg, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_medeleg pc rs1 medeleg0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_medeleg_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (medeleg0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    medeleg ↦ᵣ medeleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_medeleg, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_medeleg_o ξ pc rs1 medeleg0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11i. [csrw mideleg, rs1] *)
  Lemma wwp_csrw_mideleg_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mideleg0 : type_of_register mideleg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mideleg ↦ᵣ mideleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mideleg ↦ᵣ WpGprCsrwB.mideleg_legalized mideleg0 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hcsr #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_mideleg pc rs1 mideleg0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hcsr"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_mideleg_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mideleg0 : type_of_register mideleg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mideleg ↦ᵣ mideleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mideleg ↦ᵣ WpGprCsrwB.mideleg_legalized mideleg0 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hcsr #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_mideleg_o ξ pc rs1 mideleg0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hcsr Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hcsr Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hcsr").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11j. [csrw sie, rs1] *)
  Lemma wwp_csrw_sie_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mie0 mdl0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mdl0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mie ↦ᵣ WpGprCsrwB.sie_new_mie mie0 mdl0 rs1v -∗
      mideleg ↦ᵣ mdl0 -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hmie Hmdl #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_sie pc rs1 mie0 mdl0 rs1v pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hmie Hmdl Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hmie Hmdl Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hmie Hmdl"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_sie_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (mie0 mdl0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mdl0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mie ↦ᵣ WpGprCsrwB.sie_new_mie mie0 mdl0 rs1v -∗
      mideleg ↦ᵣ mdl0 -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hmie Hmdl #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_sie_o ξ pc rs1 mie0 mdl0 rs1v pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hmie Hmdl Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hmie Hmdl Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hmie Hmdl").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11k. [csrw pmpaddr0, rs1] *)
  Lemma wwp_csrw_pmpaddr0_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (rs1v : mword 64) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      pmpaddr_n ↦ᵣ WpGprCsrwB.pmp0_newaddr pmpcfg0 pmpaddr00 rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf Hpc Hrs Hpad #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_pmpaddr0 pc rs1 rs1v pmpaddr00 pmpcfg0 q ws
              (⌜True⌝ : vProp Σ) Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hrs Hpad Hi Hws HF").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hpad Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hrs Hpad"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_csrw_pmpaddr0_run (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (rs1v : mword 64) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    ( whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      pmpaddr_n ↦ᵣ WpGprCsrwB.pmp0_newaddr pmpcfg0 pmpaddr00 rs1v -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hrs Hpad #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_csrw_pmpaddr0_o ξ pc rs1 rs1v pmpaddr00 pmpcfg0 q
              Hgid Hpmp Hnz with "Hmm Hpcf Hpc Hrs Hpad Hi Hview").
    iIntros "Hmm Hpcf Hpc Hrs Hpad Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hrs Hpad").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 11l-n. THE THREE CELL-BASED ONES -- [_o] only (header). *)

  (** [csrr rd, mstatus] *)
  Lemma wwp_csrr_mstatus_o (ξ : CtxId) (pc : mword 64) (rd : mword 5)
      (ms0 rd0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx rd, CSRRS)) -∗
    wrunning ξ -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ ms0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg ms0 -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrd #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrr_mstatus pc rd ms0 rd0 pmpcfg0 ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz HmIE Hmprv
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrd Hi Hws HF").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrd Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hhs Hpriv Hms Hpcf Hpc Hrd"). iExists ws'. iFrame.
  Qed.

  (** [csrw mstatus, rs1] *)
  Lemma wwp_csrw_mstatus_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (ms0 rs1v : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mstatus, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ WpGprCsrwCommon.mstatus_legalized ms0 rs1v -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal4 Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrs #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_mstatus pc rs1 ms0 rs1v pmpcfg0 ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hal4 Hnz HmIE Hmprv
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrs Hi Hws HF").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrs Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hhs Hpriv Hms Hpcf Hpc Hrs"). iExists ws'. iFrame.
  Qed.

  (** [csrw pmpcfg0, rs1] *)
  Lemma wwp_csrw_pmpcfg0_o (ξ : CtxId) (pc : mword 64) (rs1 : mword 5)
      (ms0 rs1v : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) -∗
    wrunning ξ -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ ms0 -∗
      pmpcfg_n ↦ᵣ WpGprCsrwC.pmpcfg_written rs1v pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      wrunning ξ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrs #Hi [%ws [Hws Hauth]] Hcont".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HF".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_csrw_pmpcfg0 pc rs1 ms0 rs1v pmpcfg0 ws (⌜True⌝ : vProp Σ)
              Hgid Hpmp Hnz HmIE Hmprv
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hrs Hi Hws HF").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrs Hws _".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Hauth") as "Hauth";
      [by apply ws_le_view|].
    iApply ("Hcont" with "Hhs Hpriv Hms Hpcf Hpc Hrs"). iExists ws'. iFrame.
  Qed.

End leafo.
