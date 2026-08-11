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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RegFile.
Require Import RiscvFetchExec InstrBytes WpGpr WpMmodeLeafBase.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakPtOwn WeakPtPub WeakObj WeakLeafM.

Section leafo.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (** ** 0. THE AMBIENT BUNDLE.

      [mmode_config] plus this hart's view token.  Non-fractional on
      purpose (see the header); the [q] is [mmode_config]'s and is threaded
      exactly as before. *)
  Definition whart_run (q : Qp) : iProp Σ :=
    (mmode_config (DfracOwn q) ∗ hart_view cpu_id)%I.

  Lemma whart_run_open q :
    whart_run q -∗ mmode_config (DfracOwn q) ∗ hart_view cpu_id.
  Proof. iIntros "$". Qed.

  Lemma whart_run_close q :
    mmode_config (DfracOwn q) -∗ hart_view cpu_id -∗ whart_run q.
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
  Lemma leaf_hide (Pre Post : iProp Σ) :
    (∀ ws : wstate,
        ⊢ Pre -∗ hart_ws cpu_id ws -∗
          (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ Post -∗ hart_ws cpu_id ws' -∗
             WWP Loop) -∗
          WWP Loop) ->
    Pre -∗ hart_view cpu_id -∗ (Post -∗ hart_view cpu_id -∗ WWP Loop) -∗
    WWP Loop.
  Proof.
    iIntros (Hleaf) "HPre [%ws [Hws Hauth]] Hcont".
    iApply (Hleaf ws with "HPre Hws").
    iIntros (ws') "%Hle HPost Hws".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "HPost"). iExists ws'. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The worked leaf.

      Compare with [WeakLeafM.wwp_lui]: no [ws] parameter, no [∀ ws'], no
      [⌜ws_le ws ws'⌝], no frame in or out, and [hart_view cpu_id] in place
      of [hart_ws cpu_id ws] / [hart_ws cpu_id ws'].

      SO THE CALL SITE IS [WpMmodeUtype.wp_lui_gpr]'S PLUS EXACTLY ONE
      NAME.  Against [WkStartNew]'s instruction 35 as it stands today:

        SC     iApply (wp_lui_gpr … with "Hmm HpcfA Hpc Hfile Hi35").
               iIntros "Hmm HpcfA Hpc Hfile".
        NOW    iApply (wwp_lui … ws34 _ … with "… Hi35 Hhws Hstk").
               iIntros (ws35) "%Hwsle35 Hmm HpcfA Hpc Hfile Hhws Hstk".
        HERE   iApply (wwp_lui_o … with "Hmm HpcfA Hpc Hfile Hi35 Hhws").
               iIntros "Hmm HpcfA Hpc Hfile Hhws".

      [ws34], [%Hwsle35] and [Hstk] are gone.  [Hhws] is NOT, and cannot be
      removed at this altitude: it is the client half of an exclusive
      [ghost_var], so it has to be passed to whoever updates it.  Deleting
      it means moving the whole cell into [wmstate_interp] — see the
      worklist entry "the last name". *)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      hart_view cpu_id -∗
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
      left is the lemma's name and that [Hmm] is bound to [whart_run q]
      rather than [mmode_config (DfracOwn q)]. *)
  Lemma wwp_lui_run (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    ( whart_run q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hrun Hpcf Hpc Hfile #Hi Hcont".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iApply (wwp_lui_o pc is_rvc rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. [addi], both wrappers.

      Included to fix the TEMPLATE, since the remaining sweep is this pair
      per instruction and nothing else.  Neither proof does anything
      instruction-specific: [_o] is [hart_view_open] / [ws_update] /
      [hart_view_close] around the [winstr_m] leaf, and [_run] is
      [whart_run_open] / [whart_run_close] around [_o]. *)
  Lemma wwp_addi_o (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_addi_run (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( whart_run q -∗
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
    iApply (wwp_addi_o pc is_rvc rs1 rd imm m pmpcfg0 q Hgid Hpmp Hnz
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
  Lemma wwp_or_rvc_o (pc : SailStdpp.Values.mword 64)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_or_rvc_run (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( whart_run q -∗
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
    iApply (wwp_or_rvc_o pc rs2 rs1 rd m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5b. [c.add] / [c.mv] *)
  Lemma wwp_add_rvc_o (pc : SailStdpp.Values.mword 64)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_add_rvc_run (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( whart_run q -∗
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
    iApply (wwp_add_rvc_o pc rs2 rs1 rd m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5c. [c.slli] *)
  Lemma wwp_slli_rvc_o (pc : SailStdpp.Values.mword 64)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_slli_rvc_run (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( whart_run q -∗
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
    iApply (wwp_slli_rvc_o pc rs1 rd shamt m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5d. [c.addiw] *)
  Lemma wwp_addiw_rvc_o (pc : SailStdpp.Values.mword 64)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (sign_extend' 64
                    (subrange_vec_dec
                       (add_vec (m !!! Regidx rs1)
                          (sign_extend' 64 immv)) 31 0))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_addiw_rvc_run (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (immv : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    ( whart_run q -∗
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
    iApply (wwp_addiw_rvc_o pc rs1 rd immv m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

  (** *** 5e. [ori] -- the uncompressed one, so the bump is 4. *)
  Lemma wwp_ori_o (pc : SailStdpp.Values.mword 64)
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
    hart_view cpu_id -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      hart_view cpu_id -∗
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
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iApply ("Hcont" with "Hmm Hpcf Hpc Hfile"). iExists ws'. iFrame.
  Qed.

  Lemma wwp_ori_run (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    whart_run q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( whart_run q -∗
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
    iApply (wwp_ori_o pc rs1 rd imm m pmpcfg0 q Hgid Hpmp Hnz
              with "Hmm Hpcf Hpc Hfile Hi Hview").
    iIntros "Hmm Hpcf Hpc Hfile Hview".
    iApply ("Hcont" with "[Hmm Hview] Hpcf Hpc Hfile").
    iApply (whart_run_close with "Hmm Hview").
  Qed.

End leafo.
