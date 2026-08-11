(** * WeakSmodeFrame.v — DOES THE FRAMING STORY SURVIVE HART MIGRATION?

    THE EXPERIMENT.  [WeakCtx] claims that indexing objective ownership by an
    execution CONTEXT rather than by a hart makes it survive [WpNext.wp_next]
    -- the S-mode step continuation that quantifies the resuming hart -- with
    no plumbing, by the ordinary Iris frame rule.  A claim of that shape is
    worth exactly nothing until a function is proved on top of leaves stated
    that way, so this file states three S-mode leaves in [wp_next] form and
    proves a three-instruction function over them while carrying a frame that
    NO LEAF MENTIONS.

    THE LEAVES ARE HYPOTHESES, NOT AXIOMS.  The weak port is M-mode only; the
    S-mode weak funnel (privilege, trap delegation, the [sstatus] discipline)
    does not exist yet, so these leaves cannot be proved here.  They are
    therefore stated as [Prop]s and taken as SECTION HYPOTHESES of the
    function proof, which makes the function a real theorem -- "given leaves
    of this shape, this proof goes through and this frame survives" -- and
    adds nothing to the trusted base.  [proof_coverage] and [lemma_diff] stay
    clean, and that is the point: the experiment tests the INTERFACE, and the
    interface is the thing in question.

    WHAT IS BEING MEASURED.  Read [wwp_bump]'s statement and count what the
    caller must say.  The two cells the instructions touch are named, because
    a load's postcondition names what it read; the frame [F] is an arbitrary
    [vProp] and is named exactly twice -- once in, once out -- with no leaf,
    no premise and no side condition mentioning it in between.  Read the
    proof and count what it does to [F]: nothing.  It is introduced once and
    passed to the continuation at the end, having crossed three [wp_next]
    binders untouched.

    THE CONTROL.  §5 states the same frame indexed by [CpuId] -- the current
    [WeakObj.wobj] -- and shows it does NOT typecheck in the continuation,
    which is the whole reason this file exists. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RegFile WpGpr InstrBytes.
Require Import WpNext.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakWord8 WeakCtx WeakPtOwn WeakObj.
Require Import WeakFunnel WeakLeafM.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The ambient S-mode bundle.

    In the real port this is [IntrDefs.sie_cap_gpr] -- which already bundles
    [sconf] -- PLUS one conjunct, exactly as the earlier design decision put
    it: [sconf] is where the view token belongs in S-mode.  Here it is cut
    down to the two parts the experiment turns on, because the S-mode CSR
    content is irrelevant to framing and dragging it in would only obscure
    which conjunct does the work.

    THE SHAPE IS THE POINT.  [CpuId] is an implicit INSTANCE argument, so
    inside [wp_next]'s binder [wsrun] elaborates at the RESUMING hart and its
    [hart_ws] follows automatically.  [ξ] is an EXPLICIT argument, so it does
    not. *)
Section bundle.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wsrun `{CID : CpuId} (ξ : CtxId) (m : regfile) : iProp Σ :=
    (gpr_file m ∗ wrunning ξ)%I.

  Lemma wsrun_open `{CID : CpuId} ξ m :
    wsrun ξ m -∗ gpr_file m ∗ ∃ ws, hart_ws cpu_id ws ∗ ctx_auth ξ (ws_view ws).
  Proof. iIntros "[$ H]". iApply (wrunning_open with "H"). Qed.

  Lemma wsrun_close `{CID : CpuId} ξ m ws :
    gpr_file m -∗ hart_ws cpu_id ws -∗ ctx_auth ξ (ws_view ws) -∗ wsrun ξ m.
  Proof. iIntros "H1 H2 H3". iFrame "H1". iApply (wrunning_close with "H2 H3"). Qed.

End bundle.

(* ====================================================================== *)
(** ** 2. Three S-mode leaves, in [wp_next] form.

    Compare each with its M-mode twin in [WeakLeafM]:

      M-mode  ... -∗ hart_ws cpu_id ws -∗ vwp_hold F ws -∗
              (∀ ws', ⌜ws_le ws ws'⌝ -∗ ... -∗ hart_ws cpu_id ws' -∗
                      vwp_hold F ws' -∗ WWP Loop) -∗ WWP Loop

      S-mode  ... -∗ wsrun ξ m -∗ cobj ξ R -∗
              wp_next b p (fun CID => ... -∗ wsrun ξ m' -∗ cobj ξ R -∗
                                      WWP Loop) -∗ WWP Loop

    TWO THINGS CHANGED AND BOTH ARE FORCED.

    (1) [hart_ws cpu_id ws] and the [∀ ws' ⌜ws_le⌝] pair became [wsrun ξ m].
    That is not cosmetic packaging: [ws'] is the RESUMING hart's wstate, and
    [ws_le ws ws'] is FALSE across a migration (see [WeakCtx]'s header --
    hart B's [w_vrOld] need not dominate hart A's).  A migrating leaf cannot
    state its effect as a relation between two harts' wstates at all, so the
    monotonicity has to be internal to the context, which is what
    [wrunning_step] and [wrunning_resume] do.

    (2) [vwp_hold F ws] became [cobj ξ R].  [vwp_hold F ws] names a wstate
    and so cannot even be WRITTEN in the continuation -- there is no [ws]
    there.  [cobj ξ R] names neither a hart nor a wstate, so it is spelled
    identically on both sides of the binder, which is what lets it frame. *)

Section leaf_specs.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId}.

  (** [ld rd, imm(rs1)] — 8 bytes, from a cell the context owns. *)
  Definition wsld8_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64) (cmp : bool)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (m : regfile)
      (ea : Arch.pa) (v : mword 64) (dq : dfrac),
    uint rd <> 0 ->
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = ea ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
        cobj ξ (wpt8 ea dq v) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ (<[Regidx rd := regval_into_reg v]> m) -∗
          pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
          cobj ξ (wpt8 ea dq v) -∗
          WWP Loop) -∗
        WWP Loop ).

  (** [addi rd, rs1, imm] — register-only, so it touches no [cobj] at all. *)
  Definition wsaddi_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64) (cmp : bool)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (m : regfile),
    uint rd <> 0 ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc cmp (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ (<[Regidx rd :=
                     regval_into_reg (add_vec (m !!! Regidx rs1)
                                        (sign_extend' 64 imm))]> m) -∗
          pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
          WWP Loop) -∗
        WWP Loop ).

  (** [sd rs2, imm(rs1)] — 8 bytes, into a cell the context owns
      EXCLUSIVELY.  Note there is no released timestamp here and there
      should not be: [T] is what a PUBLISHING store owes a lock invariant.
      A store to your own cell publishes nothing, so it is objective in and
      objective out, and that is why it fits the [wp_next] shape unchanged
      while [WeakLeafM.wwp_sd8_tor_rvc] does not. *)
  Definition wssd8_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64) (cmp : bool)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile)
      (ea : Arch.pa) (vold : mword 64),
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = ea ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
        cobj ξ (wpt8 ea (DfracOwn 1) vold) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ m -∗
          pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
          cobj ξ (wpt8 ea (DfracOwn 1) (m !!! Regidx rs2)) -∗
          WWP Loop) -∗
        WWP Loop ).

End leaf_specs.

(* ====================================================================== *)
(** ** 3. THE FUNCTION.

      ld   rV, immX(rX)      ; rV := *X
      addi rV, rV, immI
      sd   rV, immY(rY)      ; *Y := rV

    Three instructions, three [wp_next] crossings, at a GENERIC [b] -- so
    every one of them may migrate, and the proof is not allowed to assume
    otherwise.

    The caller holds three objective resources.  Two of them, the cells at
    [X] and [Y], are named because the instructions touch them.  The third,
    [F], is an ARBITRARY [vProp Σ] -- a page, a file table, a [big_sepL] over
    a list, anything -- and is the thing under test. *)

Section framing.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  (* the leaves, as hypotheses *)
  Context (Hld : wsld8_spec) (Hadd : wsaddi_spec) (Hsd : wssd8_spec).

  Lemma wwp_bump (ξ : CtxId) (F : vProp Σ)
      (b : bool) (p : mword 64) (pc : mword 64) (m : regfile)
      (rV rX rY : mword 5) (immX immI immY : mword 12)
      (eaX eaY : Arch.pa) (vX vY : mword 64) (dqX : dfrac)
      (m1 m2 : regfile) :
    uint rV <> 0 ->
    uint rX <> 0 ->
    uint rY <> 0 ->
    m1 = <[Regidx rV := regval_into_reg vX]> m ->
    m2 = <[Regidx rV :=
           regval_into_reg (add_vec (m1 !!! Regidx rV)
                              (sign_extend' 64 immI))]> m1 ->
    add_vec (m  !!! Regidx rX) (sign_extend' 64 immX) = eaX ->
    add_vec (m2 !!! Regidx rY) (sign_extend' 64 immY) = eaY ->
    wsrun ξ m -∗
    pc_is pc -∗
    winstr_m pc false (LOAD (immX, Regidx rX, Regidx rV, false, 8)) -∗
    winstr_m (add_vec_int pc 4) false
      (ITYPE (immI, Regidx rV, Regidx rV, ADDI)) -∗
    winstr_m (add_vec_int (add_vec_int pc 4) 4) false
      (STORE (immY, Regidx rV, Regidx rY, 8)) -∗
    cobj ξ (wpt8 eaX dqX vX) -∗
    cobj ξ (wpt8 eaY (DfracOwn 1) vY) -∗
    cobj ξ F -∗
    wp_next b p (fun CID : CpuId =>
      wsrun ξ m2 -∗
      pc_is (add_vec_int (add_vec_int (add_vec_int pc 4) 4) 4) -∗
      cobj ξ (wpt8 eaX dqX vX) -∗
      cobj ξ (wpt8 eaY (DfracOwn 1) (m2 !!! Regidx rV)) -∗
      cobj ξ F -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros HnzV HnzX HnzY Hm1 Hm2 HeaX HeaY. subst m1 m2.
    iIntros "Hrun Hpc #Hi0 #Hi1 #Hi2 HX HY HF Hcont".

    (* ---- 1. the load.  [HY] and [HF] are simply not mentioned. ---- *)
    iApply (Hld CID0 ξ b p false pc rV rX immX m eaX vX dqX HnzV HeaX
              with "Hrun Hpc Hi0 HX").
    iIntros (CID1) "%Hpin1 Hrun Hpc HX".

    (* We are now on hart [CID1], which need not be [CID0].  [HY] and [HF]
       are still in the Iris context, spelled exactly as they were, because
       [cobj] mentions [ξ] and not the hart.  Nothing was done to them. *)

    (* ---- 2. the register-only step.  Touches no memory at all. ---- *)
    iApply (Hadd CID1 ξ b p false (add_vec_int pc 4) rV rV immI
              (<[Regidx rV := regval_into_reg vX]> m) HnzV
              with "Hrun Hpc Hi1").
    iIntros (CID2) "%Hpin2 Hrun Hpc".

    (* ---- 3. the store. ---- *)
    iApply (Hsd CID2 ξ b p false (add_vec_int (add_vec_int pc 4) 4) rV rY immY
              _ eaY vY HnzY HnzV HeaY with "Hrun Hpc Hi2 HY").
    iIntros (CID3) "%Hpin3 Hrun Hpc HY".

    (* ---- discharge our own [wp_next] at whatever hart we ended on. ---- *)
    iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" with "Hrun Hpc HX HY HF").
  Qed.

End framing.

(* ====================================================================== *)
(** ** 4. WHAT THE PROOF SHOWS, read off the text above.

    THE FRAME.  [HF] appears in the proof script exactly twice: in the
    opening [iIntros] and in the closing [iApply].  It crosses three
    [wp_next] binders and is never passed to a leaf, never converted, never
    weakened, never mentioned in a side condition.  That is the ordinary
    Iris frame rule doing its job, which is only possible because
    [cobj ξ F] is the SAME PROPOSITION inside and outside the binder.

    WHAT HAD TO GO IN.  Exactly two kinds of thing:

      - [wsrun ξ m], the ambient bundle.  It must go in because the leaf
        steps the machine: it needs [hart_ws] to do that and
        [ctx_auth ξ] to move the context's floor up with it
        ([WeakCtx.wrunning_step]).  It comes back at the RESUMING hart,
        which is why it is written inside the binder and not outside.
      - [cobj ξ (wpt8 eaX ...)] and [cobj ξ (wpt8 eaY ...)], the cells the
        instructions actually touch.  A load's postcondition names what it
        read, so its cell cannot be framed; that is not a weak-memory cost,
        it is the same in SC.

    Everything else frames.  Note in particular that the frame is an
    ARBITRARY [vProp], not a list of points-tos: nothing in the proof
    decomposes it, so a file-descriptor table or a [big_sepL] over a list
    costs exactly what [F] costs here, which is nothing.

    THE PRECEDENT IS ALREADY IN THE TREE.  The SC side has
    [CpuOwn.cpu_own_transport], applied as
    [ltac:(wp_next_chain)] at every migration point, because [cpu_own] is
    genuinely per-hart (it owns [cpus[cid]]'s fields) and therefore DOES
    have to be transported.  That is the correct treatment for a hart
    resource.  The whole content of [WeakCtx] is that objective memory
    ownership is NOT a hart resource and must not be made to look like one.

    THE ONE THING THIS DOES NOT SHOW.  The leaves are hypotheses, so this
    says nothing about whether an S-mode weak leaf of this shape is
    PROVABLE.  The load and the register step look routine.  The store is
    the one to watch: [wssd8_spec] is stated for a cell the context owns
    exclusively, and deliberately carries no released timestamp, so it says
    nothing about publishing.  A [c.sd] that publishes into a lock invariant
    still owes the [T] that [WeakLeafM.wwp_sd8_tor_rvc] hands back, and that
    interface is still the open question recorded in the worklist. *)

(* ====================================================================== *)
(** ** 5. THE CONTROL, MACHINE-CHECKED.

    The argument above turns entirely on one claim about ELABORATION, so it
    is checked here rather than asserted.  [wobj]'s hart is an implicit
    INSTANCE argument ([Arguments wobj {Σ weakGS0 CID} R]), so it is resolved
    from whatever [CpuId] is innermost -- and inside [wp_next]'s binder that
    is the RESUMING hart.  [cobj]'s context is an explicit argument
    ([Arguments cobj {Σ weakViewG0} ξ R]) and cannot be captured. *)

Section control.
  Context `{!weakGS Σ} `{GEN : GenId} `{CID0 : CpuId}.
  Variables (F : vProp Σ) (b : bool) (p : mword 64) (ξ : CtxId).

  (** A. Under the binder, [wobj F] means the RESUMING hart's [wobj]. *)
  Lemma wobj_rebinds :
    wp_next b p (fun CID : CpuId => wobj F)
  = wp_next b p (fun CID : CpuId => @wobj _ _ CID F).
  Proof. reflexivity. Qed.

  (** B. So it is NOT the frame the caller is holding, which is at [CID0].
      This is the failure: the caller's [wobj F] and the one the
      continuation demands are different propositions, and the only bridge
      between them -- [WeakObj.wobj_handoff] -- needs BOTH harts'
      authorities in one step, which is precisely what migrating denies. *)
  Lemma wobj_not_the_callers_frame :
    wp_next b p (fun CID : CpuId => wobj F)
  <> wp_next b p (fun _ : CpuId => @wobj _ _ CID0 F).
  Proof. Fail reflexivity. Abort.

  (** C. [cobj ξ F] is literally the same term on both sides of the binder,
      which is all the Iris frame rule ever needed. *)
  Lemma cobj_survives :
    wp_next b p (fun CID : CpuId => cobj ξ F)
  = wp_next b p (fun _ : CpuId => cobj ξ F).
  Proof. reflexivity. Qed.

End control.
