(** * WkTimerinit.v -- the weak-memory twin of [WpTimerinit.wp_timerinit]:
    xv6's [timerinit()] (21 instructions, KernelInstrs indices 9..29) as ONE
    [WWP] theorem, composed entirely from the SC-SHAPED leaves --
    [WeakLeafO]'s [_run] wrappers over [WkTimerinitAux]'s per-instruction
    [winstr_m] tokens.

    THIS IS THE FILE THAT DEMONSTRATES STEP-SITE PARITY.  Every instruction
    below is TWO proofmode lines -- one [iApply] naming the wrapper, one
    [iIntros] naming the resources back -- plus whatever register-map
    bookkeeping its SC twin also does.  What is gone relative to the
    hoisted-leaf version of this file (claude-notes/projects/weak-memory.md,
    "the sweep"):

      - the per-instruction DECODE PREAMBLE (~15 lines each): alignment,
        [acc_wf], the RAM window, the byte window, [goodb0]/[exec] at
        [dstateM], the ∀-state [Hdecf] and the expansion.  All of it is now
        [WkTimerinitAux.wsti_NN], spent as one [iPoseProof];
      - the [wstate] THREADING: no [ws] binder, no [∀ ws'], no
        [⌜ws_le ws ws'⌝], no [vwp_hold_mono] bump per carried word, and no
        transitivity chain at the joins.  The hart's view rides inside
        [WeakLeafO.whart_run ξ q] -- the slot [mmode_config] occupied -- and
        the frame is OBJECTIVE ([WeakCtx.cobj ξ]), so it simply stays in the
        Iris context across a step, exactly as an SC caller's resources do.

    Statement = [WpTimerinit.wp_timerinit] under the porting-table swaps
    (claude-notes/projects/weak-memory-porting.md):
      - [kernel_text]        -> [WeakInstr.wkernel_text kbs] + [wkb_covers kbs]
        (the [WkEntryEff] seam, reused verbatim);
      - [mmode_config (DfracOwn q)] -> [WeakLeafO.whart_run ξ q];
      - [stack_own_phys sp0 n] (built from [↦ₚ₈])
                              -> [cobj ξ (WkStackOwn.wstack_own_phys sp0 n)];
      - [WP (Loop : expr riscv_lang) {{ Φ }}] -> [WWP Loop] (no postcondition
        tree-wide);
      - everything else (the [pmpcfg_n]/[pmpaddr_n] fractional config,
        [pc_is], [gpr_file], the CSR cells, the [ti_*]/[m_*] definitional
        vocabulary) is REUSED UNCHANGED from [CodeTimerinitAux] /
        [WpTimerinit] -- never restated.

    The continuation binds only [tv] (the [csrr time] read): no [ws'], and
    no [ws_le] fact, because the caller never learns which [wstate] the
    function ended at.

    One wrapper per instruction:

      9,12,14,28  c.addi/c.addi4spn/c.li/c.addi (ADDI, RVC)  -> WeakLeafO.wwp_addi_run
      23          addi (F_Base)                              -> WeakLeafO.wwp_addi_run
      19          ori  (F_Base)                              -> WeakLeafO.wwp_ori_run
      22          lui  (F_Base)                              -> WeakLeafO.wwp_lui_run
      15          c.slli (RVC)                               -> WeakLeafO.wwp_slli_rvc_run
      16          c.or   (RVC)                               -> WeakLeafO.wwp_or_rvc_run
      24          c.add  (RVC)                               -> WeakLeafO.wwp_add_rvc_run
      13          csrr a5,menvcfg                            -> WeakLeafO.wwp_csrr_menvcfg_run
      18          csrr a5,mcounteren                         -> WeakLeafO.wwp_csrr_mcounteren_run
      21          csrr a5,time                               -> WeakLeafO.wwp_csrr_time_run
      17          csrw menvcfg,a5                            -> WeakLeafO.wwp_csrw_menvcfg_run
      20          csrw mcounteren,a5                         -> WeakLeafO.wwp_csrw_mcounteren_run
      25          csrw stimecmp,a5                           -> WeakLeafO.wwp_csrw_stimecmp_run
      10,11       c.sdsp ra/s0 (WRITTEN TOR entry)           -> WeakLeafO.wwp_sd8_tor_rvc_run
      26,27       c.ldsp ra/s0 (WRITTEN TOR entry)           -> WeakLeafO.wwp_ld8_tor_rvc_run
      29          c.ret                                      -> WeakLeafO.wwp_cjr_rvc_run

    THE TWO STACK SLOTS ARE THE ONE PLACE WEAK MEMORY IS VISIBLE, and only
    at the stores.  [wwp_sd8_tor_rvc_run] is the RELEASE store: besides the
    updated [cobj ξ (wpt8 ...)] it hands back a timestamp [T], the objective
    floor [ctx_view_lb ξ (view_addrs (acc_addr ea) 8 T)] saying the store
    landed, and the frozen payload [monPred_at R (view_scl T)].  A private
    stack slot publishes nothing, so this chain instantiates [R := ⌜True⌝]
    and drops both outputs -- the interface is there for a lock release,
    which is what will consume it.

    The two [c.sdsp]/[c.ldsp] pairs are CELL-based (two GPR cells: the base
    [sp] plus the data/destination register), extracted from the whole
    [gpr_file] via [WkGprAcc.gpr_file_acc_2] and folded back after; every
    other instruction is FILE-based (the same [gpr_file] threaded through,
    exactly as [WpTimerinit.v] does). *)
From Stdlib Require Import ZArith.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr.
Require Import WpMmodeShiftiop WpMmodeLeafBase WpMmodeUtype WpMmodeItype WpMmodeRtype
  WpMmodeJalr WpMmodeLoad WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import InstrBytes.
Require Import KernelText.
Require Import StackOwn.
Require Import RegFile.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import CodeTimerinitAux.
Require Import WpTimerinit.
(* -- weak machinery -- *)
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import MinstretInv.
Require Import WeakLeafWin WeakLeafRegOnly.
Require Import WeakLeafEff8 WeakLeafLd8 WeakLeafSd8.
Require Import WeakPmpTorEff WeakLeafTor.
Require Import WeakLeafItype WeakLeafUtypeShift WeakLeafRtypeW WeakLeafJump.
Require Import WeakLeafCsrrM WeakLeafCsrrTime WeakLeafCsrw2 WeakLeafStimecmp.
Require Import WeakLeafM.
Require Import WeakViewMono WeakCtx WeakPtPub WeakLeafO.
Require Import WkStackOwn WkGprAcc.
Require Import WkEntryEff.
Require Import WkTimerinitAux.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* concrete-register-key disequality (both keys literal) -- [WpTimerinit]'s
   [ti_reg_neq]/[ti_look]/[ti_unfold], which are [Local] there and so must be
   re-declared here. *)
Local Ltac ti_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

Local Ltac ti_look :=
  repeat first [ rewrite upd_eq
               | rewrite upd_ne; [ | ti_reg_neq ] ];
  first [ reflexivity | assumption ].

(* [WpDecodeBridge.decode_bridge_ms_bv]'s closing recipe: a bare
   [vm_compute; reflexivity] can fail on a decoded AST whose bitvector leaves
   carry a DIFFERENT (but propositionally equal) well-formedness proof term
   than the hand-written literal's; [bv_eq] closes exactly that gap. Safe as
   a drop-in for every plain [vm_compute; reflexivity] below. *)
Local Ltac vm_refl :=
  vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].

Local Ltac ti_unfold :=
  unfold ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

(* Reinserting the SAME two (unchanged) values a [c.sdsp]/[c.ldsp]-class
   store leaves in its two cells is a no-op on the underlying [regfile]
   function -- needed to fold [WkGprAcc.gpr_file_acc_2]'s reinsertion back
   into the canonical [ti_m*] name after a store (which does not otherwise
   touch the file at all). *)
Local Lemma regfile_upd2_id (f : regfile) (i j : regidx) :
  i <> j -> <[i := f !!! i]> (<[j := f !!! j]> f) = f.
Proof.
  intro Hij. apply functional_extensionality; intro k.
  unfold insert, regfile_insert, rf_upd, lookup_total, regfile_lookup_total.
  destruct (bool_decide (k = i)) eqn:Eki.
  - apply bool_decide_eq_true in Eki. subst. reflexivity.
  - destruct (bool_decide (k = j)) eqn:Ekj.
    + apply bool_decide_eq_true in Ekj. subst. reflexivity.
    + reflexivity.
Qed.

(* the same, at the ALREADY-KNOWN values [vi]/[vj] the store leaf hands back
   -- avoids re-normalising [vi]/[vj] into [f !!! i]/[f !!! j] form at the
   call site. *)
Local Lemma regfile_upd2_id' (f : regfile) (i j : regidx) (vi vj : mword 64) :
  i <> j -> f !!! i = vi -> f !!! j = vj -> <[i := vi]> (<[j := vj]> f) = f.
Proof. intros Hij <- <-. exact (regfile_upd2_id f i j Hij). Qed.

(* The [c.ldsp]-class store: the SP cell round-trips unchanged through
   [WkGprAcc.gpr_file_acc_2] but the DESTINATION cell genuinely changes (the
   loaded value), so — unlike [regfile_upd2_id] — only the OUTER (sp) insert
   collapses; the inner one must survive so the result matches the SC file's
   [ti_m26]/[ti_m27] naming ([<[rd := v]> (ti_m24 ...)], no [sp] insert at
   all, since the SC leaf is FILE-based and never re-touches [sp]). *)
Local Lemma regfile_upd_drop_outer (f : regfile) (i j : regidx) (vj : mword 64) :
  i <> j -> <[i := f !!! i]> (<[j := vj]> f) = <[j := vj]> f.
Proof.
  intro Hij. apply functional_extensionality; intro k.
  unfold insert, regfile_insert, rf_upd, lookup_total, regfile_lookup_total.
  destruct (bool_decide (k = i)) eqn:Eki.
  - apply bool_decide_eq_true in Eki. subst.
    rewrite (bool_decide_eq_false_2 (i = j) Hij). reflexivity.
  - reflexivity.
Qed.

Local Lemma regfile_upd_drop_outer' (f : regfile) (i j : regidx) (vi vj : mword 64) :
  i <> j -> f !!! i = vi -> <[i := vi]> (<[j := vj]> f) = <[j := vj]> f.
Proof. intros Hij <-. exact (regfile_upd_drop_outer f i j vj Hij). Qed.

Section wk_gpr_reinsert.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [WpGpr.gpr_file_insert_acc] specialised to a value chosen AT EXTRACTION
     TIME; [csrr time]'s destination value ([tv]) is not known until the
     [wwp_csrr_time_run] application returns it, so the wand must stay
     universally quantified over the eventual value -- exactly what
     [big_sepM_insert_acc] already hands back before [gpr_file_insert_acc]
     specialises it. *)
  Lemma gpr_file_reinsert_acc (f : regfile) (i : regidx) :
    gpr_file f ⊢ gpr_pt i (f i) ∗ (∀ w : mword 64, gpr_pt i w -∗ gpr_file (<[i := w]> f)).
  Proof.
    unfold gpr_file. iIntros "[_ Hm]".
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup f i) with "Hm") as "[$ Hcl]".
    iIntros (w) "Hpt". iSplitR; [iApply gpr_file_dom |].
    rewrite rf_to_gmap_upd. iApply ("Hcl" with "Hpt").
  Qed.

End wk_gpr_reinsert.

Section WkTimerinitThm.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [WkStackOwn.wstack_own_phys_2_intro] as a single [∗]-shaped entailment,
     so it composes with [WeakCtx.cobj_mono] at the final re-bundling. *)
  Local Lemma stack_2_intro_ent (sp : Arch.pa) (w1 w2 : bv 64) :
    (wpt8 (pa_stk sp 1) (DfracOwn 1) w1 ∗ wpt8 (pa_stk sp 2) (DfracOwn 1) w2)
    ⊢ wstack_own_phys sp 2.
  Proof. iIntros "[H1 H2]". iApply (wstack_own_phys_2_intro with "H1 H2"). Qed.

  (* [WkTimerinit.wwp_timerinit]: the whole-function spec, same statement as
     [WpTimerinit.wp_timerinit] under the porting-table swaps. *)
  Lemma wwp_timerinit (ξ : CtxId) (q : Qp)
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (menv0 stimecmp0 : mword 64) (mcen0 : mword 32)
      (pmpcfg1 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (n : nat) (kbs : _) :
    (2 ≤ n)%nat ->
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg1 ->
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_ra sp0) 8 ->
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_s0 sp0) 8 ->
    wkb_covers kbs ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx ti_ra = ra0 ->
    m !!! Regidx ti_s0 = s00 ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_ra sp0) j)) ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_s0 sp0) j)) ->
    whart_run ξ q -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is ti_pc9 -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menv0 -∗
    mcounteren ↦ᵣ mcen0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    cobj ξ (wstack_own_phys sp0 n) -∗
    wkernel_text kbs -∗
    ( ∀ tv : mword 64,
      whart_run ξ q -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (ret_pc ra0) -∗
      gpr_file (ti_mout m sp0 menv0 mcen0 tv ra0 s00) -∗
      menvcfg ↦ᵣ menvcfg_legalized menv0 (ti_menv1 menv0) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcen0 (ti_mcen1 mcen0) -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
      cobj ξ (wstack_own_phys sp0 n) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hn2 Hgid Hpmp Htor_ra Htor_s0 Hcov Hsp Hra Hs0 Hram_ra Hram_s0.
    iIntros "Hrun Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hstc Hstk #Htext Hcont".
    (* ---- split off the top two stack slots, OBJECTIVELY ---- *)
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_1 sp0 2 n Hn2)
                 with "Hstk") as "Hstk".
    iEval (rewrite cobj_sep) in "Hstk". iDestruct "Hstk" as "[Htop Hdeep]".
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_2_elim sp0) with "Htop") as "Htop".
    iEval (rewrite cobj_exist) in "Htop". iDestruct "Htop" as (vold_ra) "Htop".
    iEval (rewrite cobj_exist) in "Htop". iDestruct "Htop" as (vold_s0) "Htop".
    iEval (rewrite cobj_sep) in "Htop". iDestruct "Htop" as "[Hstkra Hstks0]".
    assert (Hpra : ti_ea_ra sp0 = pa_stk sp0 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hps0 : ti_ea_s0 sp0 = pa_stk sp0 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpra) in "Hstkra". iEval (rewrite -Hps0) in "Hstks0".
    (* the release stores' payload: a private stack slot publishes nothing *)
    iAssert (cobj ξ (⌜True⌝ : vProp Σ)) as "HRtrue".
    { rewrite cobj_pure. done. }
    (* register-nonzero side conditions *)
    assert (Hnz_sp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hnz_ra : uint ti_ra <> 0) by (vm_compute; discriminate).
    assert (Hnz_s0 : uint ti_s0 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a4 : uint ti_a4 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a5 : uint ti_a5 <> 0) by (vm_compute; discriminate).
    (* closed-value bridges (pure math, reused verbatim from [WpTimerinit]) *)
    assert (Hb63 : shift_bits_left (cli_wval i14)
                     (subrange_vec_dec sh15 (Z.sub log2_xlen 1) 0) = ti_bit63)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hival : add_vec (luival i22) (sign_extend' 64 i23) = ti_interval)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof (ti_sp_restore sp0) as Hspres.

    (* ==================================================================== *)
    (* ---- 9. c.addi sp, -16 ---- *)
    iPoseProof (wsti_9 kbs Hcov with "Htext") as "#Hi9".
    iApply (wwp_addi_run ξ ti_pc9 true csp_rs1 csp_rs1 (sign_extend' 12 i9) m
              pmpcfg1 q Hgid Hpmp Hnz_sp with "Hrun Hpmpc Hpc Hfile Hi9").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite sext6_12_64) in "Hfile".
    iEval (rewrite Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (ti_m1 m sp0)) in "Hfile".
    assert (P0 : add_vec_int ti_pc9 2 = ti_pc10) by vm_refl.
    iEval (rewrite P0) in "Hpc".

    (* ==================================================================== *)
    (* ---- 10. c.sdsp ra, 8(sp)  (WRITTEN TOR entry; RELEASE store) ---- *)
    assert (Lsp1 : ti_m1 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0) by (ti_unfold; ti_look).
    assert (Lra1 : ti_m1 m sp0 !!! Regidx ti_ra = ra0) by (ti_unfold; ti_look).
    assert (Ls01 : ti_m1 m sp0 !!! Regidx ti_s0 = s00) by (ti_unfold; ti_look).
    iPoseProof (wsti_10 kbs Hcov with "Htext") as "#Hi10".
    iDestruct (gpr_file_acc_2 (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hrac & Hfacc10)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m1 m sp0) (Regidx csp_rs1)) Lsp1) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra) -(rf_lookup (ti_m1 m sp0) (Regidx ti_ra)) Lra1) in "Hrac".
    iApply (wwp_sd8_tor_rvc_run ξ ti_pc10 csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000")))
              (ti_ea_ra sp0) vold_ra (⌜True⌝ : vProp Σ) q pmpcfg1 pmpaddrs
              (ti_sp1 sp0) ra0
              Hgid Hpmp Htor_ra Hnz_sp Hnz_ra eq_refl Hram_ra
              with "Hrun Hpmpc Hpaddr Hpc Hspc Hrac Hi10 Hstkra HRtrue").
    iIntros (T10) "_ Hrun Hpmpc Hpaddr Hpc Hspc Hrac Hstkra _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfacc10" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (regfile_upd2_id' (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
                      (ti_sp1 sp0) ra0 ltac:(ti_reg_neq) Lsp1 Lra1)) in "Hfile".
    assert (P1 : add_vec_int ti_pc10 2 = ti_pc11) by vm_refl.
    iEval (rewrite P1) in "Hpc".

    (* ==================================================================== *)
    (* ---- 11. c.sdsp s0, 0(sp)  (WRITTEN TOR entry; RELEASE store) ---- *)
    iPoseProof (wsti_11 kbs Hcov with "Htext") as "#Hi11".
    iDestruct (gpr_file_acc_2 (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hs0c & Hfacc11)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m1 m sp0) (Regidx csp_rs1)) Lsp1) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0) -(rf_lookup (ti_m1 m sp0) (Regidx ti_s0)) Ls01) in "Hs0c".
    iApply (wwp_sd8_tor_rvc_run ξ ti_pc11 csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000")))
              (ti_ea_s0 sp0) vold_s0 (⌜True⌝ : vProp Σ) q pmpcfg1 pmpaddrs
              (ti_sp1 sp0) s00
              Hgid Hpmp Htor_s0 Hnz_sp Hnz_s0 eq_refl Hram_s0
              with "Hrun Hpmpc Hpaddr Hpc Hspc Hs0c Hi11 Hstks0 HRtrue").
    iIntros (T11) "_ Hrun Hpmpc Hpaddr Hpc Hspc Hs0c Hstks0 _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iDestruct ("Hfacc11" with "Hspc Hs0c") as "Hfile".
    iEval (rewrite (regfile_upd2_id' (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
                      (ti_sp1 sp0) s00 ltac:(ti_reg_neq) Lsp1 Ls01)) in "Hfile".
    assert (P2 : add_vec_int ti_pc11 2 = ti_pc12) by vm_refl.
    iEval (rewrite P2) in "Hpc".

    (* ==================================================================== *)
    (* ---- 12. c.addi4spn s0, sp, 16 ---- *)
    iPoseProof (wsti_12 kbs Hcov with "Htext") as "#Hi12".
    iApply (wwp_addi_run ξ ti_pc12 true csp_rs1 ti_s0 (caddi4spn_imm nz12)
              (ti_m1 m sp0) pmpcfg1 q Hgid Hpmp Hnz_s0
              with "Hrun Hpmpc Hpc Hfile Hi12").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite Lsp1) in "Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg
                      (add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)))]>
                     (ti_m1 m sp0))
             with (ti_m12 m sp0)) in "Hfile".
    assert (P3 : add_vec_int ti_pc12 2 = ti_pc13) by vm_refl.
    iEval (rewrite P3) in "Hpc".

    (* ==================================================================== *)
    (* ---- 13. csrr a5, menvcfg ---- *)
    iPoseProof (wsti_13 kbs Hcov with "Htext") as "#Hi13".
    iDestruct (gpr_file_insert_acc (ti_m12 m sp0) (Regidx ti_a5) (regval_into_reg menv0)
                 with "Hfile") as "[Ha5c Hfins13]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_menvcfg_run ξ ti_pc13 ti_a5 menv0
              (ti_m12 m sp0 (Regidx ti_a5)) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Hmenv Ha5c Hi13").
    iIntros "Hrun Hpmpc Hpc Ha5c Hmenv".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins13" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0))
             with (ti_m13 m sp0 menv0)) in "Hfile".
    assert (P4 : add_vec_int ti_pc13 4 = ti_pc14) by vm_refl.
    iEval (rewrite P4) in "Hpc".

    (* ==================================================================== *)
    (* ---- 14. c.li a4, -1 ---- *)
    iDestruct (gpr_file_x0 (ti_m13 m sp0 menv0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_14 Hfile]".
    iPoseProof (wsti_14 kbs Hcov with "Htext") as "#Hi14".
    iApply (wwp_addi_run ξ ti_pc14 true cli_rs1 ti_a4 (sign_extend' 12 i14)
              (ti_m13 m sp0 menv0) pmpcfg1 q Hgid Hpmp Hnz_a4
              with "Hrun Hpmpc Hpc Hfile Hi14").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite Hx0_14 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0))
             with (ti_m14 m sp0 menv0)) in "Hfile".
    assert (P5 : add_vec_int ti_pc14 2 = ti_pc15) by vm_refl.
    iEval (rewrite P5) in "Hpc".

    (* ==================================================================== *)
    (* ---- 15. c.slli a4, 63 ---- *)
    assert (L15a4 : ti_m14 m sp0 menv0 !!! Regidx ti_a4 = cli_wval i14)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_15 kbs Hcov with "Htext") as "#Hi15".
    iApply (wwp_slli_rvc_run ξ ti_pc15 ti_a4 ti_a4 sh15 (ti_m14 m sp0 menv0)
              pmpcfg1 q Hgid Hpmp Hnz_a4 with "Hrun Hpmpc Hpc Hfile Hi15").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite L15a4 Hb63) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0))
             with (ti_m15 m sp0 menv0)) in "Hfile".
    assert (P6 : add_vec_int ti_pc15 2 = ti_pc16) by vm_refl.
    iEval (rewrite P6) in "Hpc".

    (* ==================================================================== *)
    (* ---- 16. c.or a5, a4 ---- *)
    assert (L16a5 : ti_m15 m sp0 menv0 !!! Regidx ti_a5 = menv0)
      by (ti_unfold; ti_look).
    assert (L16a4 : ti_m15 m sp0 menv0 !!! Regidx ti_a4 = ti_bit63)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_16 kbs Hcov with "Htext") as "#Hi16".
    iApply (wwp_or_rvc_run ξ ti_pc16 ti_a4 ti_a5 ti_a5 (ti_m15 m sp0 menv0)
              pmpcfg1 q Hgid Hpmp Hnz_a5 with "Hrun Hpmpc Hpc Hfile Hi16").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite L16a5 L16a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menv0 ti_bit63)]>
                     (ti_m15 m sp0 menv0))
             with (ti_m16 m sp0 menv0)) in "Hfile".
    assert (P7 : add_vec_int ti_pc16 2 = ti_pc17) by vm_refl.
    iEval (rewrite P7) in "Hpc".

    (* ==================================================================== *)
    (* ---- 17. csrw menvcfg, a5 ---- *)
    assert (L17a5 : ti_m16 m sp0 menv0 !!! Regidx ti_a5 = ti_menv1 menv0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_17 kbs Hcov with "Htext") as "#Hi17".
    iDestruct (gpr_file_lookup_acc (ti_m16 m sp0 menv0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb17]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_menvcfg_run ξ ti_pc17 ti_a5 menv0
              (ti_m16 m sp0 menv0 (Regidx ti_a5)) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Ha5c Hmenv Hi17").
    iIntros "Hrun Hpmpc Hpc Ha5c Hmenv".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb17" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m16 m sp0 menv0) (Regidx ti_a5)) L17a5) in "Hmenv".
    assert (P8 : add_vec_int ti_pc17 4 = ti_pc18) by vm_refl.
    iEval (rewrite P8) in "Hpc".

    (* ==================================================================== *)
    (* ---- 18. csrr a5, mcounteren ---- *)
    iPoseProof (wsti_18 kbs Hcov with "Htext") as "#Hi18".
    iDestruct (gpr_file_insert_acc (ti_m16 m sp0 menv0) (Regidx ti_a5)
                 (regval_into_reg (zero_extend' 64 mcen0)) with "Hfile") as "[Ha5c Hfins18]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_mcounteren_run ξ ti_pc18 ti_a5 mcen0
              (ti_m16 m sp0 menv0 (Regidx ti_a5)) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Hmcen Ha5c Hi18").
    iIntros "Hrun Hpmpc Hpc Ha5c Hmcen".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins18" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]>
                     (ti_m16 m sp0 menv0))
             with (ti_m18 m sp0 menv0 mcen0)) in "Hfile".
    assert (P9 : add_vec_int ti_pc18 4 = ti_pc19) by vm_refl.
    iEval (rewrite P9) in "Hpc".

    (* ==================================================================== *)
    (* ---- 19. ori a5, a5, 2 ---- *)
    assert (L19a5 : ti_m18 m sp0 menv0 mcen0 !!! Regidx ti_a5 = zero_extend' 64 mcen0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_19 kbs Hcov with "Htext") as "#Hi19".
    iApply (wwp_ori_run ξ ti_pc19 ti_a5 ti_a5 i19 (ti_m18 m sp0 menv0 mcen0)
              pmpcfg1 q Hgid Hpmp Hnz_a5 with "Hrun Hpmpc Hpc Hfile Hi19").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite L19a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19))]>
                     (ti_m18 m sp0 menv0 mcen0))
             with (ti_m19 m sp0 menv0 mcen0)) in "Hfile".
    assert (P10 : add_vec_int ti_pc19 4 = ti_pc20) by vm_refl.
    iEval (rewrite P10) in "Hpc".

    (* ==================================================================== *)
    (* ---- 20. csrw mcounteren, a5 ---- *)
    assert (L20a5 : ti_m19 m sp0 menv0 mcen0 !!! Regidx ti_a5 = ti_mcen1 mcen0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_20 kbs Hcov with "Htext") as "#Hi20".
    iDestruct (gpr_file_lookup_acc (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb20]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mcounteren_run ξ ti_pc20 ti_a5 mcen0
              (ti_m19 m sp0 menv0 mcen0 (Regidx ti_a5)) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Ha5c Hmcen Hi20").
    iIntros "Hrun Hpmpc Hpc Ha5c Hmcen".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb20" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5)) L20a5) in "Hmcen".
    assert (P11 : add_vec_int ti_pc20 4 = ti_pc21) by vm_refl.
    iEval (rewrite P11) in "Hpc".

    (* ==================================================================== *)
    (* ---- 21. csrr a5, time  (the read value [tv] is the leaf's own ∀) ---- *)
    iPoseProof (wsti_21 kbs Hcov with "Htext") as "#Hi21".
    iDestruct (gpr_file_reinsert_acc (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5)
                 with "Hfile") as "[Ha5c Hfins21]".
    (* the wrapper quantifies the read value [tv] itself, unknown until it
       returns it -- [gpr_file_reinsert_acc]'s wand stays open over the
       eventual value, unlike [gpr_file_insert_acc]'s fixed one. *)
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_time_run ξ ti_pc21 ti_a5
              (ti_m19 m sp0 menv0 mcen0 (Regidx ti_a5)) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Ha5c Hi21").
    iIntros (tv) "Hrun Hpmpc Hpc Ha5c".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins21" $! (regval_into_reg tv) with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg tv]> (ti_m19 m sp0 menv0 mcen0))
             with (ti_m21 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P12 : add_vec_int ti_pc21 4 = ti_pc22) by vm_refl.
    iEval (rewrite P12) in "Hpc".

    (* ==================================================================== *)
    (* ---- 22. lui a4, 0xf4 ---- *)
    iPoseProof (wsti_22 kbs Hcov with "Htext") as "#Hi22".
    iApply (wwp_lui_run ξ ti_pc22 false ti_a4 i22 (ti_m21 m sp0 menv0 mcen0 tv)
              pmpcfg1 q Hgid Hpmp Hnz_a4 with "Hrun Hpmpc Hpc Hfile Hi22").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival i22)]>
                     (ti_m21 m sp0 menv0 mcen0 tv))
             with (ti_m22 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P13 : add_vec_int ti_pc22 4 = ti_pc23) by vm_refl.
    iEval (rewrite P13) in "Hpc".

    (* ==================================================================== *)
    (* ---- 23. addi a4, a4, 576 ---- *)
    assert (L23a4 : ti_m22 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = luival i22)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_23 kbs Hcov with "Htext") as "#Hi23".
    iApply (wwp_addi_run ξ ti_pc23 false ti_a4 ti_a4 i23
              (ti_m22 m sp0 menv0 mcen0 tv) pmpcfg1 q Hgid Hpmp Hnz_a4
              with "Hrun Hpmpc Hpc Hfile Hi23").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite L23a4 Hival) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_interval]>
                     (ti_m22 m sp0 menv0 mcen0 tv))
             with (ti_m23 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P14 : add_vec_int ti_pc23 4 = ti_pc24) by vm_refl.
    iEval (rewrite P14) in "Hpc".

    (* ==================================================================== *)
    (* ---- 24. c.add a5, a4 ---- *)
    assert (L24a5 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = tv)
      by (ti_unfold; ti_look).
    assert (L24a4 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = ti_interval)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_24 kbs Hcov with "Htext") as "#Hi24".
    iApply (wwp_add_rvc_run ξ ti_pc24 ti_a4 ti_a5 ti_a5
              (ti_m23 m sp0 menv0 mcen0 tv) pmpcfg1 q Hgid Hpmp Hnz_a5
              with "Hrun Hpmpc Hpc Hfile Hi24").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite L24a5 L24a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (add_vec tv ti_interval)]>
                     (ti_m23 m sp0 menv0 mcen0 tv))
             with (ti_m24 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P15 : add_vec_int ti_pc24 2 = ti_pc25) by vm_refl.
    iEval (rewrite P15) in "Hpc".

    (* ==================================================================== *)
    (* ---- 25. csrw stimecmp, a5 ---- *)
    assert (L25a5 : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = ti_deadline tv)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_25 kbs Hcov with "Htext") as "#Hi25".
    iDestruct (gpr_file_lookup_acc (ti_m24 m sp0 menv0 mcen0 tv) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb25]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_stimecmp_run ξ ti_pc25 ti_a5 stimecmp0
              (ti_m24 m sp0 menv0 mcen0 tv (Regidx ti_a5)) pmpcfg1 q
              Hgid Hpmp Hnz_a5 with "Hrun Hpmpc Hpc Ha5c Hstc Hi25").
    iIntros "Hrun Hpmpc Hpc Ha5c Hstc".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb25" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m24 m sp0 menv0 mcen0 tv) (Regidx ti_a5)) L25a5) in "Hstc".
    assert (P16 : add_vec_int ti_pc25 4 = ti_pc26) by vm_refl.
    iEval (rewrite P16) in "Hpc".

    (* ==================================================================== *)
    (* ---- 26. c.ldsp ra, 8(sp)  (WRITTEN TOR entry) ---- *)
    assert (L26sp : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_26 kbs Hcov with "Htext") as "#Hi26".
    iDestruct (gpr_file_acc_2 (ti_m24 m sp0 menv0 mcen0 tv) (Regidx csp_rs1) (Regidx ti_ra)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hrac & Hfacc26)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m24 m sp0 menv0 mcen0 tv)
             (Regidx csp_rs1)) L26sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_ld8_tor_rvc_run ξ ti_pc26 csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000")))
              (ti_ea_ra sp0) ra0 (DfracOwn 1) q pmpcfg1 pmpaddrs
              (ti_sp1 sp0) (ti_m24 m sp0 menv0 mcen0 tv (Regidx ti_ra))
              Hgid Hpmp Htor_ra Hnz_sp Hnz_ra eq_refl Hram_ra
              with "Hrun Hpmpc Hpaddr Hpc Hspc Hrac Hi26 Hstkra").
    iIntros "Hrun Hpmpc Hpaddr Hpc Hspc Hrac Hstkra".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfacc26" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (regfile_upd_drop_outer' (ti_m24 m sp0 menv0 mcen0 tv) (Regidx csp_rs1) (Regidx ti_ra)
                      (ti_sp1 sp0) (regval_into_reg ra0) ltac:(ti_reg_neq) L26sp)) in "Hfile".
    iEval (change (<[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 tv))
             with (ti_m26 m sp0 menv0 mcen0 tv ra0)) in "Hfile".
    assert (P17 : add_vec_int ti_pc26 2 = ti_pc27) by vm_refl.
    iEval (rewrite P17) in "Hpc".

    (* ==================================================================== *)
    (* ---- 27. c.ldsp s0, 0(sp)  (WRITTEN TOR entry) ---- *)
    assert (L27sp : ti_m26 m sp0 menv0 mcen0 tv ra0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_27 kbs Hcov with "Htext") as "#Hi27".
    iDestruct (gpr_file_acc_2 (ti_m26 m sp0 menv0 mcen0 tv ra0) (Regidx csp_rs1) (Regidx ti_s0)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hs0c & Hfacc27)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m26 m sp0 menv0 mcen0 tv ra0)
             (Regidx csp_rs1)) L27sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iApply (wwp_ld8_tor_rvc_run ξ ti_pc27 csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000")))
              (ti_ea_s0 sp0) s00 (DfracOwn 1) q pmpcfg1 pmpaddrs
              (ti_sp1 sp0) (ti_m26 m sp0 menv0 mcen0 tv ra0 (Regidx ti_s0))
              Hgid Hpmp Htor_s0 Hnz_sp Hnz_s0 eq_refl Hram_s0
              with "Hrun Hpmpc Hpaddr Hpc Hspc Hs0c Hi27 Hstks0").
    iIntros "Hrun Hpmpc Hpaddr Hpc Hspc Hs0c Hstks0".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iDestruct ("Hfacc27" with "Hspc Hs0c") as "Hfile".
    iEval (rewrite (regfile_upd_drop_outer' (ti_m26 m sp0 menv0 mcen0 tv ra0)
                      (Regidx csp_rs1) (Regidx ti_s0)
                      (ti_sp1 sp0) (regval_into_reg s00) ltac:(ti_reg_neq) L27sp)) in "Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg s00]>
                     (ti_m26 m sp0 menv0 mcen0 tv ra0))
             with (ti_m27 m sp0 menv0 mcen0 tv ra0 s00)) in "Hfile".
    assert (P18 : add_vec_int ti_pc27 2 = ti_pc28) by vm_refl.
    iEval (rewrite P18) in "Hpc".

    (* ==================================================================== *)
    (* ---- 28. c.addi sp, 16 ---- *)
    assert (L28sp : ti_m27 m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_28 kbs Hcov with "Htext") as "#Hi28".
    iApply (wwp_addi_run ξ ti_pc28 true csp_rs1 csp_rs1 (sign_extend' 12 i28)
              (ti_m27 m sp0 menv0 mcen0 tv ra0 s00) pmpcfg1 q Hgid Hpmp Hnz_sp
              with "Hrun Hpmpc Hpc Hfile Hi28").
    iIntros "Hrun Hpmpc Hpc Hfile".
    iEval (rewrite sext6_12_64 L28sp Hspres) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg sp0]>
                     (ti_m27 m sp0 menv0 mcen0 tv ra0 s00))
             with (ti_mout m sp0 menv0 mcen0 tv ra0 s00)) in "Hfile".
    assert (P19 : add_vec_int ti_pc28 2 = ti_pc29) by vm_refl.
    iEval (rewrite P19) in "Hpc".

    (* ==================================================================== *)
    (* ---- 29. c.ret ---- *)
    assert (L29ra : ti_mout m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    iPoseProof (wsti_29 kbs Hcov with "Htext") as "#Hi29".
    iDestruct (gpr_file_lookup_acc (ti_mout m sp0 menv0 mcen0 tv ra0 s00) (Regidx ti_ra)
                 with "Hfile") as "[Hrac Hfb29]".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_cjr_rvc_run ξ ti_pc29 ti_ra
              (ti_mout m sp0 menv0 mcen0 tv ra0 s00 (Regidx ti_ra)) pmpcfg1 q
              Hgid Hpmp Hnz_ra with "Hrun Hpmpc Hpc Hrac Hi29").
    iIntros "Hrun Hpmpc Hpc Hrac".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfb29" with "Hrac") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_mout m sp0 menv0 mcen0 tv ra0 s00) (Regidx ti_ra)) L29ra)
      in "Hpc".

    (* ==================================================================== *)
    (* re-bundle the two frame slots (+ the untouched deeper stack) and hand
       everything to the caller.  No view arithmetic: each [cobj] has sat in
       the context, untouched, since the step that produced it. *)
    iEval (rewrite Hpra) in "Hstkra". iEval (rewrite Hps0) in "Hstks0".
    iAssert (cobj ξ (wpt8 (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
                     wpt8 (pa_stk sp0 2) (DfracOwn 1) s00))
      with "[Hstkra Hstks0]" as "Htop".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (stack_2_intro_ent sp0 ra0 s00) with "Htop") as "Htop".
    iAssert (cobj ξ (wstack_own_phys sp0 2 ∗ wstack_own_phys (pa_stk sp0 2) (n - 2)))
      with "[Htop Hdeep]" as "Hstk2".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_2 sp0 2 n Hn2) with "Hstk2")
      as "Hstk".
    iApply ("Hcont" $! tv with
              "Hrun Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hstc Hstk").
  Qed.

End WkTimerinitThm.
