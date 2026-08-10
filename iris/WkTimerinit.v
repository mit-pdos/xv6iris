(** * WkTimerinit.v -- the weak-memory twin of [WpTimerinit.wp_timerinit]:
    xv6's [timerinit()] (21 instructions, KernelInstrs indices 9..29) as ONE
    [WWP] theorem, composed entirely from the HOISTED weak leaves (the
    "remaining-leaf batch", claude-notes/projects/weak-memory.md).

    Statement = [WpTimerinit.wp_timerinit] under the porting-table swaps
    (claude-notes/projects/weak-memory-porting.md):
      - [kernel_text]        -> [WeakInstr.wkernel_text kbs] + [wkb_covers kbs]
        (the [WkEntryEff] seam, reused verbatim);
      - [stack_own_phys sp0 n] (built from [↦ₚ₈])
                              -> [hart_ws cpu_id ws] + [vwp_hold
        (WkStackOwn.wstack_own_phys sp0 n) ws]; the continuation binds a
        FRESH [ws'] with [⌜ws_le ws ws'⌝];
      - [WP (Loop : expr riscv_lang) {{ Φ }}] -> [WWP Loop] (no postcondition
        tree-wide);
      - everything else (the [mmode_config]/[pmpcfg_n]/[pmpaddr_n] fractional
        config, [pc_is], [gpr_file], the CSR cells, the [ti_*]/[m_*]
        definitional vocabulary) is REUSED UNCHANGED from [CodeTimerinitAux]
        / [WpTimerinit] -- never restated.

    Every instruction is discharged by ONE application of its hoisted leaf:

      9,12,14,28  c.addi/c.addi4spn/c.li/c.addi (ADDI, RVC)  -> WeakLeafItype.wwp_addi_rvc_leaf
      23          addi (F_Base)                              -> WeakLeafItype.wwp_addi_leaf
      19          ori  (F_Base)                               -> WeakLeafItype.wwp_ori_leaf
      22          lui  (F_Base)                               -> WeakLeafUtypeShift.wwp_lui_leaf
      15          c.slli (RVC)                                -> WeakLeafUtypeShift.wwp_slli_rvc_leaf
      16          c.or   (RVC)                                -> WeakLeafRtypeW.wwp_or_rvc_leaf
      24          c.add  (RVC)                                -> WeakLeafRtypeW.wwp_add_rvc_leaf
      13          csrr a5,menvcfg                             -> WeakLeafCsrrM.wwp_csrr_menvcfg_leaf
      18          csrr a5,mcounteren                          -> WeakLeafCsrrM.wwp_csrr_mcounteren_leaf
      21          csrr a5,time                                -> WeakLeafCsrrTime.wwp_csrr_time_leaf
      17          csrw menvcfg,a5                              -> WeakLeafCsrw2.wwp_csrw_menvcfg_leaf
      20          csrw mcounteren,a5                           -> WeakLeafCsrw2.wwp_csrw_mcounteren_leaf
      25          csrw stimecmp,a5                             -> WeakLeafStimecmp.wwp_csrw_stimecmp_leaf
      10,11       c.sdsp ra/s0 (WRITTEN TOR entry)             -> WeakLeafTor.wwp_sd8_tor_rvc_leaf
      26,27       c.ldsp ra/s0 (WRITTEN TOR entry)             -> WeakLeafTor.wwp_ld8_tor_rvc_leaf
      29          c.ret                                        -> WeakLeafJump.wwp_cjr_rvc_leaf

    Every leaf is ALIGNMENT-GENERIC ([al4 : bool]); each call site supplies
    [al4 := is_aligned_vaddr (Virtaddr pc) 4] and closes its own premise with
    [eq_refl] -- no per-instruction alignment arithmetic is needed.  The
    per-instruction decode obligations ([Hdecf]/[Hgood]/[Hdec]/[Hgood0]/[Hexp])
    are closed by the SAME [KernelDecodeNN.kd_*]/[ke_*] facts and
    [WpMmodeLeafBase.exec_execute_C_*] combinators [CodeTimerinit.v]'s
    generated [tmi_*] constructors use -- restated at the generic reference
    state [WpDecodeBridge.dstateM] via [D_m]/[agree_m_regs]/[D_none]
    ([WkEntryEff], reused).

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
Require Import WkStackOwn WkGprAcc.
Require Import WkEntryEff.
Require Import KernelDecode00 KernelDecode01 KernelDecode04 KernelDecode06 KernelDecode07
  KernelDecode11 KernelDecode12 KernelDecode13 KernelDecode14 KernelDecode15
  KernelDecode17 KernelDecode20 KernelDecode21 KernelDecode24 KernelDecode31.

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
     [wwp_csrr_time_leaf] application returns it, so the wand must stay
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

  (* [WpDecodeBridge.agree_m]/[WkEntryEff.agree_m_regs] restated in the
     argument order every leaf's [Hagree] premise wants
     (priv, misa, mseccfg -- [agree_m_regs] takes priv, mseccfg, misa). *)
  Local Definition ti_agree : forall rs : Riscv.rv64d_types.regstate,
      register_lookup cur_privilege rs = Machine ->
      register_lookup misa rs = MISA_C ->
      register_lookup mseccfg rs = mword_of_int 0 ->
      forall r, D_m r = true ->
        register_lookup r rs = register_lookup r (sregs dstateM) :=
    fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi.

  (* [WkStackOwn.wstack_own_phys_2_intro] as a single [∗]-shaped entailment,
     so it composes with [vwp_hold_ent] at the final re-bundling. *)
  Local Lemma stack_2_intro_ent (sp : Arch.pa) (w1 w2 : bv 64) :
    (wpt8 (pa_stk sp 1) (DfracOwn 1) w1 ∗ wpt8 (pa_stk sp 2) (DfracOwn 1) w2)
    ⊢ wstack_own_phys sp 2.
  Proof. iIntros "[H1 H2]". iApply (wstack_own_phys_2_intro with "H1 H2"). Qed.

  (* [WkTimerinit.wwp_timerinit]: the whole-function spec, same statement as
     [WpTimerinit.wp_timerinit] under the porting-table swaps. *)
  Lemma wwp_timerinit (q : Qp)
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (menv0 stimecmp0 : mword 64) (mcen0 : mword 32)
      (pmpcfg1 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (n : nat) (kbs : _) (ws : wstate) :
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
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is ti_pc9 -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menv0 -∗
    mcounteren ↦ᵣ mcen0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wstack_own_phys sp0 n) ws -∗
    wkernel_text kbs -∗
    ( ∀ (tv : mword 64) (ws' : wstate),
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (ret_pc ra0) -∗
      gpr_file (ti_mout m sp0 menv0 mcen0 tv ra0 s00) -∗
      menvcfg ↦ᵣ menvcfg_legalized menv0 (ti_menv1 menv0) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcen0 (ti_mcen1 mcen0) -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wstack_own_phys sp0 n) ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hn2 Hgid Hpmp Htor_ra Htor_s0 Hcov Hsp Hra Hs0 Hram_ra Hram_s0.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] Hfile Hmenv Hmcen Hstc Hhws Hstk #Htext Hcont".
    (* ---- split off the top two stack slots, under [vwp_hold] ---- *)
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_split_1 sp0 2 n Hn2)
                 with "Hstk") as "Hstk".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Htop Hdeep]".
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_2_elim sp0) with "Htop")
      as "Htop".
    iEval (rewrite vwp_hold_exist) in "Htop". iDestruct "Htop" as (vold_ra) "Htop".
    iEval (rewrite vwp_hold_exist) in "Htop". iDestruct "Htop" as (vold_s0) "Htop".
    iEval (rewrite vwp_hold_sep) in "Htop". iDestruct "Htop" as "[Hstkra Hstks0]".
    assert (Hpra : ti_ea_ra sp0 = pa_stk sp0 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hps0 : ti_ea_s0 sp0 = pa_stk sp0 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpra) in "Hstkra". iEval (rewrite -Hps0) in "Hstks0".
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
    (* ---- 9. c.addi sp, -16  (F_RVC 0x1141, ADDI) ---- *)
    assert (Hal2_9 : is_aligned_vaddr (Virtaddr ti_pc9) 2 = true)
      by vm_refl.
    assert (Hacc_9 : acc_wf ti_pc9 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_9 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc9 j))
      by ram_win.
    assert (Hbytes_9 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x0 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x0)) j)) by kb_win.
    assert (Hsub_9 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x0)) 15 0
                     = (mword_of_int 0x1141 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_9 : isRVC (mword_of_int 0x1141 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc9 (F_RVC (mword_of_int 0x1141))) as "#Hbs9".
    { iApply (winstr_bytes_of_text kbs ti_pc9 (F_RVC (mword_of_int 0x1141))
                (kb_word_at (KernelSyms.timerinit + 0x0)) Hal2_9 Hacc_9 Hram_9
                (conj Hsub_9 Hrvc_9) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x0)
        (kb_word_at (KernelSyms.timerinit + 0x0)) Hcov Hbytes_9). }
    assert (Hgood_9 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x1141 : mword 16))
                        dstateM = true) by vm_refl.
    assert (Hdec_9 : exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) dstateM
                     = Some (C_ADDI (i9, Regidx csp_rs1), dstateM))
      by vm_refl.
    assert (Hgood0_9 : forall s : mstate,
              goodb0 D_none (execute (C_ADDI (i9, Regidx csp_rs1))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_9 : forall s : mstate, exec (execute (C_ADDI (i9, Regidx csp_rs1))) s
                = Some (ExecuteAs (ITYPE (sign_extend' 12 i9, Regidx csp_rs1,
                                          Regidx csp_rs1, ADDI)), s))
      by exact (exec_execute_C_ADDI i9 (Regidx csp_rs1)).
    assert (Hlpad_9 : is_lpad_instruction (C_ADDI (i9, Regidx csp_rs1)) = false)
      by vm_refl.
    assert (Hdecf_9 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x1141 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (ITYPE (sign_extend' 12 i9, Regidx csp_rs1,
                                      Regidx csp_rs1, ADDI)), s))).
    { intros t _ HC _ _ _. exists (C_ADDI (i9, Regidx csp_rs1)). split_and!.
      - exact (kd_1141 t HC).
      - exact Hlpad_9.
      - exact Hexp_9. }
    iApply (wwp_addi_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc9) 4)
              ti_pc9 (mword_of_int 0x1141) csp_rs1 csp_rs1 (sign_extend' 12 i9)
              (C_ADDI (i9, Regidx csp_rs1)) m ti_pc9 pmpcfg1 q D_m D_none dstateM ws
              Hgid Hpmp Hal2_9 eq_refl Hnz_sp
              Hdecf_9 ti_agree D_m_mi Hgood_9 Hdec_9 Hgood0_9 Hexp_9
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs9 Hhws").
    iIntros (ws1) "%Hle1 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite sext6_12_64) in "Hfile".
    iEval (rewrite Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (ti_m1 m sp0)) in "Hfile".
    assert (P0 : add_vec_int ti_pc9 2 = ti_pc10) by vm_refl.
    iEval (rewrite P0) in "Hpc". iEval (rewrite P0) in "Hnpc".
    (* the two frame words have not moved yet: bump to [ws1] *)
    iDestruct (vwp_hold_mono _ ws ws1 Hle1 with "Hstkra") as "Hstkra".
    iDestruct (vwp_hold_mono _ ws ws1 Hle1 with "Hstks0") as "Hstks0".

    (* ==================================================================== *)
    (* ---- 10. c.sdsp ra, 8(sp)  (F_RVC 0xe406, STORE, WRITTEN TOR) ---- *)
    assert (Lsp1 : ti_m1 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0) by (ti_unfold; ti_look).
    assert (Lra1 : ti_m1 m sp0 !!! Regidx ti_ra = ra0) by (ti_unfold; ti_look).
    assert (Ls01 : ti_m1 m sp0 !!! Regidx ti_s0 = s00) by (ti_unfold; ti_look).
    assert (Hal2_10 : is_aligned_vaddr (Virtaddr ti_pc10) 2 = true)
      by vm_refl.
    assert (Hram4_10 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc10 j))
      by ram_win.
    assert (Hbytes_10 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x2)) j)) by kb_win.
    assert (Hsub_10 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x2)) 15 0
                      = (mword_of_int 0xe406 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_10 : isRVC (mword_of_int 0xe406 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc10 (F_RVC (mword_of_int 0xe406))) as "#Hbs10".
    { iApply (winstr_bytes_of_text kbs ti_pc10 (F_RVC (mword_of_int 0xe406))
                (kb_word_at (KernelSyms.timerinit + 0x2)) Hal2_10 ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram4_10 (conj Hsub_10 Hrvc_10) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2)
        (kb_word_at (KernelSyms.timerinit + 0x2)) Hcov Hbytes_10). }
    assert (Hgood_10 : goodb0 D_m (ext_decode_compressed (mword_of_int 0xe406 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_10 : exec (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) dstateM
                      = Some (C_SDSP (u10, Regidx ti_ra), dstateM))
      by vm_refl.
    assert (Hgood0_10 : forall s : mstate,
              goodb0 D_none (execute (C_SDSP (u10, Regidx ti_ra))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_10 : forall s : mstate, exec (execute (C_SDSP (u10, Regidx ti_ra))) s
                = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u10 ('b"000")),
                                          Regidx ti_ra, Regidx csp_rs1, 8)), s))
      by exact (exec_execute_C_SDSP u10 (Regidx ti_ra)).
    assert (Hlpad_10 : is_lpad_instruction (C_SDSP (u10, Regidx ti_ra)) = false)
      by vm_refl.
    assert (Hdecf_10 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0xe406 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u10 ('b"000")),
                                      Regidx ti_ra, Regidx csp_rs1, 8)), s))).
    { intros t _ HC _ _ _. exists (C_SDSP (u10, Regidx ti_ra)). split_and!.
      - exact (kd_e406 t HC).
      - exact Hlpad_10.
      - exact Hexp_10. }
    iDestruct (gpr_file_acc_2 (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hrac & Hfacc10)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m1 m sp0) (Regidx csp_rs1)) Lsp1) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra) -(rf_lookup (ti_m1 m sp0) (Regidx ti_ra)) Lra1) in "Hrac".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws1) as "HRtrue10".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_sd8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc10) 4)
              ti_pc10 (mword_of_int 0xe406) csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000")))
              (C_SDSP (u10, Regidx ti_ra)) (ti_ea_ra sp0) vold_ra (⌜True⌝%I) q
              pmpcfg1 pmpaddrs (ti_sp1 sp0) ra0 ti_pc10 D_m D_none dstateM ws1
              Hgid Hpmp Htor_ra Hal2_10 eq_refl Hnz_sp Hnz_ra eq_refl
              Hram_ra Hdecf_10 ti_agree D_m_mi Hgood_10 Hdec_10 Hgood0_10 Hexp_10
              with "Hmm Hpmpc Hpaddr Hpc Hnpc Hspc Hrac Hbs10 Hhws Hstkra HRtrue10").
    iIntros (ws2 T10) "%Hle2 %HT10 Hmm Hpmpc Hpaddr [Hpc Hnpc] Hspc Hrac Hhws Hstkra _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfacc10" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (regfile_upd2_id' (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
                      (ti_sp1 sp0) ra0 ltac:(ti_reg_neq) Lsp1 Lra1)) in "Hfile".
    assert (P1 : add_vec_int ti_pc10 2 = ti_pc11) by vm_refl.
    iEval (rewrite P1) in "Hpc". iEval (rewrite P1) in "Hnpc".
    (* [Hstks0] has not moved since the start: bump to [ws2] *)
    iDestruct (vwp_hold_mono _ ws1 ws2 Hle2 with "Hstks0") as "Hstks0".

    (* ==================================================================== *)
    (* ---- 11. c.sdsp s0, 0(sp)  (F_RVC 0xe022, STORE, WRITTEN TOR) ---- *)
    assert (Hal2_11 : is_aligned_vaddr (Virtaddr ti_pc11) 2 = true)
      by vm_refl.
    assert (Hram4_11 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc11 j))
      by ram_win.
    assert (Hbytes_11 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x4 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x4)) j)) by kb_win.
    assert (Hsub_11 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x4)) 15 0
                      = (mword_of_int 0xe022 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_11 : isRVC (mword_of_int 0xe022 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc11 (F_RVC (mword_of_int 0xe022))) as "#Hbs11".
    { iApply (winstr_bytes_of_text kbs ti_pc11 (F_RVC (mword_of_int 0xe022))
                (kb_word_at (KernelSyms.timerinit + 0x4)) Hal2_11 ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram4_11 (conj Hsub_11 Hrvc_11) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x4)
        (kb_word_at (KernelSyms.timerinit + 0x4)) Hcov Hbytes_11). }
    assert (Hgood_11 : goodb0 D_m (ext_decode_compressed (mword_of_int 0xe022 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_11 : exec (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) dstateM
                      = Some (C_SDSP (u11, Regidx ti_s0), dstateM))
      by vm_refl.
    assert (Hgood0_11 : forall s : mstate,
              goodb0 D_none (execute (C_SDSP (u11, Regidx ti_s0))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_11 : forall s : mstate, exec (execute (C_SDSP (u11, Regidx ti_s0))) s
                = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u11 ('b"000")),
                                          Regidx ti_s0, Regidx csp_rs1, 8)), s))
      by exact (exec_execute_C_SDSP u11 (Regidx ti_s0)).
    assert (Hlpad_11 : is_lpad_instruction (C_SDSP (u11, Regidx ti_s0)) = false)
      by vm_refl.
    assert (Hdecf_11 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0xe022 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u11 ('b"000")),
                                      Regidx ti_s0, Regidx csp_rs1, 8)), s))).
    { intros t _ HC _ _ _. exists (C_SDSP (u11, Regidx ti_s0)). split_and!.
      - exact (kd_e022 t HC).
      - exact Hlpad_11.
      - exact Hexp_11. }
    iDestruct (gpr_file_acc_2 (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hs0c & Hfacc11)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m1 m sp0) (Regidx csp_rs1)) Lsp1) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0) -(rf_lookup (ti_m1 m sp0) (Regidx ti_s0)) Ls01) in "Hs0c".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws2) as "HRtrue11".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_sd8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc11) 4)
              ti_pc11 (mword_of_int 0xe022) csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000")))
              (C_SDSP (u11, Regidx ti_s0)) (ti_ea_s0 sp0) vold_s0 (⌜True⌝%I) q
              pmpcfg1 pmpaddrs (ti_sp1 sp0) s00 ti_pc11 D_m D_none dstateM ws2
              Hgid Hpmp Htor_s0 Hal2_11 eq_refl Hnz_sp Hnz_s0 eq_refl
              Hram_s0 Hdecf_11 ti_agree D_m_mi Hgood_11 Hdec_11 Hgood0_11 Hexp_11
              with "Hmm Hpmpc Hpaddr Hpc Hnpc Hspc Hs0c Hbs11 Hhws Hstks0 HRtrue11").
    iIntros (ws3 T11) "%Hle3 %HT11 Hmm Hpmpc Hpaddr [Hpc Hnpc] Hspc Hs0c Hhws Hstks0 _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iDestruct ("Hfacc11" with "Hspc Hs0c") as "Hfile".
    iEval (rewrite (regfile_upd2_id' (ti_m1 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
                      (ti_sp1 sp0) s00 ltac:(ti_reg_neq) Lsp1 Ls01)) in "Hfile".
    assert (P2 : add_vec_int ti_pc11 2 = ti_pc12) by vm_refl.
    iEval (rewrite P2) in "Hpc". iEval (rewrite P2) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 12. c.addi4spn s0, sp, 16  (F_RVC 0x0800, ADDI via ADDI4SPN) ---- *)
    assert (Hal2_12 : is_aligned_vaddr (Virtaddr ti_pc12) 2 = true)
      by vm_refl.
    assert (Hram_12 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc12 j))
      by ram_win.
    assert (Hbytes_12 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x6 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x6)) j)) by kb_win.
    assert (Hsub_12 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x6)) 15 0
                      = (mword_of_int 0x0800 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_12 : isRVC (mword_of_int 0x0800 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc12 (F_RVC (mword_of_int 0x0800))) as "#Hbs12".
    { iApply (winstr_bytes_of_text kbs ti_pc12 (F_RVC (mword_of_int 0x0800))
                (kb_word_at (KernelSyms.timerinit + 0x6)) Hal2_12
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_12 (conj Hsub_12 Hrvc_12) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x6)
        (kb_word_at (KernelSyms.timerinit + 0x6)) Hcov Hbytes_12). }
    assert (Hgood_12 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x0800 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_12 : exec (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) dstateM
                      = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12), dstateM))
      by vm_refl.
    assert (Hgood0_12 : forall s : mstate,
              goodb0 D_none (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_12 : forall s : mstate,
              exec (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s
              = Some (ExecuteAs (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1,
                                        Regidx ti_s0, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_ADDI4SPN (Cregidx (mword_of_int 0)) nz12).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    assert (Hlpad_12 : is_lpad_instruction (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))
                       = false) by vm_refl.
    assert (Hdecf_12 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x0800 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1,
                                      Regidx ti_s0, ADDI)), s))).
    { intros t _ HC _ _ _. exists (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12)). split_and!.
      - exact (kd_0800 t HC).
      - exact Hlpad_12.
      - exact Hexp_12. }
    iApply (wwp_addi_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc12) 4)
              ti_pc12 (mword_of_int 0x0800) csp_rs1 ti_s0 (caddi4spn_imm nz12)
              (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12)) (ti_m1 m sp0) ti_pc12
              pmpcfg1 q D_m D_none dstateM ws3
              Hgid Hpmp Hal2_12 eq_refl Hnz_s0
              Hdecf_12 ti_agree D_m_mi Hgood_12 Hdec_12 Hgood0_12 Hexp_12
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs12 Hhws").
    iIntros (ws4) "%Hle4 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite Lsp1) in "Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg
                      (add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)))]>
                     (ti_m1 m sp0))
             with (ti_m12 m sp0)) in "Hfile".
    assert (P3 : add_vec_int ti_pc12 2 = ti_pc13) by vm_refl.
    iEval (rewrite P3) in "Hpc". iEval (rewrite P3) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 13. csrr a5, menvcfg  (F_Base 0x30a027f3) ---- *)
    assert (Hal2_13 : is_aligned_vaddr (Virtaddr ti_pc13) 2 = true)
      by vm_refl.
    assert (Hram_13 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc13 j))
      by ram_win.
    assert (Hbytes_13 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x8 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x30a027f3 : mword 32) j)) by kb_win.
    assert (HnotRVC_13 : isRVC (subrange_vec_dec (mword_of_int 0x30a027f3 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc13 (F_Base (mword_of_int 0x30a027f3))) as "#Hbs13".
    { iApply (winstr_bytes_of_text kbs ti_pc13 (F_Base (mword_of_int 0x30a027f3))
                (mword_of_int 0x30a027f3) Hal2_13
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_13 (conj eq_refl HnotRVC_13) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x8)
        (mword_of_int 0x30a027f3) Hcov Hbytes_13). }
    assert (Hgood_13 : goodb0 D_m (ext_decode (mword_of_int 0x30a027f3 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_13 : exec (ext_decode (mword_of_int 0x30a027f3 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), dstateM))
      by vm_refl.
    assert (Hdecf_13 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x30a027f3 : mword 32))) t
         = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_30a027f3 t Hmi Hcfg). }
    iDestruct (gpr_file_insert_acc (ti_m12 m sp0) (Regidx ti_a5) (regval_into_reg menv0)
                 with "Hfile") as "[Ha5c Hfins13]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_menvcfg_leaf (is_aligned_vaddr (Virtaddr ti_pc13) 4)
              ti_pc13 (mword_of_int 0x30a027f3) ti_a5 menv0
              (ti_m12 m sp0 (Regidx ti_a5)) ti_pc13 pmpcfg1 q D_m dstateM ws4
              Hgid Hpmp Hal2_13 eq_refl Hnz_a5
              Hdecf_13 ti_agree D_m_mi Hgood_13 Hdec_13
              with "Hmm Hpmpc Hpc Hnpc Hmenv Ha5c Hbs13 Hhws").
    iIntros (ws5) "%Hle5 Hmm Hpmpc [Hpc Hnpc] Ha5c Hmenv Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins13" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0))
             with (ti_m13 m sp0 menv0)) in "Hfile".
    assert (P4 : add_vec_int ti_pc13 4 = ti_pc14) by vm_refl.
    iEval (rewrite P4) in "Hpc". iEval (rewrite P4) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 14. c.li a4, -1  (F_RVC 0x577d, ADDI via LI) ---- *)
    iDestruct (gpr_file_x0 (ti_m13 m sp0 menv0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_14 Hfile]".
    assert (Hal2_14 : is_aligned_vaddr (Virtaddr ti_pc14) 2 = true)
      by vm_refl.
    assert (Hram_14 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc14 j))
      by ram_win.
    assert (Hbytes_14 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0xc + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0xc)) j)) by kb_win.
    assert (Hsub_14 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0xc)) 15 0
                      = (mword_of_int 0x577d : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_14 : isRVC (mword_of_int 0x577d : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc14 (F_RVC (mword_of_int 0x577d))) as "#Hbs14".
    { iApply (winstr_bytes_of_text kbs ti_pc14 (F_RVC (mword_of_int 0x577d))
                (kb_word_at (KernelSyms.timerinit + 0xc)) Hal2_14
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_14 (conj Hsub_14 Hrvc_14) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0xc)
        (kb_word_at (KernelSyms.timerinit + 0xc)) Hcov Hbytes_14). }
    assert (Hgood_14 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x577d : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_14 : exec (ext_decode_compressed (mword_of_int 0x577d : mword 16)) dstateM
                      = Some (C_LI (i14, Regidx ti_a4), dstateM))
      by vm_refl.
    assert (Hgood0_14 : forall s : mstate,
              goodb0 D_none (execute (C_LI (i14, Regidx ti_a4))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_14 : forall s : mstate, exec (execute (C_LI (i14, Regidx ti_a4))) s
                = Some (ExecuteAs (ITYPE (sign_extend' 12 i14, Regidx cli_rs1,
                                          Regidx ti_a4, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_LI i14 (Regidx ti_a4)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    assert (Hlpad_14 : is_lpad_instruction (C_LI (i14, Regidx ti_a4)) = false)
      by vm_refl.
    assert (Hdecf_14 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x577d : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (ITYPE (sign_extend' 12 i14, Regidx cli_rs1,
                                      Regidx ti_a4, ADDI)), s))).
    { intros t _ HC _ _ _. exists (C_LI (i14, Regidx ti_a4)). split_and!.
      - exact (kd_577d t HC).
      - exact Hlpad_14.
      - exact Hexp_14. }
    iApply (wwp_addi_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc14) 4)
              ti_pc14 (mword_of_int 0x577d) cli_rs1 ti_a4 (sign_extend' 12 i14)
              (C_LI (i14, Regidx ti_a4)) (ti_m13 m sp0 menv0) ti_pc14
              pmpcfg1 q D_m D_none dstateM ws5
              Hgid Hpmp Hal2_14 eq_refl Hnz_a4
              Hdecf_14 ti_agree D_m_mi Hgood_14 Hdec_14 Hgood0_14 Hexp_14
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs14 Hhws").
    iIntros (ws6) "%Hle6 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite Hx0_14 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0))
             with (ti_m14 m sp0 menv0)) in "Hfile".
    assert (P5 : add_vec_int ti_pc14 2 = ti_pc15) by vm_refl.
    iEval (rewrite P5) in "Hpc". iEval (rewrite P5) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 15. c.slli a4, 63  (F_RVC 0x177e, SHIFTIOP SLLI) ---- *)
    assert (L15a4 : ti_m14 m sp0 menv0 !!! Regidx ti_a4 = cli_wval i14)
      by (ti_unfold; ti_look).
    assert (Hal2_15 : is_aligned_vaddr (Virtaddr ti_pc15) 2 = true)
      by vm_refl.
    assert (Hram_15 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc15 j))
      by ram_win.
    assert (Hbytes_15 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0xe + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0xe)) j)) by kb_win.
    assert (Hsub_15 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0xe)) 15 0
                      = (mword_of_int 0x177e : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_15 : isRVC (mword_of_int 0x177e : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc15 (F_RVC (mword_of_int 0x177e))) as "#Hbs15".
    { iApply (winstr_bytes_of_text kbs ti_pc15 (F_RVC (mword_of_int 0x177e))
                (kb_word_at (KernelSyms.timerinit + 0xe)) Hal2_15
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_15 (conj Hsub_15 Hrvc_15) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0xe)
        (kb_word_at (KernelSyms.timerinit + 0xe)) Hcov Hbytes_15). }
    assert (Hgood_15 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x177e : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_15 : exec (ext_decode_compressed (mword_of_int 0x177e : mword 16)) dstateM
                      = Some (C_SLLI (sh15, Regidx ti_a4), dstateM))
      by vm_refl.
    assert (Hgood0_15 : forall s : mstate,
              goodb0 D_none (execute (C_SLLI (sh15, Regidx ti_a4))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_15 : forall s : mstate, exec (execute (C_SLLI (sh15, Regidx ti_a4))) s
                = Some (ExecuteAs (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)), s)).
    exact (exec_execute_C_SLLI sh15 (Regidx ti_a4)).
    assert (Hlpad_15 : is_lpad_instruction (C_SLLI (sh15, Regidx ti_a4)) = false)
      by vm_refl.
    assert (Hdecf_15 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x177e : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)), s))).
    { intros t _ HC _ _ _. exists (C_SLLI (sh15, Regidx ti_a4)). split_and!.
      - exact (kd_177e t HC).
      - exact Hlpad_15.
      - exact Hexp_15. }
    iApply (wwp_slli_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc15) 4)
              ti_pc15 (mword_of_int 0x177e) ti_a4 ti_a4 sh15
              (C_SLLI (sh15, Regidx ti_a4)) (ti_m14 m sp0 menv0) ti_pc15
              pmpcfg1 q D_m D_none dstateM ws6
              Hgid Hpmp Hal2_15 eq_refl Hnz_a4
              Hdecf_15 ti_agree D_m_mi Hgood_15 Hdec_15 Hgood0_15 Hexp_15
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs15 Hhws").
    iIntros (ws7) "%Hle7 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite L15a4 Hb63) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0))
             with (ti_m15 m sp0 menv0)) in "Hfile".
    assert (P6 : add_vec_int ti_pc15 2 = ti_pc16) by vm_refl.
    iEval (rewrite P6) in "Hpc". iEval (rewrite P6) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 16. c.or a5, a4  (F_RVC 0x8fd9, RTYPE OR) ---- *)
    assert (L16a5 : ti_m15 m sp0 menv0 !!! Regidx ti_a5 = menv0)
      by (ti_unfold; ti_look).
    assert (L16a4 : ti_m15 m sp0 menv0 !!! Regidx ti_a4 = ti_bit63)
      by (ti_unfold; ti_look).
    assert (Hal2_16 : is_aligned_vaddr (Virtaddr ti_pc16) 2 = true)
      by vm_refl.
    assert (Hram_16 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc16 j))
      by ram_win.
    assert (Hbytes_16 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x10 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x10)) j)) by kb_win.
    assert (Hsub_16 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x10)) 15 0
                      = (mword_of_int 0x8fd9 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_16 : isRVC (mword_of_int 0x8fd9 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc16 (F_RVC (mword_of_int 0x8fd9))) as "#Hbs16".
    { iApply (winstr_bytes_of_text kbs ti_pc16 (F_RVC (mword_of_int 0x8fd9))
                (kb_word_at (KernelSyms.timerinit + 0x10)) Hal2_16
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_16 (conj Hsub_16 Hrvc_16) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x10)
        (kb_word_at (KernelSyms.timerinit + 0x10)) Hcov Hbytes_16). }
    assert (Hgood_16 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_16 : exec (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16)) dstateM
                      = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), dstateM))
      by vm_refl.
    assert (Hgood0_16 : forall s : mstate,
              goodb0 D_none
                (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
              = true) by (intro s; vm_compute; reflexivity).
    assert (Hexp_16 : forall s : mstate,
              exec (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
              = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)), s)).
    { intro s. rewrite (exec_execute_C_OR (Cregidx (mword_of_int 7)) (Cregidx (mword_of_int 6))).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    assert (Hlpad_16 : is_lpad_instruction
              (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))) = false)
      by vm_refl.
    assert (Hdecf_16 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x8fd9 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)), s))).
    { intros t _ HC _ _ _.
      exists (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))). split_and!.
      - exact (kd_8fd9 t HC).
      - exact Hlpad_16.
      - exact Hexp_16. }
    iApply (wwp_or_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc16) 4)
              ti_pc16 (mword_of_int 0x8fd9) ti_a4 ti_a5 ti_a5
              (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
              (ti_m15 m sp0 menv0) ti_pc16 pmpcfg1 q D_m D_none dstateM ws7
              Hgid Hpmp Hal2_16 eq_refl Hnz_a5
              Hdecf_16 ti_agree D_m_mi Hgood_16 Hdec_16 Hgood0_16 Hexp_16
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs16 Hhws").
    iIntros (ws8) "%Hle8 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite L16a5 L16a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menv0 ti_bit63)]>
                     (ti_m15 m sp0 menv0))
             with (ti_m16 m sp0 menv0)) in "Hfile".
    assert (P7 : add_vec_int ti_pc16 2 = ti_pc17) by vm_refl.
    iEval (rewrite P7) in "Hpc". iEval (rewrite P7) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 17. csrw menvcfg, a5  (F_Base 0x30a79073) ---- *)
    assert (L17a5 : ti_m16 m sp0 menv0 !!! Regidx ti_a5 = ti_menv1 menv0)
      by (ti_unfold; ti_look).
    assert (Hal2_17 : is_aligned_vaddr (Virtaddr ti_pc17) 2 = true)
      by vm_refl.
    assert (Hram_17 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc17 j))
      by ram_win.
    assert (Hbytes_17 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x12 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x30a79073 : mword 32) j)) by kb_win.
    assert (HnotRVC_17 : isRVC (subrange_vec_dec (mword_of_int 0x30a79073 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc17 (F_Base (mword_of_int 0x30a79073))) as "#Hbs17".
    { iApply (winstr_bytes_of_text kbs ti_pc17 (F_Base (mword_of_int 0x30a79073))
                (mword_of_int 0x30a79073) Hal2_17
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_17 (conj eq_refl HnotRVC_17) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x12)
        (mword_of_int 0x30a79073) Hcov Hbytes_17). }
    assert (Hgood_17 : goodb0 D_m (ext_decode (mword_of_int 0x30a79073 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_17 : exec (ext_decode (mword_of_int 0x30a79073 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), dstateM))
      by vm_refl.
    assert (Hdecf_17 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x30a79073 : mword 32))) t
         = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_30a79073 t Hmi Hcfg). }
    iDestruct (gpr_file_lookup_acc (ti_m16 m sp0 menv0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb17]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_menvcfg_leaf (is_aligned_vaddr (Virtaddr ti_pc17) 4)
              ti_pc17 (mword_of_int 0x30a79073) ti_a5 menv0
              (ti_m16 m sp0 menv0 (Regidx ti_a5)) ti_pc17
              pmpcfg1 q D_m dstateM ws8
              Hgid Hpmp Hal2_17 eq_refl Hnz_a5
              Hdecf_17 ti_agree D_m_mi Hgood_17 Hdec_17
              with "Hmm Hpmpc Hpc Hnpc Ha5c Hmenv Hbs17 Hhws").
    iIntros (ws9) "%Hle9 Hmm Hpmpc [Hpc Hnpc] Ha5c Hmenv Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb17" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m16 m sp0 menv0) (Regidx ti_a5)) L17a5) in "Hmenv".
    assert (P8 : add_vec_int ti_pc17 4 = ti_pc18) by vm_refl.
    iEval (rewrite P8) in "Hpc". iEval (rewrite P8) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 18. csrr a5, mcounteren  (F_Base 0x306027f3) ---- *)
    assert (Hal2_18 : is_aligned_vaddr (Virtaddr ti_pc18) 2 = true)
      by vm_refl.
    assert (Hram_18 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc18 j))
      by ram_win.
    assert (Hbytes_18 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x16 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x306027f3 : mword 32) j)) by kb_win.
    assert (HnotRVC_18 : isRVC (subrange_vec_dec (mword_of_int 0x306027f3 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc18 (F_Base (mword_of_int 0x306027f3))) as "#Hbs18".
    { iApply (winstr_bytes_of_text kbs ti_pc18 (F_Base (mword_of_int 0x306027f3))
                (mword_of_int 0x306027f3) Hal2_18
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_18 (conj eq_refl HnotRVC_18) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x16)
        (mword_of_int 0x306027f3) Hcov Hbytes_18). }
    assert (Hgood_18 : goodb0 D_m (ext_decode (mword_of_int 0x306027f3 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_18 : exec (ext_decode (mword_of_int 0x306027f3 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS), dstateM))
      by vm_refl.
    assert (Hdecf_18 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x306027f3 : mword 32))) t
         = Some (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_306027f3 t Hmi Hcfg). }
    iDestruct (gpr_file_insert_acc (ti_m16 m sp0 menv0) (Regidx ti_a5)
                 (regval_into_reg (zero_extend' 64 mcen0)) with "Hfile") as "[Ha5c Hfins18]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_mcounteren_leaf (is_aligned_vaddr (Virtaddr ti_pc18) 4)
              ti_pc18 (mword_of_int 0x306027f3) ti_a5 mcen0
              (ti_m16 m sp0 menv0 (Regidx ti_a5)) ti_pc18 pmpcfg1 q D_m dstateM ws9
              Hgid Hpmp Hal2_18 eq_refl Hnz_a5
              Hdecf_18 ti_agree D_m_mi Hgood_18 Hdec_18
              with "Hmm Hpmpc Hpc Hnpc Hmcen Ha5c Hbs18 Hhws").
    iIntros (ws10) "%Hle10 Hmm Hpmpc [Hpc Hnpc] Ha5c Hmcen Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins18" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]>
                     (ti_m16 m sp0 menv0))
             with (ti_m18 m sp0 menv0 mcen0)) in "Hfile".
    assert (P9 : add_vec_int ti_pc18 4 = ti_pc19) by vm_refl.
    iEval (rewrite P9) in "Hpc". iEval (rewrite P9) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 19. ori a5, a5, 2  (F_Base 0x0027e793) ---- *)
    assert (L19a5 : ti_m18 m sp0 menv0 mcen0 !!! Regidx ti_a5 = zero_extend' 64 mcen0)
      by (ti_unfold; ti_look).
    assert (Hal2_19 : is_aligned_vaddr (Virtaddr ti_pc19) 2 = true)
      by vm_refl.
    assert (Hram_19 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc19 j))
      by ram_win.
    assert (Hbytes_19 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x1a + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x0027e793 : mword 32) j)) by kb_win.
    assert (HnotRVC_19 : isRVC (subrange_vec_dec (mword_of_int 0x0027e793 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc19 (F_Base (mword_of_int 0x0027e793))) as "#Hbs19".
    { iApply (winstr_bytes_of_text kbs ti_pc19 (F_Base (mword_of_int 0x0027e793))
                (mword_of_int 0x0027e793) Hal2_19
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_19 (conj eq_refl HnotRVC_19) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x1a)
        (mword_of_int 0x0027e793) Hcov Hbytes_19). }
    assert (Hgood_19 : goodb0 D_m (ext_decode (mword_of_int 0x0027e793 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_19 : exec (ext_decode (mword_of_int 0x0027e793 : mword 32)) dstateM
                      = Some (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI), dstateM))
      by vm_refl.
    assert (Hdecf_19 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x0027e793 : mword 32))) t
         = Some (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_0027e793 t Hmi Hcfg). }
    iApply (wwp_ori_leaf (is_aligned_vaddr (Virtaddr ti_pc19) 4)
              ti_pc19 (mword_of_int 0x0027e793) ti_a5 ti_a5 i19
              (ti_m18 m sp0 menv0 mcen0) ti_pc19 pmpcfg1 q D_m dstateM ws10
              Hgid Hpmp Hal2_19 eq_refl Hnz_a5
              Hdecf_19 ti_agree D_m_mi Hgood_19 Hdec_19
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs19 Hhws").
    iIntros (ws11) "%Hle11 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite L19a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19))]>
                     (ti_m18 m sp0 menv0 mcen0))
             with (ti_m19 m sp0 menv0 mcen0)) in "Hfile".
    assert (P10 : add_vec_int ti_pc19 4 = ti_pc20) by vm_refl.
    iEval (rewrite P10) in "Hpc". iEval (rewrite P10) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 20. csrw mcounteren, a5  (F_Base 0x30679073) ---- *)
    assert (L20a5 : ti_m19 m sp0 menv0 mcen0 !!! Regidx ti_a5 = ti_mcen1 mcen0)
      by (ti_unfold; ti_look).
    assert (Hal2_20 : is_aligned_vaddr (Virtaddr ti_pc20) 2 = true)
      by vm_refl.
    assert (Hram_20 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc20 j))
      by ram_win.
    assert (Hbytes_20 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x1e + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x30679073 : mword 32) j)) by kb_win.
    assert (HnotRVC_20 : isRVC (subrange_vec_dec (mword_of_int 0x30679073 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc20 (F_Base (mword_of_int 0x30679073))) as "#Hbs20".
    { iApply (winstr_bytes_of_text kbs ti_pc20 (F_Base (mword_of_int 0x30679073))
                (mword_of_int 0x30679073) Hal2_20
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_20 (conj eq_refl HnotRVC_20) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x1e)
        (mword_of_int 0x30679073) Hcov Hbytes_20). }
    assert (Hgood_20 : goodb0 D_m (ext_decode (mword_of_int 0x30679073 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_20 : exec (ext_decode (mword_of_int 0x30679073 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW), dstateM))
      by vm_refl.
    assert (Hdecf_20 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x30679073 : mword 32))) t
         = Some (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_30679073 t Hmi Hcfg). }
    iDestruct (gpr_file_lookup_acc (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb20]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mcounteren_leaf (is_aligned_vaddr (Virtaddr ti_pc20) 4)
              ti_pc20 (mword_of_int 0x30679073) ti_a5 mcen0
              (ti_m19 m sp0 menv0 mcen0 (Regidx ti_a5)) ti_pc20
              pmpcfg1 q D_m dstateM ws11
              Hgid Hpmp Hal2_20 eq_refl Hnz_a5
              Hdecf_20 ti_agree D_m_mi Hgood_20 Hdec_20
              with "Hmm Hpmpc Hpc Hnpc Ha5c Hmcen Hbs20 Hhws").
    iIntros (ws12) "%Hle12 Hmm Hpmpc [Hpc Hnpc] Ha5c Hmcen Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb20" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5)) L20a5) in "Hmcen".
    assert (P11 : add_vec_int ti_pc20 4 = ti_pc21) by vm_refl.
    iEval (rewrite P11) in "Hpc". iEval (rewrite P11) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 21. csrr a5, time  (F_Base 0xc01027f3) ---- *)
    assert (Hal2_21 : is_aligned_vaddr (Virtaddr ti_pc21) 2 = true)
      by vm_refl.
    assert (Hram_21 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc21 j))
      by ram_win.
    assert (Hbytes_21 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x22 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0xc01027f3 : mword 32) j)) by kb_win.
    assert (HnotRVC_21 : isRVC (subrange_vec_dec (mword_of_int 0xc01027f3 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc21 (F_Base (mword_of_int 0xc01027f3))) as "#Hbs21".
    { iApply (winstr_bytes_of_text kbs ti_pc21 (F_Base (mword_of_int 0xc01027f3))
                (mword_of_int 0xc01027f3) Hal2_21
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_21 (conj eq_refl HnotRVC_21) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x22)
        (mword_of_int 0xc01027f3) Hcov Hbytes_21). }
    assert (Hgood_21 : goodb0 D_m (ext_decode (mword_of_int 0xc01027f3 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_21 : exec (ext_decode (mword_of_int 0xc01027f3 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS), dstateM))
      by vm_refl.
    assert (Hdecf_21 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0xc01027f3 : mword 32))) t
         = Some (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_c01027f3 t Hmi Hcfg). }
    iDestruct (gpr_file_reinsert_acc (ti_m19 m sp0 menv0 mcen0) (Regidx ti_a5)
                 with "Hfile") as "[Ha5c Hfins21]".
    (* the leaf quantifies the read value [tv] itself, unknown until it
       returns it -- [gpr_file_reinsert_acc]'s wand stays open over the
       eventual value, unlike [gpr_file_insert_acc]'s fixed one. *)
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_time_leaf (is_aligned_vaddr (Virtaddr ti_pc21) 4)
              ti_pc21 (mword_of_int 0xc01027f3) ti_a5
              (ti_m19 m sp0 menv0 mcen0 (Regidx ti_a5)) ti_pc21 pmpcfg1 q D_m dstateM ws12
              Hgid Hpmp Hal2_21 eq_refl Hnz_a5
              Hdecf_21 ti_agree D_m_mi Hgood_21 Hdec_21
              with "Hmm Hpmpc Hpc Hnpc Ha5c Hbs21 Hhws").
    iIntros (tv ws13) "%Hle13 Hmm Hpmpc [Hpc Hnpc] Ha5c Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins21" $! (regval_into_reg tv) with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg tv]> (ti_m19 m sp0 menv0 mcen0))
             with (ti_m21 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P12 : add_vec_int ti_pc21 4 = ti_pc22) by vm_refl.
    iEval (rewrite P12) in "Hpc". iEval (rewrite P12) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 22. lui a4, 0xf4  (F_Base 0x000f4737) ---- *)
    assert (Hal2_22 : is_aligned_vaddr (Virtaddr ti_pc22) 2 = true)
      by vm_refl.
    assert (Hram_22 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc22 j))
      by ram_win.
    assert (Hbytes_22 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x26 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x000f4737 : mword 32) j)) by kb_win.
    assert (HnotRVC_22 : isRVC (subrange_vec_dec (mword_of_int 0x000f4737 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc22 (F_Base (mword_of_int 0x000f4737))) as "#Hbs22".
    { iApply (winstr_bytes_of_text kbs ti_pc22 (F_Base (mword_of_int 0x000f4737))
                (mword_of_int 0x000f4737) Hal2_22
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_22 (conj eq_refl HnotRVC_22) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x26)
        (mword_of_int 0x000f4737) Hcov Hbytes_22). }
    assert (Hgood_22 : goodb0 D_m (ext_decode (mword_of_int 0x000f4737 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_22 : exec (ext_decode (mword_of_int 0x000f4737 : mword 32)) dstateM
                      = Some (UTYPE (i22, Regidx ti_a4, LUI), dstateM))
      by vm_refl.
    assert (Hdecf_22 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x000f4737 : mword 32))) t
         = Some (UTYPE (i22, Regidx ti_a4, LUI), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_000f4737 t Hmi Hcfg). }
    iApply (wwp_lui_leaf (is_aligned_vaddr (Virtaddr ti_pc22) 4)
              ti_pc22 (mword_of_int 0x000f4737) ti_a4 i22
              (ti_m21 m sp0 menv0 mcen0 tv) ti_pc22 pmpcfg1 q D_m dstateM ws13
              Hgid Hpmp Hal2_22 eq_refl Hnz_a4
              Hdecf_22 ti_agree D_m_mi Hgood_22 Hdec_22
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs22 Hhws").
    iIntros (ws14) "%Hle14 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival i22)]>
                     (ti_m21 m sp0 menv0 mcen0 tv))
             with (ti_m22 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P13 : add_vec_int ti_pc22 4 = ti_pc23) by vm_refl.
    iEval (rewrite P13) in "Hpc". iEval (rewrite P13) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 23. addi a4, a4, 576  (F_Base 0x24070713) ---- *)
    assert (L23a4 : ti_m22 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = luival i22)
      by (ti_unfold; ti_look).
    assert (Hal2_23 : is_aligned_vaddr (Virtaddr ti_pc23) 2 = true)
      by vm_refl.
    assert (Hram_23 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc23 j))
      by ram_win.
    assert (Hbytes_23 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2a + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x24070713 : mword 32) j)) by kb_win.
    assert (HnotRVC_23 : isRVC (subrange_vec_dec (mword_of_int 0x24070713 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc23 (F_Base (mword_of_int 0x24070713))) as "#Hbs23".
    { iApply (winstr_bytes_of_text kbs ti_pc23 (F_Base (mword_of_int 0x24070713))
                (mword_of_int 0x24070713) Hal2_23
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_23 (conj eq_refl HnotRVC_23) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2a)
        (mword_of_int 0x24070713) Hcov Hbytes_23). }
    assert (Hgood_23 : goodb0 D_m (ext_decode (mword_of_int 0x24070713 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_23 : exec (ext_decode (mword_of_int 0x24070713 : mword 32)) dstateM
                      = Some (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI), dstateM))
      by vm_refl.
    assert (Hdecf_23 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x24070713 : mword 32))) t
         = Some (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_24070713 t Hmi Hcfg). }
    iApply (wwp_addi_leaf (is_aligned_vaddr (Virtaddr ti_pc23) 4)
              ti_pc23 (mword_of_int 0x24070713) ti_a4 ti_a4 i23
              (ti_m22 m sp0 menv0 mcen0 tv) ti_pc23 pmpcfg1 q D_m dstateM ws14
              Hgid Hpmp Hal2_23 eq_refl Hnz_a4
              Hdecf_23 ti_agree D_m_mi Hgood_23 Hdec_23
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs23 Hhws").
    iIntros (ws15) "%Hle15 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite L23a4 Hival) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_interval]>
                     (ti_m22 m sp0 menv0 mcen0 tv))
             with (ti_m23 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P14 : add_vec_int ti_pc23 4 = ti_pc24) by vm_refl.
    iEval (rewrite P14) in "Hpc". iEval (rewrite P14) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 24. c.add a5, a4  (F_RVC 0x97ba, RTYPE ADD) ---- *)
    assert (L24a5 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = tv)
      by (ti_unfold; ti_look).
    assert (L24a4 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = ti_interval)
      by (ti_unfold; ti_look).
    assert (Hal2_24 : is_aligned_vaddr (Virtaddr ti_pc24) 2 = true)
      by vm_refl.
    assert (Hram_24 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc24 j))
      by ram_win.
    assert (Hbytes_24 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2e + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x2e)) j)) by kb_win.
    assert (Hsub_24 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x2e)) 15 0
                      = (mword_of_int 0x97ba : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_24 : isRVC (mword_of_int 0x97ba : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc24 (F_RVC (mword_of_int 0x97ba))) as "#Hbs24".
    { iApply (winstr_bytes_of_text kbs ti_pc24 (F_RVC (mword_of_int 0x97ba))
                (kb_word_at (KernelSyms.timerinit + 0x2e)) Hal2_24
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_24 (conj Hsub_24 Hrvc_24) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2e)
        (kb_word_at (KernelSyms.timerinit + 0x2e)) Hcov Hbytes_24). }
    assert (Hgood_24 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x97ba : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_24 : exec (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) dstateM
                      = Some (C_ADD (Regidx ti_a5, Regidx ti_a4), dstateM))
      by vm_refl.
    assert (Hgood0_24 : forall s : mstate,
              goodb0 D_none (execute (C_ADD (Regidx ti_a5, Regidx ti_a4))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_24 : forall s : mstate,
              exec (execute (C_ADD (Regidx ti_a5, Regidx ti_a4))) s
              = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)), s)).
    exact (exec_execute_C_ADD (Regidx ti_a5) (Regidx ti_a4)).
    assert (Hlpad_24 : is_lpad_instruction (C_ADD (Regidx ti_a5, Regidx ti_a4)) = false)
      by vm_refl.
    assert (Hdecf_24 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x97ba : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)), s))).
    { intros t _ HC _ _ _. exists (C_ADD (Regidx ti_a5, Regidx ti_a4)). split_and!.
      - exact (kd_97ba t HC).
      - exact Hlpad_24.
      - exact Hexp_24. }
    iApply (wwp_add_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc24) 4)
              ti_pc24 (mword_of_int 0x97ba) ti_a4 ti_a5 ti_a5
              (C_ADD (Regidx ti_a5, Regidx ti_a4)) (ti_m23 m sp0 menv0 mcen0 tv) ti_pc24
              pmpcfg1 q D_m D_none dstateM ws15
              Hgid Hpmp Hal2_24 eq_refl Hnz_a5
              Hdecf_24 ti_agree D_m_mi Hgood_24 Hdec_24 Hgood0_24 Hexp_24
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs24 Hhws").
    iIntros (ws16) "%Hle16 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite L24a5 L24a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (add_vec tv ti_interval)]>
                     (ti_m23 m sp0 menv0 mcen0 tv))
             with (ti_m24 m sp0 menv0 mcen0 tv)) in "Hfile".
    assert (P15 : add_vec_int ti_pc24 2 = ti_pc25) by vm_refl.
    iEval (rewrite P15) in "Hpc". iEval (rewrite P15) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 25. csrw stimecmp, a5  (F_Base 0x14d79073, opens clock_inv) ---- *)
    assert (L25a5 : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = ti_deadline tv)
      by (ti_unfold; ti_look).
    assert (Hal2_25 : is_aligned_vaddr (Virtaddr ti_pc25) 2 = true)
      by vm_refl.
    assert (Hram_25 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc25 j))
      by ram_win.
    assert (Hbytes_25 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x30 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0x14d79073 : mword 32) j)) by kb_win.
    assert (HnotRVC_25 : isRVC (subrange_vec_dec (mword_of_int 0x14d79073 : mword 32) 15 0)
                          = false) by vm_refl.
    iAssert (winstr_bytes ti_pc25 (F_Base (mword_of_int 0x14d79073))) as "#Hbs25".
    { iApply (winstr_bytes_of_text kbs ti_pc25 (F_Base (mword_of_int 0x14d79073))
                (mword_of_int 0x14d79073) Hal2_25
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_25 (conj eq_refl HnotRVC_25) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x30)
        (mword_of_int 0x14d79073) Hcov Hbytes_25). }
    assert (Hgood_25 : goodb0 D_m (ext_decode (mword_of_int 0x14d79073 : mword 32))
                          dstateM = true) by vm_refl.
    assert (Hdec_25 : exec (ext_decode (mword_of_int 0x14d79073 : mword 32)) dstateM
                      = Some (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW), dstateM))
      by vm_refl.
    assert (Hdecf_25 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base (mword_of_int 0x14d79073 : mword 32))) t
         = Some (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW), t)).
    { intros t _ _ _ Hmi Hcfg. exact (kd_14d79073 t Hmi Hcfg). }
    iDestruct (gpr_file_lookup_acc (ti_m24 m sp0 menv0 mcen0 tv) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb25]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_stimecmp_leaf (is_aligned_vaddr (Virtaddr ti_pc25) 4)
              ti_pc25 (mword_of_int 0x14d79073) ti_a5
              (ti_m24 m sp0 menv0 mcen0 tv (Regidx ti_a5)) ti_pc25
              stimecmp0 pmpcfg1 q D_m dstateM ws16
              Hgid Hpmp Hal2_25 eq_refl Hnz_a5
              Hdecf_25 ti_agree D_m_mi Hgood_25 Hdec_25
              with "Hmm Hpmpc Hpc Hnpc Ha5c Hstc Hbs25 Hhws").
    iIntros (ws17) "%Hle17 Hmm Hpmpc [Hpc Hnpc] Ha5c Hstc Hhws".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb25" with "Ha5c") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_m24 m sp0 menv0 mcen0 tv) (Regidx ti_a5)) L25a5) in "Hstc".
    assert (P16 : add_vec_int ti_pc25 4 = ti_pc26) by vm_refl.
    iEval (rewrite P16) in "Hpc". iEval (rewrite P16) in "Hnpc".
    (* the two frame words have not moved since steps 10/11: bump [Hstkra]
       (last touched at [ws2]) and [Hstks0] (last touched at [ws3]) to [ws17] *)
    iDestruct (vwp_hold_mono _ ws2 ws17 (transitivity Hle3 (transitivity Hle4
                 (transitivity Hle5 (transitivity Hle6 (transitivity Hle7
                 (transitivity Hle8 (transitivity Hle9 (transitivity Hle10
                 (transitivity Hle11 (transitivity Hle12 (transitivity Hle13
                 (transitivity Hle14 (transitivity Hle15 (transitivity Hle16
                 Hle17)))))))))))))) with "Hstkra") as "Hstkra".
    iDestruct (vwp_hold_mono _ ws3 ws17 (transitivity Hle4
                 (transitivity Hle5 (transitivity Hle6 (transitivity Hle7
                 (transitivity Hle8 (transitivity Hle9 (transitivity Hle10
                 (transitivity Hle11 (transitivity Hle12 (transitivity Hle13
                 (transitivity Hle14 (transitivity Hle15 (transitivity Hle16
                 Hle17))))))))))))) with "Hstks0") as "Hstks0".

    (* ==================================================================== *)
    (* ---- 26. c.ldsp ra, 8(sp)  (F_RVC 0x60a2, LOAD, WRITTEN TOR) ---- *)
    assert (L26sp : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (L26ra : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    assert (Hal2_26 : is_aligned_vaddr (Virtaddr ti_pc26) 2 = true)
      by vm_refl.
    assert (Hram4_26 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc26 j))
      by ram_win.
    assert (Hbytes_26 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x34 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x34)) j)) by kb_win.
    assert (Hsub_26 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x34)) 15 0
                      = (mword_of_int 0x60a2 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_26 : isRVC (mword_of_int 0x60a2 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc26 (F_RVC (mword_of_int 0x60a2))) as "#Hbs26".
    { iApply (winstr_bytes_of_text kbs ti_pc26 (F_RVC (mword_of_int 0x60a2))
                (kb_word_at (KernelSyms.timerinit + 0x34)) Hal2_26
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram4_26 (conj Hsub_26 Hrvc_26) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x34)
        (kb_word_at (KernelSyms.timerinit + 0x34)) Hcov Hbytes_26). }
    assert (Hgood_26 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x60a2 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_26 : exec (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) dstateM
                      = Some (C_LDSP (u10, Regidx ti_ra), dstateM))
      by vm_refl.
    assert (Hgood0_26 : forall s : mstate,
              goodb0 D_none (execute (C_LDSP (u10, Regidx ti_ra))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_26 : forall s : mstate, exec (execute (C_LDSP (u10, Regidx ti_ra))) s
                = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")),
                                        Regidx csp_rs1, Regidx ti_ra, false, 8)), s))
      by exact (exec_execute_C_LDSP u10 (Regidx ti_ra)).
    assert (Hlpad_26 : is_lpad_instruction (C_LDSP (u10, Regidx ti_ra)) = false)
      by vm_refl.
    assert (Hdecf_26 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x60a2 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")),
                                     Regidx csp_rs1, Regidx ti_ra, false, 8)), s))).
    { intros t _ HC _ _ _. exists (C_LDSP (u10, Regidx ti_ra)). split_and!.
      - exact (kd_60a2 t HC).
      - exact Hlpad_26.
      - exact Hexp_26. }
    iDestruct (gpr_file_acc_2 (ti_m24 m sp0 menv0 mcen0 tv) (Regidx csp_rs1) (Regidx ti_ra)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hrac & Hfacc26)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m24 m sp0 menv0 mcen0 tv)
             (Regidx csp_rs1)) L26sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_ld8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc26) 4)
              ti_pc26 (mword_of_int 0x60a2) csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000")))
              (C_LDSP (u10, Regidx ti_ra)) (ti_ea_ra sp0) ra0 (DfracOwn 1) q
              pmpcfg1 pmpaddrs (ti_sp1 sp0) (ti_m24 m sp0 menv0 mcen0 tv (Regidx ti_ra))
              ti_pc26 D_m D_none dstateM ws17
              Hgid Hpmp Htor_ra Hal2_26 eq_refl Hnz_sp Hnz_ra eq_refl
              Hram_ra Hdecf_26 ti_agree D_m_mi Hgood_26 Hdec_26 Hgood0_26 Hexp_26
              with "Hmm Hpmpc Hpaddr Hpc Hnpc Hspc Hrac Hbs26 Hhws Hstkra").
    iIntros (ws18) "%Hle18 Hmm Hpmpc Hpaddr [Hpc Hnpc] Hspc Hrac Hhws Hstkra".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfacc26" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (regfile_upd_drop_outer' (ti_m24 m sp0 menv0 mcen0 tv) (Regidx csp_rs1) (Regidx ti_ra)
                      (ti_sp1 sp0) (regval_into_reg ra0) ltac:(ti_reg_neq) L26sp)) in "Hfile".
    iEval (change (<[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 tv))
             with (ti_m26 m sp0 menv0 mcen0 tv ra0)) in "Hfile".
    assert (P17 : add_vec_int ti_pc26 2 = ti_pc27) by vm_refl.
    iEval (rewrite P17) in "Hpc". iEval (rewrite P17) in "Hnpc".
    (* [Hstks0] has not moved since step 25: bump to [ws18] *)
    iDestruct (vwp_hold_mono _ ws17 ws18 Hle18 with "Hstks0") as "Hstks0".

    (* ==================================================================== *)
    (* ---- 27. c.ldsp s0, 0(sp)  (F_RVC 0x6402, LOAD, WRITTEN TOR) ---- *)
    assert (L27sp : ti_m26 m sp0 menv0 mcen0 tv ra0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hal2_27 : is_aligned_vaddr (Virtaddr ti_pc27) 2 = true)
      by vm_refl.
    assert (Hram4_27 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc27 j))
      by ram_win.
    assert (Hbytes_27 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x36 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x36)) j)) by kb_win.
    assert (Hsub_27 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x36)) 15 0
                      = (mword_of_int 0x6402 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_27 : isRVC (mword_of_int 0x6402 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc27 (F_RVC (mword_of_int 0x6402))) as "#Hbs27".
    { iApply (winstr_bytes_of_text kbs ti_pc27 (F_RVC (mword_of_int 0x6402))
                (kb_word_at (KernelSyms.timerinit + 0x36)) Hal2_27
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram4_27 (conj Hsub_27 Hrvc_27) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x36)
        (kb_word_at (KernelSyms.timerinit + 0x36)) Hcov Hbytes_27). }
    assert (Hgood_27 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x6402 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_27 : exec (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) dstateM
                      = Some (C_LDSP (u11, Regidx ti_s0), dstateM))
      by vm_refl.
    assert (Hgood0_27 : forall s : mstate,
              goodb0 D_none (execute (C_LDSP (u11, Regidx ti_s0))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_27 : forall s : mstate, exec (execute (C_LDSP (u11, Regidx ti_s0))) s
                = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")),
                                        Regidx csp_rs1, Regidx ti_s0, false, 8)), s))
      by exact (exec_execute_C_LDSP u11 (Regidx ti_s0)).
    assert (Hlpad_27 : is_lpad_instruction (C_LDSP (u11, Regidx ti_s0)) = false)
      by vm_refl.
    assert (Hdecf_27 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x6402 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")),
                                     Regidx csp_rs1, Regidx ti_s0, false, 8)), s))).
    { intros t _ HC _ _ _. exists (C_LDSP (u11, Regidx ti_s0)). split_and!.
      - exact (kd_6402 t HC).
      - exact Hlpad_27.
      - exact Hexp_27. }
    iDestruct (gpr_file_acc_2 (ti_m26 m sp0 menv0 mcen0 tv ra0) (Regidx csp_rs1) (Regidx ti_s0)
                 ltac:(ti_reg_neq) with "Hfile") as "(Hspc & Hs0c & Hfacc27)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp) -(rf_lookup (ti_m26 m sp0 menv0 mcen0 tv ra0)
             (Regidx csp_rs1)) L27sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iApply (wwp_ld8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc27) 4)
              ti_pc27 (mword_of_int 0x6402) csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000")))
              (C_LDSP (u11, Regidx ti_s0)) (ti_ea_s0 sp0) s00 (DfracOwn 1) q
              pmpcfg1 pmpaddrs (ti_sp1 sp0)
              (ti_m26 m sp0 menv0 mcen0 tv ra0 (Regidx ti_s0))
              ti_pc27 D_m D_none dstateM ws18
              Hgid Hpmp Htor_s0 Hal2_27 eq_refl Hnz_sp Hnz_s0 eq_refl
              Hram_s0 Hdecf_27 ti_agree D_m_mi Hgood_27 Hdec_27 Hgood0_27 Hexp_27
              with "Hmm Hpmpc Hpaddr Hpc Hnpc Hspc Hs0c Hbs27 Hhws Hstks0").
    iIntros (ws19) "%Hle19 Hmm Hpmpc Hpaddr [Hpc Hnpc] Hspc Hs0c Hhws Hstks0".
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
    iEval (rewrite P18) in "Hpc". iEval (rewrite P18) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 28. c.addi sp, 16  (F_RVC 0x0141, ADDI) ---- *)
    assert (L28sp : ti_m27 m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hal2_28 : is_aligned_vaddr (Virtaddr ti_pc28) 2 = true)
      by vm_refl.
    assert (Hram_28 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc28 j))
      by ram_win.
    assert (Hbytes_28 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x38 + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x38)) j)) by kb_win.
    assert (Hsub_28 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x38)) 15 0
                      = (mword_of_int 0x0141 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_28 : isRVC (mword_of_int 0x0141 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc28 (F_RVC (mword_of_int 0x0141))) as "#Hbs28".
    { iApply (winstr_bytes_of_text kbs ti_pc28 (F_RVC (mword_of_int 0x0141))
                (kb_word_at (KernelSyms.timerinit + 0x38)) Hal2_28
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_28 (conj Hsub_28 Hrvc_28) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x38)
        (kb_word_at (KernelSyms.timerinit + 0x38)) Hcov Hbytes_28). }
    assert (Hgood_28 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x0141 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_28 : exec (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) dstateM
                      = Some (C_ADDI (i28, Regidx csp_rs1), dstateM))
      by vm_refl.
    assert (Hgood0_28 : forall s : mstate,
              goodb0 D_none (execute (C_ADDI (i28, Regidx csp_rs1))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_28 : forall s : mstate, exec (execute (C_ADDI (i28, Regidx csp_rs1))) s
                = Some (ExecuteAs (ITYPE (sign_extend' 12 i28, Regidx csp_rs1,
                                          Regidx csp_rs1, ADDI)), s))
      by exact (exec_execute_C_ADDI i28 (Regidx csp_rs1)).
    assert (Hlpad_28 : is_lpad_instruction (C_ADDI (i28, Regidx csp_rs1)) = false)
      by vm_refl.
    assert (Hdecf_28 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x0141 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (ITYPE (sign_extend' 12 i28, Regidx csp_rs1,
                                      Regidx csp_rs1, ADDI)), s))).
    { intros t _ HC _ _ _. exists (C_ADDI (i28, Regidx csp_rs1)). split_and!.
      - exact (kd_0141 t HC).
      - exact Hlpad_28.
      - exact Hexp_28. }
    iApply (wwp_addi_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc28) 4)
              ti_pc28 (mword_of_int 0x0141) csp_rs1 csp_rs1 (sign_extend' 12 i28)
              (C_ADDI (i28, Regidx csp_rs1)) (ti_m27 m sp0 menv0 mcen0 tv ra0 s00) ti_pc28
              pmpcfg1 q D_m D_none dstateM ws19
              Hgid Hpmp Hal2_28 eq_refl Hnz_sp
              Hdecf_28 ti_agree D_m_mi Hgood_28 Hdec_28 Hgood0_28 Hexp_28
              with "Hmm Hpmpc Hpc Hnpc Hfile Hbs28 Hhws").
    iIntros (ws20) "%Hle20 Hmm Hpmpc [Hpc Hnpc] Hfile Hhws".
    iEval (rewrite sext6_12_64 L28sp Hspres) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg sp0]>
                     (ti_m27 m sp0 menv0 mcen0 tv ra0 s00))
             with (ti_mout m sp0 menv0 mcen0 tv ra0 s00)) in "Hfile".
    assert (P19 : add_vec_int ti_pc28 2 = ti_pc29) by vm_refl.
    iEval (rewrite P19) in "Hpc". iEval (rewrite P19) in "Hnpc".

    (* ==================================================================== *)
    (* ---- 29. c.ret  (F_RVC 0x8082, JALR via c.jr ra) ---- *)
    assert (L29ra : ti_mout m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    assert (Hal2_29 : is_aligned_vaddr (Virtaddr ti_pc29) 2 = true)
      by vm_refl.
    assert (Hram_29 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ti_pc29 j))
      by ram_win.
    assert (Hbytes_29 : forall j : nat, (j < 4)%nat ->
              KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x3a + Z.of_nat j)
              = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x3a)) j)) by kb_win.
    assert (Hsub_29 : subrange_vec_dec (kb_word_at (KernelSyms.timerinit + 0x3a)) 15 0
                      = (mword_of_int 0x8082 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hrvc_29 : isRVC (mword_of_int 0x8082 : mword 16) = true)
      by vm_refl.
    iAssert (winstr_bytes ti_pc29 (F_RVC (mword_of_int 0x8082))) as "#Hbs29".
    { iApply (winstr_bytes_of_text kbs ti_pc29 (F_RVC (mword_of_int 0x8082))
                (kb_word_at (KernelSyms.timerinit + 0x3a)) Hal2_29
                ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
                Hram_29 (conj Hsub_29 Hrvc_29) with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x3a)
        (kb_word_at (KernelSyms.timerinit + 0x3a)) Hcov Hbytes_29). }
    assert (Hgood_29 : goodb0 D_m (ext_decode_compressed (mword_of_int 0x8082 : mword 16))
                          dstateM = true) by vm_refl.
    assert (Hdec_29 : exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) dstateM
                      = Some (C_JR (Regidx ti_ra), dstateM))
      by vm_refl.
    assert (Hgood0_29 : forall s : mstate,
              goodb0 D_none (execute (C_JR (Regidx ti_ra))) s = true)
      by (intro s; vm_compute; reflexivity).
    assert (Hexp_29 : forall s : mstate, exec (execute (C_JR (Regidx ti_ra))) s
                = Some (ExecuteAs (JALR (zeros' 12, Regidx ti_ra, zreg)), s))
      by exact (exec_execute_C_JR (Regidx ti_ra)).
    assert (Hlpad_29 : is_lpad_instruction (C_JR (Regidx ti_ra)) = false)
      by vm_refl.
    assert (Hdecf_29 : forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC (mword_of_int 0x8082 : mword 16))) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (JALR (zeros' 12, Regidx ti_ra, zreg)), s))).
    { intros t _ HC _ _ _. exists (C_JR (Regidx ti_ra)). split_and!.
      - exact (kd_8082 t HC).
      - exact Hlpad_29.
      - exact Hexp_29. }
    iDestruct (gpr_file_lookup_acc (ti_mout m sp0 menv0 mcen0 tv ra0 s00) (Regidx ti_ra)
                 with "Hfile") as "[Hrac Hfb29]".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_cjr_rvc_leaf (is_aligned_vaddr (Virtaddr ti_pc29) 4)
              ti_pc29 (mword_of_int 0x8082) ti_ra (C_JR (Regidx ti_ra))
              (ti_mout m sp0 menv0 mcen0 tv ra0 s00 (Regidx ti_ra)) ti_pc29
              pmpcfg1 q D_m D_none dstateM ws20
              Hgid Hpmp Hal2_29 eq_refl Hnz_ra
              Hdecf_29 ti_agree D_m_mi Hgood_29 Hdec_29 Hgood0_29 Hexp_29
              with "Hmm Hpmpc Hpc Hnpc Hrac Hbs29 Hhws").
    iIntros (ws21) "%Hle21 Hmm Hpmpc [Hpc Hnpc] Hrac Hhws".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfb29" with "Hrac") as "Hfile".
    iEval (rewrite -(rf_lookup (ti_mout m sp0 menv0 mcen0 tv ra0 s00) (Regidx ti_ra)) L29ra)
      in "Hpc".
    iEval (rewrite -(rf_lookup (ti_mout m sp0 menv0 mcen0 tv ra0 s00) (Regidx ti_ra)) L29ra)
      in "Hnpc".

    (* ==================================================================== *)
    (* re-bundle the two frame slots (+ the untouched deeper stack) at the
       FINAL view [ws21], and hand everything to the caller. *)
    pose proof (transitivity Hle19 (transitivity Hle20 Hle21)) as Hle_ra_final.
    pose proof (transitivity Hle20 Hle21) as Hle_s0_final.
    pose proof (transitivity Hle1 (transitivity Hle2 (transitivity Hle3 (transitivity Hle4
      (transitivity Hle5 (transitivity Hle6 (transitivity Hle7 (transitivity Hle8
      (transitivity Hle9 (transitivity Hle10 (transitivity Hle11 (transitivity Hle12
      (transitivity Hle13 (transitivity Hle14 (transitivity Hle15 (transitivity Hle16
      (transitivity Hle17 (transitivity Hle18 (transitivity Hle19 (transitivity Hle20
      Hle21)))))))))))))))))))) as Hle_deep_final.
    iDestruct (vwp_hold_mono _ ws18 ws21 Hle_ra_final with "Hstkra") as "Hstkra".
    iDestruct (vwp_hold_mono _ ws19 ws21 Hle_s0_final with "Hstks0") as "Hstks0".
    iDestruct (vwp_hold_mono _ ws ws21 Hle_deep_final with "Hdeep") as "Hdeep".
    iEval (rewrite Hpra) in "Hstkra". iEval (rewrite Hps0) in "Hstks0".
    iAssert (vwp_hold (wpt8 (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
                       wpt8 (pa_stk sp0 2) (DfracOwn 1) s00) ws21)
      with "[Hstkra Hstks0]" as "Htop".
    { iEval (rewrite vwp_hold_sep). iFrame. }
    iDestruct (vwp_hold_ent _ _ ws21 (stack_2_intro_ent sp0 ra0 s00) with "Htop") as "Htop".
    iAssert (vwp_hold (wstack_own_phys sp0 2 ∗ wstack_own_phys (pa_stk sp0 2) (n - 2)) ws21)
      with "[Htop Hdeep]" as "Hstk2".
    { iEval (rewrite vwp_hold_sep). iFrame. }
    iDestruct (vwp_hold_ent _ _ ws21 (wstack_own_phys_split_2 sp0 2 n Hn2) with "Hstk2")
      as "Hstk".
    iApply ("Hcont" $! tv ws21 with
              "[%] Hmm Hpmpc Hpaddr [$Hpc $Hnpc] Hfile Hmenv Hmcen Hstc Hhws Hstk").
    exact Hle_deep_final.
  Qed.

End WkTimerinitThm.
