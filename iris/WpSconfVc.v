(* WpSconfVc.v -- the SIE-AGNOSTIC VCgen block executor (interrupt-sweep
   stage 6): [wp_vc_block_s_aux]/[wp_vc_block_s] re-derived over the
   [sconf]+[sie_cap] leaves, so a VCgen-driven straight-line block runs
   whether interrupts are enabled or disabled.

   Scope: the SP-FREE fragment ([vblock_no_sp prog = true] -- no
   VScaddi16sp, and no rd-writing op with rd = sp).  An sp-moving
   instruction re-carves [sie_cap]'s stack bound, which is per-call-site
   bookkeeping: function proofs split their blocks at the sp-move and
   use [wp_caddi16sp_s_sconf]/[wp_caddi_sp_s_sconf] (WpSconfAlu.v)
   between blocks -- exactly how prologue/epilogue composition already
   works.  Everything else (the vstate denotation, [block_instrs_s],
   the vheap cells, [gpr_matches]/[agree_off] plumbing) is reused from
   VcGenS.v unchanged.                                                   *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase WpSmodeLeafBase.
Require Import SmodeCore WpSmodeGpr.
Require Import VcGen VcGenS.
Require Import KptTree SmodeCorePt WpSmodePtLeaves.
Require Import StackOwn WpSmodeSret AlignBits.
Require Import WpIntrBits WpIntrCore IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem.
Local Open Scope Z_scope.
Import Defs.

(* the sp-free guard: no op may WRITE sp inside an agnostic block. *)
Definition vop_no_sp (op : vop_s) : bool :=
  match op with
  | VScaddi _ rd | VScaddi4spn _ _ rd | VScldsp _ rd
  | VSclw _ _ rd | VScaddiw _ rd | VSld _ _ _ rd => negb (eq_vec rd csp_rs1)
  | VScsdsp _ _ | VScsw _ _ _ | VSsd _ _ _ _ => true
  | VScaddi16sp _ => false
  end.

Definition vblock_no_sp (prog : list vop_s) : bool := forallb vop_no_sp prog.

Local Lemma neq_of_eq_vec_false (a b : mword 5) :
  eq_vec a b = false -> a <> b.
Proof.
  intros Hf He. subst.
  rewrite (proj2 (eq_vec_true_iff b b) eq_refl) in Hf. discriminate.
Qed.

Section WpSconfVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_vc_block_s_sconf_aux (γ : gname) (root_ppn : mword 44)
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m m0 : gmap regidx (mword 64)) :
    vblock_no_sp prog = true ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    agree_off st.(vregs) m m0 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : gmap regidx (mword 64),
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m0 ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mf -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    revert st m. induction prog as [|op rest IH]; intros st m Hwf Hblk Hmatch Hao.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr _ Hheap Hheap4 Hcont".
      iApply ("Hcont" $! m with "[//] Hsc Hhs Hcap Htlbinv Hpc Hgpr Hheap Hheap4").
    - cbn [vc_block_s] in Hblk.
      cbn [vblock_no_sp forallb] in Hwf. apply andb_prop in Hwf as [Hnosp Hwfr].
      destruct (vc_step_s st op) as [st1|] eqn:Hstep;
        rewrite ?Hstep in Hblk; [|discriminate].
      iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr [Hi Hbi] Hheap Hheap4 Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                     |imm rs1 rd|imm rs2 rs1|imm rd
                     |rvc imm rs2 rs1|rvc imm rs1 rd|imm6]; simpl in Hstep;
        cbn [vop_no_sp] in Hnosp.
      + (* VScaddi *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rd imm m
                  Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (sign_extend' 12 imm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (sign_extend' 12 imm) H64).
          reflexivity. }
        iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi4spn *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (vpc st))
                  rdc nzimm rd m Hrdc Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (caddi4spn_imm nzimm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (caddi4spn_imm nzimm) H64).
          reflexivity. }
        iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsdsp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) uimm rs2
                  m (sval_den ρ vold)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite Hm2 -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ _ Hwfr Hblk Hmatch Hao
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScldsp *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) uimm rd
                  m (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv)
          by reflexivity.
        iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSclw *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i w32]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_clw_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rd rs1 imm
                  m (sval32_den ρ w32) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sign_extend' 64 (sval32_den ρ w32))
                       = sval_den ρ (S32 w32)) by reflexivity.
        iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsw *)
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i wold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csw_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rs2 rs1 imm
                  m (sval32_den ρ wold)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hsv : trunc32 (m !!! Regidx rs2) = sval32_den ρ (sval_trunc32 v2)).
        { rewrite sval_trunc32_den Hm2. reflexivity. }
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iApply (IH _ _ Hwfr Hblk Hmatch Hao
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddiw *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rd imm m
                  Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (m !!! Regidx rd)
                                (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
                = sval_den ρ (S32 (sval32_addZ (sval_trunc32 v1) (zimm32 imm)))).
        { unfold regval_into_reg. rewrite Hm1.
          cbn [sval_den].
          rewrite sval32_den_addZ.
          rewrite sval_trunc32_den.
          unfold zimm32. rewrite mword_of_int_uint32.
          rewrite -trunc32_add.
          rewrite trunc32_subrange. reflexivity. }
        iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSsd *)
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        destruct rvc.
        * iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rs2 rs1 imm
                    m (sval_den ρ vold)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hwfr Hblk Hmatch Hao
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rs2 rs1 imm
                    m (sval_den ρ vold)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hwfr Hblk Hmatch Hao
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSld *)
        apply negb_true_iff in Hnosp.
        pose proof (neq_of_eq_vec_false _ _ Hnosp) as Hrdsp.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv) by reflexivity.
        destruct rvc.
        * iApply (wp_cld_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rd rs1 imm
                    m (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (vpc st)) rd rs1 imm
                    m (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hwfr Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi16sp : excluded by [vblock_no_sp] *)
        discriminate Hnosp.
  Qed.

  (* the [m0 := m] instantiation: entry agreement is reflexive. *)
  Lemma wp_vc_block_s_sconf (γ : gname) (root_ppn : mword 44)
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m : gmap regidx (mword 64)) :
    vblock_no_sp prog = true ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : gmap regidx (mword 64),
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mf -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hwf Hblk Hmatch.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont".
    iApply (wp_vc_block_s_sconf_aux γ root_ppn prog Φ st st' ρ m m
              Hwf Hblk Hmatch (fun r _ => eq_refl)
              with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
  Qed.

End WpSconfVc.
