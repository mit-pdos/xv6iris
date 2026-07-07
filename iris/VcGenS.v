(* VcGenS.v -- the S-MODE instantiation of the straight-line VCgen (VcGen.v).

   Same idea as the M-mode [wp_vc_block]: a deep-embedded symbolic executor
   whose successful run (checked by [vm_compute]) yields, through ONE
   generic Iris lemma, the WP of a whole straight-line block.  The
   differences from the M-mode version are dictated by the S-mode leaf WPs
   (wp_caddi_gpr_s_config / wp_caddi4spn_gpr_s_config / wp_csdsp_gpr_s_ram /
   wp_cldsp_gpr_s_ram):

     - the instruction alphabet [vop_s] mirrors the RVC SHAPES those leaves
       are stated for (c.addi / c.addi4spn / c.sdsp / c.ldsp -- exactly the
       prologue/epilogue instructions of the kernel's S-mode functions),
       with the immediate FORMS baked in so the leaf ASTs match up
       syntactically;
     - the fixed context threaded through every step is the S-mode machine
       configuration (Supervisor privilege, mstatus/mie/mideleg/menvcfg,
       the PMP TOR-covers-RAM geometry, and the [tlb_inv root_ppn]
       identity-translation invariant) instead of [mmode_config];
     - all loads/stores are sp-relative 8-byte accesses (that is all the
       S-mode RVC-shape leaves cover today).

   The symbolic state, heap, and register denotation are shared with
   VcGen.v ([vstate] / [vheap_own] / [vregs_den] / [sval]).  See
   WpMycpuVc.v / WpPopOffVc.v for this VCgen applied to mycpu() and
   pop_off(). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
Require Import WpGprAddi WpGprLogic WpGprLui WpGprLoad WpGprStore WpGprRvc.
Require Import WpEntryNew WpSpinNew SmodeCore WpSmodeGpr WpMemsetS.
Require Import VcGen.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The S-mode instruction alphabet.                                     *)
(* ====================================================================== *)

Inductive vop_s : Type :=
  | VScaddi (imm : mword 6) (rd : mword 5)                    (* c.addi rd, imm       *)
  | VScaddi4spn (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
                                                              (* addi rd, sp, nz*4    *)
  | VScsdsp (uimm : mword 6) (rs2 : mword 5)                  (* sd rs2, uimm*8(sp)   *)
  | VScldsp (uimm : mword 6) (rd : mword 5).                  (* ld rd, uimm*8(sp)    *)

(* the TARGET AST of each shape, exactly as the S-mode leaves state it. *)
Definition vop_s_ast (op : vop_s) : instruction :=
  match op with
  | VScaddi imm rd =>
      ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)
  | VScaddi4spn rdc nzimm rd =>
      ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)
  | VScsdsp uimm rs2 =>
      STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)
  | VScldsp uimm rd =>
      LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)
  end.

(* the sp-relative byte offset of a c.sdsp/c.ldsp (canonical Z). *)
Definition zoff6 (uimm : mword 6) : Z :=
  uint (zero_extend' 64 (concat_vec uimm ('b"000")) : mword 64).

(* ====================================================================== *)
(* 2. The symbolic executor (state shared with the M-mode VCgen).          *)
(*    All four shapes are RVC, so every step advances the pc by 2.         *)
(* ====================================================================== *)

Definition vc_step_s (st : vstate) (op : vop_s) : option vstate :=
  let pc' := st.(vpc) + 2 in
  match op with
  | VScaddi imm rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rd with
      | Some v =>
          Some (VSt pc'
                  (<[Regidx rd := sval_addZ v (zimm12 (sign_extend' 12 imm))]>
                     st.(vregs))
                  st.(vheap))
      | None => None
      end
  | VScaddi4spn rdc nzimm rd =>
      if negb (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) then None else
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx csp_rs1 with
      | Some v =>
          Some (VSt pc'
                  (<[Regidx rd := sval_addZ v (zimm12 (caddi4spn_imm nzimm))]>
                     st.(vregs))
                  st.(vheap))
      | None => None
      end
  | VScsdsp uimm rs2 =>
      match st.(vregs) !! Regidx csp_rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          let a := sval_addZ v1 (zoff6 uimm) in
          match vheap_find st.(vheap) a with
          | Some (i, _) => Some (VSt pc' st.(vregs) (<[i := (a, v2)]> st.(vheap)))
          | None => None
          end
      | _, _ => None
      end
  | VScldsp uimm rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx csp_rs1 with
      | Some v1 =>
          let a := sval_addZ v1 (zoff6 uimm) in
          match vheap_find st.(vheap) a with
          | Some (_, v) =>
              Some (VSt pc' (<[Regidx rd := v]> st.(vregs)) st.(vheap))
          | None => None
          end
      | None => None
      end
  end.

Fixpoint vc_block_s (st : vstate) (prog : list vop_s) : option vstate :=
  match prog with
  | nil => Some st
  | op :: rest =>
      match vc_step_s st op with
      | Some st1 => vc_block_s st1 rest
      | None => None
      end
  end.

Section VcGenSIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the block's code: one RVC [instr] fact per entry, at consecutive pcs. *)
  Fixpoint block_instrs_s (pc : Z) (prog : list vop_s) : iProp Σ :=
    match prog with
    | nil => emp%I
    | op :: rest =>
        (instr (mword_of_int pc) true (vop_s_ast op) ∗
         block_instrs_s (pc + 2) rest)%I
    end.

  (* expose gpr_file's dom-completeness fact without consuming it. *)
  Lemma gpr_file_dom (m : gmap regidx (mword 64)) :
    gpr_file m -∗ ⌜ forall r : regidx, r ∈ dom m ⌝ ∗ gpr_file m.
  Proof.
    iIntros "[%Hdom Hmap]".
    iSplitR; [iPureIntro; exact Hdom|].
    iSplitR; [iPureIntro; exact Hdom|].
    iExact "Hmap".
  Qed.

  (* ================================================================== *)
  (* THE lemma: one successful symbolic run = one WP for the S-mode      *)
  (* block, under the standard S-mode machine configuration.             *)
  (* ================================================================== *)
  Lemma wp_vc_block_s (root_ppn : mword 44) (prog : list vop_s) E
      (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    vc_block_s st prog = Some st' ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file (vregs_den ρ st.(vregs)) -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file (vregs_den ρ st'.(vregs)) -∗
      vheap_own ρ st'.(vheap) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion HW HR.
    revert st. induction prog as [|op rest IH]; intros st Hblk.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
               Hpc Hgpr _ Hheap Hcont".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                            Hpc Hgpr Hheap").
    - cbn [vc_block_s] in Hblk.
      destruct (vc_step_s st op) as [st1|] eqn:Hstep;
        rewrite ?Hstep in Hblk; [|discriminate].
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
               Hpc Hgpr [Hi Hbi] Hheap Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd]; simpl in Hstep.
      + (* VScaddi *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (vpc st)) rd imm
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx rd)
                             (sign_extend' 64 (sign_extend' 12 imm)))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx rd := sval_addZ v1 (zimm12 (sign_extend' 12 imm))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -(sval_den_add_imm ρ v1 (sign_extend' 12 imm)).
          apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa
                                Htlbinv Hpc Hgpr Hbi Hheap Hcont").
      + (* VScaddi4spn *)
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (vpc st))
                  rdc nzimm rd (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Hrdc Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm nzimm)))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx rd := sval_addZ v1 (zimm12 (caddi4spn_imm nzimm))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -(sval_den_add_imm ρ v1 (caddi4spn_imm nzimm)).
          apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa
                                Htlbinv Hpc Hgpr Hbi Hheap Hcont").
      + (* VScsdsp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite sval_den_add_off.
          rewrite (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rs2
                  (vregs_den ρ (vregs st)) (sval_den ρ vold)
                  mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion
                  Hcov HW
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite (vregs_den_lookup ρ _ _ _ Hrs2) -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa
                                Htlbinv Hpc Hgpr Hbi Hheap Hcont").
      + (* VScldsp *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite sval_den_add_off.
          rewrite (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rd
                  (vregs_den ρ (vregs st)) (sval_den ρ vv)
                  mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                  (dq:=dq) (dqm:=DfracOwn 1)
                  HN Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp
                  Hpteregion Hcov HR
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Egpr : <[Regidx rd := regval_into_reg (sval_den ρ vv)]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := vv]> (vregs st))).
        { unfold regval_into_reg. apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa
                                Htlbinv Hpc Hgpr Hbi Hheap Hcont").
  Qed.

End VcGenSIris.
