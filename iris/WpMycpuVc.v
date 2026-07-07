(* WpMycpuVc.v -- wp_mycpu re-proved with the S-mode VCgen (VcGenS.v).

   Same statement as WpMycpu.wp_mycpu (the whole mycpu(), entry through its
   c.ret).  The hand proof steps 14 instructions individually; here the
   4-instruction PROLOGUE (c.addi sp,-16; sd ra,8(sp); sd s0,0(sp);
   addi s0,sp,16) and the 3-instruction EPILOGUE (ld ra,8(sp); ld s0,0(sp);
   addi sp,16) are each ONE [wp_vc_block_s] application whose symbolic run
   is a one-line [vm_compute] ([mycpu_prologue_run] / [mycpu_epilogue_run]);
   only the 6 middle instructions (mv/sext.w/slli/auipc/addi/add -- value
   shapes outside the VCgen's symbolic domain) and the final c.ret keep
   their per-instruction leaves.

   The [assert]s around each block are the SEAM GLUE: they identify the
   hand-spelled addresses/values of the surrounding proof (e.g.
   [add_vec (add_vec sp (-16)) 8]) with the VCgen's canonical forms
   ([sp + wrap64(-8)]) -- pure bv algebra, one [add_vec_off2]/[bv_eq] each. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpMycpu.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The two straight-line blocks of mycpu, in the VCgen's alphabet.          *)
(* ---------------------------------------------------------------------- *)
Definition mycpu_prologue : list vop_s :=
  [ VScaddi (mword_of_int 48) csp_rs1;                                  (* c.addi sp,-16      *)
    VScsdsp (mword_of_int 1) (mword_of_int 1);                          (* sd ra,8(sp)        *)
    VScsdsp (mword_of_int 0) (mword_of_int 8);                          (* sd s0,0(sp)        *)
    VScaddi4spn (Cregidx (mword_of_int 0)) (mword_of_int 4)
                (mword_of_int 8) ].                                     (* addi s0,sp,16      *)

Definition mycpu_epilogue : list vop_s :=
  [ VScldsp (mword_of_int 1) (mword_of_int 1);                          (* ld ra,8(sp)        *)
    VScldsp (mword_of_int 0) (mword_of_int 8);                          (* ld s0,0(sp)        *)
    VScaddi (mword_of_int 16) csp_rs1 ].                                (* c.addi sp,16       *)

(* variable convention: xk ↦ SX k 0 (from vregs_init); 33/34 = the two
   stack-slot contents at block entry. *)
Definition mycpu_pro_heap0 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 33 0);
    (SX 2 (wrap64 (-16)), SX 34 0) ].
Definition mycpu_pro_heap1 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 1 0);
    (SX 2 (wrap64 (-16)), SX 8 0) ].
Definition mycpu_pro_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 8 : mword 5) := SX 2 0]>
    (<[Regidx csp_rs1 := SX 2 (wrap64 (-16))]> vregs_init).

Lemma mycpu_prologue_run :
  vc_block_s (VSt KernelSyms.mycpu vregs_init mycpu_pro_heap0 []) mycpu_prologue
  = Some (VSt (KernelSyms.mycpu + 8) mycpu_pro_regs1 mycpu_pro_heap1 []).
Proof. vm_compute. reflexivity. Qed.

(* the epilogue runs with sp already at sp' (the decremented value), so its
   stack slots sit at sp+8 / sp+0. *)
Definition mycpu_epi_heap : list (sval * sval) :=
  [ (SX 2 8, SX 33 0);
    (SX 2 0, SX 34 0) ].
Definition mycpu_epi_regs1 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 16]>
    (<[Regidx (mword_of_int 8 : mword 5) := SX 34 0]>
       (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> vregs_init)).

Lemma mycpu_epilogue_run :
  vc_block_s (VSt (KernelSyms.mycpu + 24) vregs_init mycpu_epi_heap []) mycpu_epilogue
  = Some (VSt (KernelSyms.mycpu + 30) mycpu_epi_regs1 mycpu_epi_heap []).
Proof. vm_compute. reflexivity. Qed.

Section WpMycpuVc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the prologue's / epilogue's [instr] facts, from kernel_text via the
     existing WpMycpu decode templates. *)
  Lemma mycpu_prologue_instrs :
    kernel_text -∗ block_instrs_s KernelSyms.mycpu mycpu_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_prologue vop_s_ast].
    replace (KernelSyms.mycpu + 2 + 2) with (KernelSyms.mycpu + 4) by lia.
    replace (KernelSyms.mycpu + 4 + 2) with (KernelSyms.mycpu + 6) by lia.
    iSplitR; [by iApply myi_00|].
    iSplitR; [by iApply myi_02|].
    iSplitR; [by iApply myi_04|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply myi_06. }
    done.
  Qed.

  Lemma mycpu_epilogue_instrs :
    kernel_text -∗ block_instrs_s (KernelSyms.mycpu + 24) mycpu_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_epilogue vop_s_ast].
    replace (KernelSyms.mycpu + 24 + 2) with (KernelSyms.mycpu + 26) by lia.
    replace (KernelSyms.mycpu + 26 + 2) with (KernelSyms.mycpu + 28) by lia.
    iSplitR; [by iApply myi_18|].
    iSplitR; [by iApply myi_1a|].
    iSplitR; [by iApply myi_1c|].
    done.
  Qed.

  (* ==================================================================== *)
  (* wp_mycpu, re-proved.  Statement identical to WpMycpu.wp_mycpu.        *)
  (* ==================================================================== *)
  Lemma wp_mycpu_vc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64))
      (raold s0old : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let tp_idx : mword 5 := mword_of_int 4 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.mycpu in
    let imm_entry : mword 6 := mword_of_int 48 in
    let imm_dealloc : mword 6 := mword_of_int 16 in
    let nzimm_s0 : mword 8 := mword_of_int 4 in
    let imm_auipc : mword 20 := mword_of_int 0x11 in
    let imm_addi : mword 12 := mword_of_int 0xa94 in
    let shamt_slli : mword 6 := mword_of_int 7 in
    let imm_addiw : mword 6 := mword_of_int 0 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2 in
    let m4 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3 in
    let m5 := <[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int pcE 14) (auipc_off imm_auipc))]> m5 in
    let m7 := <[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6 in
    let m8 := <[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7 in
    let m9 := <[Regidx ra_idx := regval_into_reg ra0]> m8 in
    let m10 := <[Regidx s0_idx := regval_into_reg s00]> m9 in
    let m11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m10 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    pa_ra ↦₈ raold -∗
    pa_s0 ↦₈ s0old -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file m11 -∗
      pa_ra ↦₈ ra0 -∗
      pa_s0 ↦₈ s00 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx tp_idx s0_idx a0_idx a5_idx pcE imm_entry imm_dealloc nzimm_s0
      imm_auipc imm_addi shamt_slli imm_addiw sp' ra0 s00
      ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0
      m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      HX Hpmpp Hpteregion Hal0 HW HR Hramcov.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hbra Hbs0 Hcont".
    (* register-index / offset spelling bridges (pure, concrete) *)
    assert (Hcsp2 : Regidx (mword_of_int 2 : mword 5) = Regidx csp_rs1)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    (* ------------------------------------------------------------------ *)
    (* SEAM 1: enter the prologue block.                                    *)
    (* ------------------------------------------------------------------ *)
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom0 Hfile]".
    iDestruct (gpr_file_x0 m0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx00 Hfile]".
    set (ρA := fun k : nat =>
           if (k <? 32)%nat
           then m0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then (raold : mword 64) else (s0old : mword 64)).
    assert (HdenA : vregs_den ρA vregs_init = m0).
    { apply (vregs_den_init_agree _ _ Hdom0 Hx00). intros k Hk.
      unfold ρA. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    (* the block's two cells ARE the two stack words *)
    assert (Hara : sval_den ρA (SX 2 (wrap64 (-8))) = pa_ra).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold pa_ra, a8_ra, ea_ra, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has0 : sval_den ρA (SX 2 (wrap64 (-16))) = pa_s0).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold pa_s0, a8_s0, ea_s0, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hvra : sval_den ρA (SX 33 0) = (raold : mword 64)).
    { cbn [sval_den].
      replace (ρA 33%nat) with (raold : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (raold : mword 64) (mword_of_int 0))
        with (add_vec_int (raold : mword 64) 0).
      apply avi0. }
    assert (Hvs0 : sval_den ρA (SX 34 0) = (s0old : mword 64)).
    { cbn [sval_den].
      replace (ρA 34%nat) with (s0old : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (s0old : mword 64) (mword_of_int 0))
        with (add_vec_int (s0old : mword 64) 0).
      apply avi0. }
    iDestruct (mycpu_prologue_instrs with "Htext") as "Hbi".
    iEval (rewrite -HdenA) in "Hfile".
    iApply (wp_vc_block_s root_ppn mycpu_prologue E Φ
              (VSt KernelSyms.mycpu vregs_init mycpu_pro_heap0 [])
              (VSt (KernelSyms.mycpu + 8) mycpu_pro_regs1 mycpu_pro_heap1 [])
              ρA mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hramcov Hpmpp Hpteregion
              HW HR mycpu_prologue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                    Hpc Hfile Hbi [Hbra Hbs0] []").
    { rewrite /vheap_own. cbn [vheap].
      rewrite /mycpu_pro_heap0.
      rewrite big_sepL_cons big_sepL_cons big_sepL_nil.
      cbn [fst snd]. rewrite Hara Has0 Hvra Hvs0.
      iFrame "Hbra Hbs0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hheap _".
    (* SEAM 1 exit: the symbolic post-state denotes to m2 / the stored words *)
    assert (Hspv : sval_den ρA (SX 2 (wrap64 (-16))) = sp').
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold sp'. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs0v : sval_den ρA (SX 2 0)
                   = add_vec (m1 !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm nzimm_s0))).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold m1. rewrite lookup_total_insert. unfold regval_into_reg, sp'.
      rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hm2den : vregs_den ρA mycpu_pro_regs1 = m2).
    { unfold mycpu_pro_regs1.
      rewrite -vregs_den_insert -vregs_den_insert HdenA.
      rewrite Hspv Hs0v.
      unfold m2, m1, regval_into_reg. reflexivity. }
    iEval (rewrite Hm2den) in "Hfile".
    (* the stored words: den (SX 1 0) = ra0, den (SX 8 0) = s00 *)
    assert (Hvra0 : sval_den ρA (SX 1 0) = ra0).
    { cbn [sval_den].
      replace (ρA 1%nat) with (m0 !!! Regidx (mword_of_int 1 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m0 !!! Regidx (mword_of_int 1 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m0 !!! Regidx (mword_of_int 1 : mword 5)) 0).
      rewrite avi0. reflexivity. }
    assert (Hvs00 : sval_den ρA (SX 8 0) = s00).
    { cbn [sval_den].
      replace (ρA 8%nat) with (m0 !!! Regidx (mword_of_int 8 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m0 !!! Regidx (mword_of_int 8 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m0 !!! Regidx (mword_of_int 8 : mword 5)) 0).
      rewrite avi0. reflexivity. }
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_pro_heap1;
           rewrite big_sepL_cons big_sepL_cons big_sepL_nil; cbn [fst snd];
           rewrite Hara Has0 Hvra0 Hvs00) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & _)".
    (* pc: mword_of_int (mycpu+8) -> the hand-proof's add_vec_int spelling *)
    assert (Hpc8 : (mword_of_int (KernelSyms.mycpu + 8) : mword 64)
                   = add_vec_int pcE 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (cbn [vpc]; rewrite Hpc8) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* middle: the six value-computing instructions (as in wp_mycpu).       *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (myi_08 with "Htext") as "Hi08".
    iPoseProof (myi_0a with "Htext") as "Hi0a".
    iPoseProof (myi_0c with "Htext") as "Hi0c".
    iPoseProof (myi_0e with "Htext") as "Hi0e".
    iPoseProof (myi_12 with "Htext") as "Hi12".
    iPoseProof (myi_16 with "Htext") as "Hi16".
    iPoseProof (myi_1e with "Htext") as "Hi1e".
    (* +0x08 c.mv a5,tp : a5 := tp *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (add_vec_int pcE 8) a5_idx tp_idx m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2) with m3.
    (* +0x0a c.addiw a5,0 : a5 := sext32(a5) *)
    iApply (wp_caddiw_s root_ppn E Φ (add_vec_int pcE 10) a5_idx imm_addiw m3
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3) with m4.
    (* +0x0c c.slli a5,7 : a5 := a5 << 7 *)
    iApply (wp_cslli_gpr_s_config root_ppn E Φ (add_vec_int pcE 12) (Regidx a5_idx) a5_idx shamt_slli m4
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* +0x0e auipc a0,0x11 : a0 := pc + off *)
    iApply (wp_auipc_s root_ppn E Φ (add_vec_int pcE 14) a0_idx imm_auipc m5
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int pcE 14) (auipc_off imm_auipc))]> m5) with m6.
    replace (add_vec_int (add_vec_int pcE 14) 4) with (add_vec_int pcE 18) by (vm_compute; reflexivity).
    (* +0x12 addi a0,a0,-1388 : a0 := &cpus *)
    iApply (wp_addi4_s root_ppn E Φ (add_vec_int pcE 18) a0_idx a0_idx imm_addi m6
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6) with m7.
    replace (add_vec_int (add_vec_int pcE 18) 4) with (add_vec_int pcE 22) by (vm_compute; reflexivity).
    (* +0x16 c.add a0,a0,a5 : a0 := &cpus[cpuid] *)
    iApply (wp_cadd_s root_ppn E Φ (add_vec_int pcE 22) a0_idx a5_idx m7
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7) with m8.
    (* ------------------------------------------------------------------ *)
    (* SEAM 2: enter the epilogue block from the abstract file m8.          *)
    (* ------------------------------------------------------------------ *)
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = sp').
    { unfold m8, m7, m6, m5, m4, m3, m2, m1.
      do 7 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert. reflexivity. }
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom8 Hfile]".
    iDestruct (gpr_file_x0 m8 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx08 Hfile]".
    set (ρB := fun k : nat =>
           if (k <? 32)%nat
           then m8 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then ra0 else s00).
    assert (HdenB : vregs_den ρB vregs_init = m8).
    { apply (vregs_den_init_agree _ _ Hdom8 Hx08). intros k Hk.
      unfold ρB. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (HspB : ρB 2%nat = sp').
    { replace (ρB 2%nat) with (m8 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρB; reflexivity).
      rewrite Hcsp2. exact Hsp8. }
    assert (HaraB : sval_den ρB (SX 2 8) = pa_ra).
    { cbn [sval_den]. rewrite HspB.
      unfold pa_ra, a8_ra, ea_ra. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Has0B : sval_den ρB (SX 2 0) = pa_s0).
    { cbn [sval_den]. rewrite HspB.
      unfold pa_s0, a8_s0, ea_s0. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (HvraB : sval_den ρB (SX 33 0) = ra0).
    { cbn [sval_den].
      replace (ρB 33%nat) with ra0 by (unfold ρB; reflexivity).
      change (add_vec ra0 (mword_of_int 0)) with (add_vec_int ra0 0).
      apply avi0. }
    assert (Hvs0B : sval_den ρB (SX 34 0) = s00).
    { cbn [sval_den].
      replace (ρB 34%nat) with s00 by (unfold ρB; reflexivity).
      change (add_vec s00 (mword_of_int 0)) with (add_vec_int s00 0).
      apply avi0. }
    assert (Hpc24 : add_vec_int (add_vec_int pcE 22) 2
                    = (mword_of_int (KernelSyms.mycpu + 24) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    iEval (rewrite -HdenB) in "Hfile".
    iDestruct (mycpu_epilogue_instrs with "Htext") as "Hbi2".
    iApply (wp_vc_block_s root_ppn mycpu_epilogue E Φ
              (VSt (KernelSyms.mycpu + 24) vregs_init mycpu_epi_heap [])
              (VSt (KernelSyms.mycpu + 30) mycpu_epi_regs1 mycpu_epi_heap [])
              ρB mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hramcov Hpmpp Hpteregion
              HW HR mycpu_epilogue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                    Hpc Hfile Hbi2 [Hbra Hbs0] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
      rewrite big_sepL_cons big_sepL_cons big_sepL_nil.
      cbn [fst snd]. rewrite HaraB Has0B HvraB Hvs0B.
      iFrame "Hbra Hbs0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hheap _".
    (* SEAM 2 exit: the symbolic post-state denotes to m11 *)
    assert (Hsp16B : sval_den ρB (SX 2 16)
                     = add_vec (m10 !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 imm_dealloc))).
    { cbn [sval_den]. rewrite HspB.
      assert (Hsp10 : m10 !!! Regidx csp_rs1 = sp').
      { unfold m10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        unfold m9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hsp8. }
      rewrite Hsp10. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hm11den : vregs_den ρB mycpu_epi_regs1 = m11).
    { unfold mycpu_epi_regs1.
      rewrite -vregs_den_insert -vregs_den_insert -vregs_den_insert HdenB.
      rewrite HvraB Hvs0B Hsp16B.
      unfold m11, m10, m9, regval_into_reg. reflexivity. }
    iEval (rewrite Hm11den) in "Hfile".
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
           rewrite big_sepL_cons big_sepL_cons big_sepL_nil; cbn [fst snd];
           rewrite HaraB Has0B HvraB Hvs0B) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & _)".
    (* +0x1e c.ret : PC := ra0 (low bit cleared) *)
    assert (Hra_final : m11 !!! Regidx ra_idx = ra0).
    { unfold m11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m9. rewrite lookup_total_insert. reflexivity. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (KernelSyms.mycpu + 30)) ra_idx m11
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra_final; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile [Hbra] [Hbs0]").
    - iExact "Hbra".
    - iExact "Hbs0".
  Qed.

End WpMycpuVc.
