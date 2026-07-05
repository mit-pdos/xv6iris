(* WpHolding.v -- whole-function WP for xv6's holding() FAST PATH in S-mode:
   when the spinlock's [locked] word reads 0, holding() is four compressed
   instructions with no stack frame and no mycpu() call:

     holding @ 0x80000b94 (KernelInstrs.kernel_bytes):
       +0x0  411c  c.lw  a5,0(a0)     a5 := sext32(lk->locked)
       +0x2  e399  c.bnez a5,+0x8     NOT taken (locked = 0)
       +0x4  4501  c.li  a0,0         a0 := 0
       +0x6  8082  c.ret              return to ra

   The composition follows WpMycpu.v; the c.bnez fall-through leaf
   [wp_cbnez_fall_s] mirrors WpMemsetS.wp_cbeqz_fall_s_config with BNE. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas (podec-style; the tactics mirror WpPushOffTop's).        *)
(* ===================================================================== *)
Local Ltac h_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac h_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

Local Ltac h_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac h_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac h_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* +0x0  0x411c  c.lw a5,0(a0) *)
Lemma hdec_lw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x411c : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. h_open_rvc s H. h_close0 s H.
Qed.

(* +0x2  0xe399  c.bnez a5,+0x8 *)
Lemma hdec_bnez s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe399 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. h_open_rvc s H. h_close1 s H.
Qed.

(* +0x4  0x4501  c.li a0,0 *)
Lemma hdec_li s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4501 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof.
  intro H. h_reg_step Hr (mword_of_int 0x4501 : mword 16) 11 7 s.
  h_open_rvc s H. rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta. h_close1 s H.
Qed.

(* +0x6  0x8082  c.ret: reuse WpPushOffTop.podec_2a *)

(* the C_LW ExecuteAs expansion for imm 0 / a0-base / a5-dest *)
Lemma h_imm0 : zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")) = (mword_of_int 0 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma hexec_lw s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite h_imm0. reflexivity.
Qed.

Lemma hexec_bnez (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BNEZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BNE)), s).
Proof. unfold execute. cbn match. unfold execute_C_BNEZ. apply exec_returnM. Qed.

Section WpHolding.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs NOT taken (rs = 0): fall through to pc+2.  Mirrors          *)
  (* WpMemsetS.wp_cbeqz_fall_s_config with BEQ -> BNE.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cbnez_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom Hpmp Hpmpp Hpteregion Halignp Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom ltac:(discriminate) Hpmp Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the four fast-path instructions.                    *)
  (* ------------------------------------------------------------------- *)
  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Lemma hi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0) : mword 64) true
      (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x0)%Z (mword_of_int 0x411c : mword 16) (mword_of_int 0xe399411c : mword 32)
    (mword_of_int (KernelSyms.holding + 0x0) : mword 64)
    (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) hdec_lw hexec_lw. Qed.

  Lemma hi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x2) : mword 64) true
      (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x2)%Z (mword_of_int 0xe399 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x2) : mword 64)
    (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) hdec_bnez hexec_bnez. Qed.

  Lemma hi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x4) : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x4)%Z (mword_of_int 0x4501 : mword 16) (mword_of_int 0x80824501 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x4) : mword 64)
    (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) hdec_li exec_execute_C_LI. Qed.

  Lemma hi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x6) : mword 64) true
      (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x6)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x6) : mword 64)
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  wp_holding_fast: holding() when the lock word reads 0 -- returns    *)
  (*  a0 = 0 to the caller, clobbering only a5 (:= 0-extended lock word). *)
  (* =================================================================== *)
  Lemma wp_holding_fast (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (svpn_lk : mword 27) (lockv : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqm : dfrac} :
    let pcE : mword 64 := mword_of_int KernelSyms.holding in
    let a_lk := add_vec (m !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) in
    let m1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m in
    let m2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> m1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    kv_fetch_geom pcE -> kv_fetch_geom (add_vec_int pcE 2) ->
    kv_fetch_geom (add_vec_int pcE 4) -> kv_fetch_geom (add_vec_int pcE 6) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pcE ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 4) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 6) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* the lock word's data-slot geometry (R load, 4 bytes) *)
    po_slot_geom root_ppn pmpaddr00 svpn_lk a_lk 4 ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* fast path: the lock word reads 0 *)
    neq_vec (sign_extend' 64 lockv) zero_reg = false ->
    (* return target alignment *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file m2 -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE a_lk m1 m2 ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      Hg0 Hg2 Hg4 Hg6 Hp0 Hp2 Hp4 Hp6 Hpmpp Hpteregion Halignp
      Hslot HR Hlock0 Hal0.
    destruct Hslot as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hlk Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    iPoseProof (hi_04 with "Htext") as "Hi04".
    iPoseProof (hi_06 with "Htext") as "Hi06".
    (* +0x0 c.lw a5,0(a0): a5 := sext64 lockv *)
    iApply (wp_clw_s root_ppn E Φ pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) svpn_lk m lockv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=dq) (dqm:=dqm)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hg0 Hp0
              Lcanon Lvpn Lident Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp Lrange HR
              Lalign Lpalign
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 Hlk [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlk".
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m) with m1.
    (* +0x2 c.bnez a5: NOT taken (a5 = sext64 lockv = 0) *)
    assert (Ha5 : m1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (unfold m1; apply lookup_total_insert).
    iApply (wp_cbnez_fall_s root_ppn E Φ (add_vec_int pcE 2) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              m1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg2 Hp2 Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5; exact Hlock0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp4 : add_vec_int (add_vec_int pcE 2) 2 = add_vec_int pcE 4) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4) in "Hpc".
    (* +0x4 c.li a0,0 *)
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ (add_vec_int pcE 4) (mword_of_int 10) (mword_of_int 10) (mword_of_int 10)
              (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              m1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg4 Hp4 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [-]").
    { intros s_pc Hnpc _ _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 10) (sign_extend' 12 (mword_of_int 0 : mword 6)) s_pc).
      replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false by (vm_compute; reflexivity).
      unfold gpr_addi_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      reflexivity. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> m1) with m2.
    assert (Hpp6 : add_vec_int (add_vec_int pcE 4) 2 = add_vec_int pcE 6) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6) in "Hpc".
    (* +0x6 c.ret *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { unfold m2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m1. rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_zca root_ppn E Φ (add_vec_int pcE 6) (mword_of_int 1) m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg6 Hp6 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra2; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite Hra2) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlk").
  Qed.

End WpHolding.
