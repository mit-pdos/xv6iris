(* WpUserretTop.v -- the userret WP itself: the trapframe loads, the
   page-table-switch entry (phase A/B), sret to user mode, and the
   whole-trampoline [wp_userret] (continuation of WpUserret.v). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpDecodeBridge WpRvcBridge WpLeafCommon.
Require Import WpGpr WpGprLui WpGprAddi WpMmodeShiftiop WpGprRvc WpGprRvcTor WpGprLoad WpLoad.
Require Import WpGprCsrwCommon WpGprCsrwB WpGprMret WpGprMretNew WpRelease.
Require Import WpEntryNew SmodeCore WpSmodeGpr WpSmodeSret WpKallocDecode.
Require Import TrampPt TrampTlb WpUserret.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 7. wp_uld -- one trapframe load (ld or c.ld target): rd := tf[imm].    *)
(* ===================================================================== *)

(* unsigned/alignment of a trapframe byte address (concat tfp off12). *)
Lemma tfcat_unsigned (tfp : mword 44) (x : mword 12) :
  bv_unsigned (zero_extend' 64 (concat_vec tfp x)) = bv_unsigned tfp * 4096 + bv_unsigned x.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12 in Hx.
  unfold zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (44 + 12)) (44 + 12)) as [e | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e)).
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  erewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096.
  apply Z_lor_disjoint_add.
  change 4096 with (2 ^ 12).
  apply Z_land_shift_low; [lia |].
  change (2 ^ 12) with 4096.
  pose proof (bv_unsigned_in_range _ x) as Hx2.
  change (MachineWord.MachineWord.Z_idx 12) with 12%N in Hx2.
  unfold bv_modulus in Hx2.
  change (Z.of_N 12%N) with 12 in Hx2.
  change (2 ^ 12) with 4096 in Hx2.
  lia.
Qed.

Lemma tfcat_aligned8 (tfp : mword 44) (x : mword 12) :
  bv_unsigned x `mod` 8 = 0 ->
  is_aligned_paddr (Physaddr (zero_extend' 64 (concat_vec tfp x))) 8 = true.
Proof.
  intro Hx8. unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  rewrite tfcat_unsigned.
  rewrite Z.rem_mod_nonneg; [| | lia].
  - rewrite Zplus_mod. rewrite Hx8.
    replace (bv_unsigned tfp * 4096) with ((bv_unsigned tfp * 512) * 8) by lia.
    rewrite Z_mod_mult. reflexivity.
  - pose proof (bv_unsigned_in_range _ tfp) as Ht. unfold bv_modulus in Ht.
    pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
    nia.
Qed.

Section WpUld.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_uld (uroot ul1 ul0 tfp : mword 44) E (Φ : mval -> iProp Σ)
      (off immz : Z) (rd : mword 5) (is_rvc : bool)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq dqm : dfrac} :
    let va := uva off in
    let pa := upa off in
    let imm : mword 12 := mword_of_int immz in
    let iva : mword 64 := mword_of_int (TRAPFRAME + immz) in
    let tfpa : mword 64 := zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0)) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* GPR: a0 holds TRAPFRAME *)
    m !! Regidx (mword_of_int 10) = Some (mword_of_int TRAPFRAME) ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 1) ->
    addr_is_ram (pa_add pa 2) -> addr_is_ram (pa_add pa 3) ->
    (* data va geometry (vm_compute per instruction) *)
    add_vec (mword_of_int TRAPFRAME) (sign_extend' 64 imm) = iva ->
    neq_vec (bits_of_virtaddr (Virtaddr iva))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tf_vpn ->
    is_aligned_vaddr (Virtaddr iva) 8 = true ->
    bv_unsigned (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0) `mod` 8 = 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv uroot ul1 ul0 tfp -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8)) -∗
    pte8 tfpa v dqm -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv uroot ul1 ul0 tfp -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pte8 tfpa v dqm -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros va pa imm iva tfpa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
      Hram0 Hram1 Hram2b Hram3b
      Heva Hcanond Hvpnd Halignd Hmod8.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all tfpa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_u uroot ul1 ul0 tfp E Φ va pa is_rvc
              (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              Hram0 Hram1 Hram2b Hram3b
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq usatp tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 rg2 rg1 rg0t rg0f)
      "(Hpmpc & Hpmpa & %Hp2 & %Hp1 & %Hp0 & %Hpf & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hr2 & Hr1 & Hr0t & Hr0f).
    (* trapframe byte + user-PTE mem facts at σ *)
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hbytes") as %[Hbytesf Hrampa].
    iDestruct "Hpbytes" as "(Hpb2 & Hpb1 & Hpb0t & Hpb0f)".
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb2") as %[Hb2 HramP2].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb1") as %[Hb1 HramP1].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb0f") as %[Hb0f HramP0f].
    iAssert (⌜addr_is_ram (pa_add tfpa 7)⌝)%I as %Hrampa7.
    { iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid    with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma0v : m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int TRAPFRAME)
      by (apply lookup_total_correct; exact Ha0).
    assert (Hmsp : m !! Regidx (mword_of_int 10 : mword 5) = Some (m !!! Regidx (mword_of_int 10 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* PMP range for the trapframe read from RAM coverage *)
    assert (Hlo : (ram_base <= uint tfpa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint tfpa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint tfpa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add tfpa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match tfpa (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) as Hrange_ld.
    pose proof (tfcat_aligned8 tfp _ Hmod8) as Hpalign8.
    (* tick nextPC *)
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m !!! Regidx (mword_of_int 10 : mword 5)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = usatp)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* a0's value, with the rs1<>x0 guard reduced *)
    assert (Hif : (if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s_pc.(sregs))
                  = mword_of_int TRAPFRAME).
    { rewrite Lva. exact Hma0v. }
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    (* mem facts transfer to s_pc (same memory) *)
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 8)%N ->
              s_pc.(mem) !! (pa_add tfpa j) = Some (nth_byte v j)) by exact Hbytesf.
    (* --- the data translation at s_pc: hit slot 62 or walk + fill --- *)
    pose proof (addr_is_ram_not_in_clint _ HramP2) as HncP2.
    pose proof (addr_is_ram_not_in_sig _ HramP2) as HnsP2.
    pose proof (addr_is_ram_not_dev _ HramP2) as HdevP2.
    pose proof (addr_is_ram_not_in_clint _ HramP1) as HncP1.
    pose proof (addr_is_ram_not_in_sig _ HramP1) as HnsP1.
    pose proof (addr_is_ram_not_dev _ HramP1) as HdevP1.
    pose proof (addr_is_ram_not_in_clint _ HramP0f) as HncP0f.
    pose proof (addr_is_ram_not_in_sig _ HramP0f) as HnsP0f.
    pose proof (addr_is_ram_not_dev _ HramP0f) as HdevP0f.
    destruct Hp2 as (HAx & Hordx & Hrg2x & HRx).
    destruct Hp1 as (HA1 & Hord1 & Hrg1x & HR1).
    destruct Hp0 as (HA0t & Hord0t & Hrg0tx & HR0t).
    destruct Hpf as (HAf & Hordf & Hrgfx & HRf).
    (* the level-2/1 walk facts are phrased at TRAMP_VPN's (identical) walk
       indices; convert them SYNTACTICALLY to TF_VPN's (kernel conversion on
       the bv index terms diverges, so rewrite with a vm-proved equality). *)
    assert (Hidx2 : subrange_vec_dec tf_vpn 26 18 = subrange_vec_dec tramp_vpn 26 18)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hidx1 : subrange_vec_dec tf_vpn 17 9 = subrange_vec_dec tramp_vpn 17 9)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof Hrg2x as Hrg2f; rewrite <- Hidx2 in Hrg2f.
    pose proof Hr2 as Hr2f; rewrite <- Hidx2 in Hr2f.
    pose proof Hb2 as Hb2f; rewrite <- Hidx2 in Hb2f.
    pose proof HncP2 as HncP2f; rewrite <- Hidx2 in HncP2f.
    pose proof HnsP2 as HnsP2f; rewrite <- Hidx2 in HnsP2f.
    pose proof HdevP2 as HdevP2f; rewrite <- Hidx2 in HdevP2f.
    pose proof Hrg1x as Hrg1f; rewrite <- Hidx1 in Hrg1f.
    pose proof Hr1 as Hr1f; rewrite <- Hidx1 in Hr1f.
    pose proof Hb1 as Hb1f; rewrite <- Hidx1 in Hb1f.
    pose proof HncP1 as HncP1f; rewrite <- Hidx1 in HncP1f.
    pose proof HnsP1 as HnsP1f; rewrite <- Hidx1 in HnsP1f.
    pose proof HdevP1 as HdevP1f; rewrite <- Hidx1 in HdevP1f.
    destruct (exec_translateAddr_tramp
                (Load Data) tf_vpn uroot ul1 ul0 tfp PTE_TF
                rg2 rg1 rg0f menvcfg0 s_pc
                ltac:(unfold PTE_TF; lia)
                tf_inv_red
                ltac:(vm_compute; reflexivity)
                tf_chk_load
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Lmisa_pc; exact HmisaS)
                ltac:(rewrite Lpmpc_pc; exact HAx)
                ltac:(rewrite Lpmpaddr_pc; exact Hordx)
                ltac:(rewrite Lpmpc_pc; exact HR)
                Lmenv_pc HPBMTE
                ltac:(rewrite Lpmpaddr_pc; exact Hrg2f)
                ltac:(rewrite Lpma_pc; exact (proj1 Hr2f))
                (proj2 Hr2f)
                (within_clint_false _ 8 s_pc HncP2f ltac:(lia))
                (within_sig_false _ 8 s_pc HnsP2f ltac:(lia))
                (within_htif_false _ 8 s_pc Lhtif_pc)
                HdevP2f
                Hb2f
                ltac:(rewrite Lpmpaddr_pc; exact Hrg1f)
                ltac:(rewrite Lpma_pc; exact (proj1 Hr1f))
                (proj2 Hr1f)
                (within_clint_false _ 8 s_pc HncP1f ltac:(lia))
                (within_sig_false _ 8 s_pc HnsP1f ltac:(lia))
                (within_htif_false _ 8 s_pc Lhtif_pc)
                HdevP1f
                Hb1f
                ltac:(rewrite Lpmpaddr_pc; exact Hrgfx)
                ltac:(rewrite Lpma_pc; exact (proj1 Hr0f))
                (proj2 Hr0f)
                (within_clint_false _ 8 s_pc HncP0f ltac:(lia))
                (within_sig_false _ 8 s_pc HnsP0f ltac:(lia))
                (within_htif_false _ 8 s_pc Lhtif_pc)
                HdevP0f
                Hb0f
                ltac:(unfold update_PTE_Bits;
                      rewrite (mk_pte_flags tfp PTE_TF ltac:(unfold PTE_TF; lia));
                      match goal with |- (if ?c then _ else _) = None =>
                        replace c with false by (vm_compute; reflexivity) end;
                      reflexivity)
                usatp tfpa iva
                ltac:(apply exec_effectivePrivilege_load_S; rewrite Lms_pc; exact HMPRV)
                (exec_is_shadow_stack_load s_pc)
                Lpriv_pc
                ltac:(rewrite Lms_pc; exact HSXL)
                Lsatp_pc Hmode Hppn Hasid Hcanond Hvpnd eq_refl
                tlbvec_f Ltlb_pc
                (utlb_slot62 ul0 tfp tlbvec_f Hconsf))
      as (s' & Htr & Hcase).
    (* register-transfer to the (possibly) tlb-updated state *)
    assert (HregT : forall (tv : vec (option TLB_Entry) (2 ^ 6)) (rr : register),
              register_beq rr tlb = false ->
              register_lookup rr (set_reg s_pc tlb tv).(sregs) = register_lookup rr s_pc.(sregs)).
    { intros tv rr Hne. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [reflexivity | exact Hne]. }
    pose proof (addr_is_ram_not_in_clint _ Hrampa) as Hncd.
    pose proof (addr_is_ram_not_in_sig _ Hrampa) as Hnsd.
    destruct Hcase as [-> | ->].
    - (* ---- HIT: the data slot already holds the trapframe entry ---- *)
      assert (Htr' : exec (translateAddr (Virtaddr iva) (Load Data)) s_pc
                     = Some (Ok (Physaddr tfpa, PBMT_PMA, init_ext_ptw), set_reg s_pc tlb tlbvec_f)).
      { replace (set_reg s_pc tlb tlbvec_f) with s_pc; [exact Htr |].
        rewrite <- Ltlb_pc. symmetry. apply set_reg_tlb_id. }
      assert (Hload : exec (execute (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8)))
                        (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                             (if is_rvc then 2 else 4)))
                      = Some (RETIRE_SUCCESS,
                              set_reg (set_reg s_pc tlb tlbvec_f) (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite Hpceq. fold s_pc.
        rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_pa (mword_of_int 10) rd imm tfpa v region_ld usatp tlbvec_f s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Hif; rewrite subrange_id; rewrite sign_extend'_id; rewrite Heva; exact Halignd)
                 ltac:(rewrite Hif; rewrite subrange_id; rewrite sign_extend'_id; rewrite Heva;
                       cbn [bits_of_virtaddr]; rewrite avi0_mul8; exact Htr')
                 ltac:(rewrite (HregT tlbvec_f cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc)
                 ltac:(rewrite (HregT tlbvec_f mstatus ltac:(vm_compute; reflexivity)); rewrite Lms_pc; exact HMPRV)
                 ltac:(rewrite (HregT tlbvec_f pmpcfg_n ltac:(vm_compute; reflexivity)); rewrite Lpmpc_pc; exact HAx)
                 ltac:(rewrite (HregT tlbvec_f pmpaddr_n ltac:(vm_compute; reflexivity)); rewrite Lpmpaddr_pc; exact Hordx)
                 ltac:(rewrite (HregT tlbvec_f pmpaddr_n ltac:(vm_compute; reflexivity)); rewrite Lpmpaddr_pc; exact Hrange_ld)
                 ltac:(rewrite (HregT tlbvec_f pmpcfg_n ltac:(vm_compute; reflexivity)); rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite (HregT tlbvec_f pma_regions ltac:(vm_compute; reflexivity)); rewrite Lpma_pc; exact Hmatch_ld0)
                 Hpalign8 Hread_ld
                 (within_clint_false tfpa 8 _ Hncd ltac:(lia))
                 (within_sig_false tfpa 8 _ Hnsd ltac:(lia))
                 ltac:(apply within_htif_false;
                       rewrite (HregT tlbvec_f htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc)
                 (addr_is_ram_not_dev _ Hrampa)
                 Hbytesf_pc). }
      iMod (reg_update _ tlb _ tlbvec_f with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg (set_reg s_pc tlb tlbvec_f) (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg v)).
      iSplitR.
      { iPureIntro. exact Hload. }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg (set_reg s_pc tlb tlbvec_f) (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg v)).(sregs)
               = add_vec_int va (if is_rvc then 2 else 4)).
      { unfold s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv
                            [Hsatp Htlb Hpb2 Hpb1 Hpb0t Hpb0f Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbytes").
      { iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb [Hpb2 Hpb1 Hpb0t Hpb0f] [Hpmpc Hpmpa]").
        - iFrame "Hpb2 Hpb1 Hpb0t Hpb0f".
        - iExists pmpcfg0, pmpaddr00, rg2, rg1, rg0t, rg0f.
          iFrame "Hpmpc Hpmpa". iPureIntro.
          exact (conj (conj HAx (conj Hordx (conj Hrg2x HRx)))
                 (conj (conj HA1 (conj Hord1 (conj Hrg1x HR1)))
                 (conj (conj HA0t (conj Hord0t (conj Hrg0tx HR0t)))
                 (conj (conj HAf (conj Hordf (conj Hrgfx HRf)))
                 (conj Hpteregion (conj HX (conj HW (conj HR Hcov)))))))). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
    - (* ---- MISS: the walk fills slot 62 ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) tf_vpn)
                      (Some (tramp_tlb_ent tf_vpn ul0 tfp PTE_TF))).
      assert (Hconsf2 : utlb_consistent ul0 tfp tlbf2).
      { unfold tlbf2.
        change (tramp_tlb_ent tf_vpn ul0 tfp PTE_TF) with (tf_ent ul0 tfp).
        apply utlb_consistent_fill62. exact Hconsf. }
      assert (Htr' : exec (translateAddr (Virtaddr iva) (Load Data)) s_pc
                     = Some (Ok (Physaddr tfpa, PBMT_PMA, init_ext_ptw), set_reg s_pc tlb tlbf2)).
      { exact Htr. }
      assert (Hload : exec (execute (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8)))
                        (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                             (if is_rvc then 2 else 4)))
                      = Some (RETIRE_SUCCESS,
                              set_reg (set_reg s_pc tlb tlbf2) (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite Hpceq. fold s_pc.
        rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_pa (mword_of_int 10) rd imm tfpa v region_ld usatp tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Hif; rewrite subrange_id; rewrite sign_extend'_id; rewrite Heva; exact Halignd)
                 ltac:(rewrite Hif; rewrite subrange_id; rewrite sign_extend'_id; rewrite Heva;
                       cbn [bits_of_virtaddr]; rewrite avi0_mul8; exact Htr')
                 ltac:(rewrite (HregT tlbf2 cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc)
                 ltac:(rewrite (HregT tlbf2 mstatus ltac:(vm_compute; reflexivity)); rewrite Lms_pc; exact HMPRV)
                 ltac:(rewrite (HregT tlbf2 pmpcfg_n ltac:(vm_compute; reflexivity)); rewrite Lpmpc_pc; exact HAx)
                 ltac:(rewrite (HregT tlbf2 pmpaddr_n ltac:(vm_compute; reflexivity)); rewrite Lpmpaddr_pc; exact Hordx)
                 ltac:(rewrite (HregT tlbf2 pmpaddr_n ltac:(vm_compute; reflexivity)); rewrite Lpmpaddr_pc; exact Hrange_ld)
                 ltac:(rewrite (HregT tlbf2 pmpcfg_n ltac:(vm_compute; reflexivity)); rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite (HregT tlbf2 pma_regions ltac:(vm_compute; reflexivity)); rewrite Lpma_pc; exact Hmatch_ld0)
                 Hpalign8 Hread_ld
                 (within_clint_false tfpa 8 _ Hncd ltac:(lia))
                 (within_sig_false tfpa 8 _ Hnsd ltac:(lia))
                 ltac:(apply within_htif_false;
                       rewrite (HregT tlbf2 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc)
                 (addr_is_ram_not_dev _ Hrampa)
                 Hbytesf_pc). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg (set_reg s_pc tlb tlbf2) (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg v)).
      iSplitR.
      { iPureIntro. exact Hload. }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg (set_reg s_pc tlb tlbf2) (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg v)).(sregs)
               = add_vec_int va (if is_rvc then 2 else 4)).
      { unfold s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv
                            [Hsatp Htlb Hpb2 Hpb1 Hpb0t Hpb0f Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbytes").
      { iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbf2 Hmode Hasid Hppn Hconsf2
                  with "Hsatp Htlb [Hpb2 Hpb1 Hpb0t Hpb0f] [Hpmpc Hpmpa]").
        - iFrame "Hpb2 Hpb1 Hpb0t Hpb0f".
        - iExists pmpcfg0, pmpaddr00, rg2, rg1, rg0t, rg0f.
          iFrame "Hpmpc Hpmpa". iPureIntro.
          exact (conj (conj HAx (conj Hordx (conj Hrg2x HRx)))
                 (conj (conj HA1 (conj Hord1 (conj Hrg1x HR1)))
                 (conj (conj HA0t (conj Hord0t (conj Hrg0tx HR0t)))
                 (conj (conj HAf (conj Hordf (conj Hrgfx HRf)))
                 (conj Hpteregion (conj HX (conj HW (conj HR Hcov)))))))). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

End WpUld.

(* ===================================================================== *)
(* 8. wp_ualu -- one pure a0-updating step (lui / c.addiw / c.slli).      *)
(* ===================================================================== *)

Section WpUalu.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* Generic over the executed AST [ast] and its (state-dependent) result
     value [vf]: all three a0-arithmetic steps of userret instantiate this
     with the corresponding WpGpr* execute lemma and a pure value fact. *)
  Lemma wp_ualu (uroot ul1 ul0 tfp : mword 44) E (Φ : mval -> iProp Σ)
      (off : Z) (is_rvc : bool) (ast : instruction)
      (m : gmap regidx (mword 64)) (a0v vnew : mword 64)
      (vf : mstate -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* the execute: a0 := vf s *)
    (forall s : mstate,
       exec (execute ast) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                      (regval_into_reg (vf s)))) ->
    (* the value, given a0's current contents *)
    (forall s : mstate,
       register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s.(sregs) = a0v ->
       vf s = vnew) ->
    (* GPR: a0's current contents *)
    m !! Regidx (mword_of_int 10) = Some a0v ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 1) ->
    addr_is_ram (pa_add pa 2) -> addr_is_ram (pa_add pa 3) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv uroot ul1 ul0 tfp -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc ast -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv uroot ul1 ul0 tfp -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx (mword_of_int 10) := regval_into_reg vnew]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros va pa HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hexec Hval Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
      Hram0 Hram1 Hram2b Hram3b.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_u uroot ul1 ul0 tfp E Φ va pa is_rvc ast
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              Hram0 Hram1 Hram2b Hram3b
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq usatp tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hrd10 : uint (mword_of_int 10 : mword 5) <> 0) by (vm_compute; lia).
    assert (Hma0v : m !!! Regidx (mword_of_int 10 : mword 5) = a0v)
      by (apply lookup_total_correct; exact Ha0).
    assert (Hmsp : m !! Regidx (mword_of_int 10 : mword 5) = Some (m !!! Regidx (mword_of_int 10 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC *)
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m !!! Regidx (mword_of_int 10 : mword 5)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false in Lva
      by (vm_compute; reflexivity).
    rewrite Hma0v in Lva.
    (* the execute at s_pc *)
    assert (Hload : exec (execute ast)
                      (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                           (if is_rvc then 2 else 4)))
                    = Some (RETIRE_SUCCESS,
                            set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                              (regval_into_reg vnew))).
    { rewrite Hpceq. fold s_pc. rewrite (Hexec s_pc).
      replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false
        by (vm_compute; reflexivity).
      rewrite (Hval s_pc Lva). reflexivity. }
    (* a0 := vnew in the ghost gpr file *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmsp with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz (mword_of_int 10) _ Hrd10).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) _ (regval_into_reg vnew)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg vnew) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz (mword_of_int 10) _ Hrd10). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
               (regval_into_reg vnew)).
    iSplitR.
    { iPureIntro. exact Hload. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                (regval_into_reg vnew)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv
                          [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpUalu.

(* ===================================================================== *)
(* 9. sret to USER mode, over [utlb_inv].                                 *)
(* ===================================================================== *)

(* get_xLPE at User with senvcfg = 0 and menvcfg = MENVCFG_S: reads
   senvcfg/menvcfg/senvcfg (via read_senvcfg); the LPE bit of the
   SSE-merged senvcfg is 0. *)
Lemma exec_get_xLPE_U (sz : mstate) :
  eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1") = true ->
  register_lookup senvcfg sz.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg sz.(sregs) = MENVCFG_S ->
  exec (get_xLPE User) sz = Some (false, sz).
Proof.
  intros HS Hsenv Hmenv.
  unfold get_xLPE. destruct (Defs.Zwf_guarded _).
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb 2 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl sz)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    assert (HrecS : exec (_rec_currentlyEnabled Ext_S k a) sz
                    = Some (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1"), sz)) end.
  { match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    match goal with |- context[Z.geb ?kk 0] => change (Z.geb kk 0) with true end.
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl sz)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S sz)). cbn match.
    rewrite (exec_and_boolM_Some _ _ sz
               (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1")) sz).
    - destruct (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1")) eqn:?.
      + match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_rec_cE_Zicsr_any k2 a2 sz ltac:(reflexivity)) end.
      + reflexivity.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa sz)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ HrecS).
  rewrite HS. cbv iota.
  (* read_senvcfg: senvcfg, menvcfg, senvcfg -- all pinned *)
  unfold read_senvcfg.
  assert (Hrs : exec (Defs.bind (Defs.read_reg senvcfg)
           (fun w0 => Defs.bind (Defs.read_reg menvcfg)
              (fun w1 => Defs.bind (Defs.read_reg senvcfg)
                 (fun w2 => returnM (_update_SEnvcfg_SSE w0
                              (and_vec (_get_MEnvcfg_SSE w1) (_get_SEnvcfg_SSE w2))))))) sz
         = Some (_update_SEnvcfg_SSE (mword_of_int 0)
                   (and_vec (_get_MEnvcfg_SSE MENVCFG_S)
                            (_get_SEnvcfg_SSE (mword_of_int 0))), sz)).
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg sz)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg sz)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg sz)).
    rewrite Hsenv. rewrite Hmenv. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hrs).
  match goal with |- context[bool_bit_backwards ?b] =>
    replace (bool_bit_backwards b) with false by (vm_compute; reflexivity) end.
  apply exec_returnM.
Qed.

(* The SRET execute reduction (verbatim WpSmodeSret's [ExecSRET] tower)
   with the [get_xLPE] premise ALSO carrying the senvcfg and misa lookups
   of the intermediate state -- [get_xLPE User] reads both. *)
Section ExecSRETU.
  Context (s : mstate) (lpe : bool) (menvcfg0 : mword 64).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 5 5 ('b"1").
  Let newpriv : Privilege := if eq_vec (_get_Mstatus_SPP ms2) ('b"1") then Supervisor else User.
  Let ms3 := update_subrange_vec_dec ms2 8 8 ('b"0").
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_SPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := update_vec_dec (register_lookup sepc s.(sregs)) 0 ('b"0").
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HTSR : eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis Hlpe : forall sz : mstate,
      register_lookup menvcfg sz.(sregs) = menvcfg0 ->
      register_lookup senvcfg sz.(sregs) = register_lookup senvcfg s.(sregs) ->
      register_lookup misa sz.(sregs) = register_lookup misa s.(sregs) ->
      exec (get_xLPE newpriv) sz = Some (lpe, sz).

  Lemma exec_execute_SRET_menvU : exec (execute (SRET tt)) s = Some (RETIRE_SUCCESS, sF).
  Proof using All.
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. cbn match.
    assert (Harm1 : exec (Defs.bind (currentlyEnabled Ext_S)
                          (fun w1 : bool => returnM (Riscv.rv64d.not w1))) s = Some (false, s)).
    { rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS.
      cbn [Riscv.rv64d.not negb]. apply exec_returnM. }
    assert (Hguard : exec (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                            (fun w1 : bool => returnM (Riscv.rv64d.not w1)))
                          (Defs.bind (Defs.read_reg mstatus)
                            (fun w2 : mword 64 => returnM (eq_vec (_get_Mstatus_TSR w2) ('b"1"))))) s
                    = Some (false, s)).
    { unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ Harm1). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite HTSR. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hguard). cbn match.
    change (ext_check_xret_priv Supervisor) with true. cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms2 s1)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege newpriv s2)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set; [subst s2; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms3 s3)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set; [subst s3; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    assert (Hnpm : generic_neq newpriv Machine = true)
      by (unfold newpriv; destruct (eq_vec (_get_Mstatus_SPP ms2) ('b"1")); reflexivity).
    rewrite Hnpm. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms4 s4)).
    set (s6 := set_reg s5 mstatus ms5).
    set (s7 := set_reg s6 elp elpv).
    assert (HL6 : register_lookup menvcfg s6.(sregs) = menvcfg0).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Hmenv. }
    assert (HL6s : register_lookup senvcfg s6.(sregs) = register_lookup senvcfg s.(sregs)).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      reflexivity. }
    assert (HL6m : register_lookup misa s6.(sregs) = register_lookup misa s.(sregs)).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12)) s5
               = Some (tt, s7))).
        2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s5)).
            replace (register_lookup cur_privilege s5.(sregs)) with newpriv
              by (subst s5 s4 s3; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite register_lookup_set; reflexivity).
            unfold zicfilp_restore_elp_on_xret. cbn match.
            rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind (Defs.read_reg mstatus)
                     (fun w0 : mword 64 => Defs.bind (Defs.read_reg mstatus)
                        (fun w1 : mword 64 => Defs.bind0
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 23 23
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_SPELP w0))))) s5
                   = Some (_get_Mstatus_SPELP ms4, s6))).
            2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms5 s5)).
                apply exec_returnm. }
            rewrite (exec_bind_Some _ _ _ _ _ (Hlpe s6 HL6 HL6s HL6m)).
            rewrite (exec_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Supervisor)) s7 = Some (tgt, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7))).
        2:{ rewrite (exec_bind0_Some _ _ _ _ _
              (_ : exec (long_csr_write_callback "mstatus" "mstatush" ms5) s7 = Some (tt, s7))).
            2:{ apply exec_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_returnm. }
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s7)).
        replace (register_lookup sepc s7.(sregs)) with (register_lookup sepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_bind_Some _ _ _ _ _
          (_ : exec (currentlyEnabled Ext_Zca) s7 = Some (true, s7))).
        2:{ apply exec_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Hmc. }
        cbn match. apply exec_returnM. }
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_set_next_pc tgt s7)).
    apply exec_returnm.
  Qed.
End ExecSRETU.

(* ------------------------------------------------------------------- *)
(* wp_usret -- SRET at the trampoline's end: privilege drops to USER,    *)
(* pc := sepc (bit 0 cleared), [utlb_inv] rides through untouched.       *)
(* ------------------------------------------------------------------- *)
Section WpUsret.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_usret (uroot ul1 ul0 tfp : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0 : mword 64) :
    let va := uva 0x11c in
    let pa := upa 0x11c in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    senvcfg0 = mword_of_int 0 ->
    (* SRET-specific premises: no trap, and SPP decodes to USER *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = User ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    senvcfg ↦ᵣ senvcfg0 -∗
    sepc ↦ᵣ sepc0 -∗
    utlb_inv uroot ul1 ul0 tfp -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ User -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      senvcfg ↦ᵣ senvcfg0 -∗
      sepc ↦ᵣ sepc0 -∗
      utlb_inv uroot ul1 ul0 tfp -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros va pa HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsenvval0 HTSR Hsup.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb
             [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    iApply (wp_instr_u uroot ul1 ul0 tfp E Φ va pa false (SRET tt)
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq usatp tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    (* tick nextPC := va+4 *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lsenv_pc : register_lookup senvcfg s_pc.(sregs) = senvcfg0)
      by (unfold s_pc; tmig; exact Lsenv).
    assert (Lsepc_pc : register_lookup sepc s_pc.(sregs) = sepc0)
      by (unfold s_pc; tmig; exact Lsepc).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the SRET execute reduction at s_pc, with newpriv = User, lpe = false *)
    pose proof (exec_execute_SRET_menvU s_pc false menvcfg0
                  Lpriv_pc
                  ltac:(rewrite Lmisa_pc; exact HmisaS)
                  ltac:(rewrite Lms_pc; exact HTSR)
                  ltac:(rewrite Lmisa_pc; exact HmisaC)
                  Lmenv_pc
                  ltac:(intros sz Hm Hs Hmi;
                        assert (Hx : exec (get_xLPE User) sz = Some (false, sz))
                          by (apply exec_get_xLPE_U;
                              [ rewrite Hmi; rewrite Lmisa_pc; exact HmisaS
                              | rewrite Hs; rewrite Lsenv_pc; exact Hsenvval0
                              | rewrite Hm; exact Hmenvval0 ]);
                        rewrite <- Hsup in Hx;
                        unfold sret_newpriv, sret_ms2, sret_ms1 in Hx;
                        rewrite Lms_pc; exact Hx)) as HexecC0.
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 mstatus0)) mstatus (sret_ms2 mstatus0))
                           cur_privilege User) mstatus (sret_ms3 mstatus0)) mstatus (sret_ms4 mstatus0))
                  mstatus (sret_ms5 mstatus0)) elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (sret_tgt sepc0)).
    assert (HexecC : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite HexecC0. unfold sX.
      rewrite !Lms_pc Lsepc_pc.
      unfold sret_newpriv, sret_ms2, sret_ms1 in Hsup.
      unfold sret_ms1, sret_ms2, sret_ms3, sret_ms4, sret_ms5, sret_tgt.
      rewrite Hsup. reflexivity. }
    (* mirror the physical set_regs on the ghost cells *)
    iMod (reg_update _ mstatus _ (sret_ms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ User with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (sret_ms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (sret_ms5 mstatus0) (register_set mstatus (sret_ms4 mstatus0)
                (register_set mstatus (sret_ms3 mstatus0) (register_set cur_privilege User
                  (register_set mstatus (sret_ms2 mstatus0) (register_set mstatus (sret_ms1 mstatus0)
                    (register_set nextPC (add_vec_int va 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (sret_tgt sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists sX.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold sX, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC sX.(sregs) = sret_tgt sepc0)
      by (unfold sX, set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
                          [Hsatp Htlb Hpbytes Hpmp] [$Hpc' $Hnpc] Hfile").
    iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbvec_f Hmode Hasid Hppn Hconsf
              with "Hsatp Htlb Hpbytes Hpmp").
  Qed.

End WpUsret.
