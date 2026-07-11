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
Require Import WpGpr WpGprLui WpGprAddi WpGprShift WpGprRvc WpGprRvcTor WpGprLoad WpLoad.
Require Import WpGprCsrwCommon WpGprCsrwB WpGprMretNew WpRelease.
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
    pose proof (addr_is_ram_not_in_clint _ HramP1) as HncP1.
    pose proof (addr_is_ram_not_in_sig _ HramP1) as HnsP1.
    pose proof (addr_is_ram_not_in_clint _ HramP0f) as HncP0f.
    pose proof (addr_is_ram_not_in_sig _ HramP0f) as HnsP0f.
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
    pose proof Hrg1x as Hrg1f; rewrite <- Hidx1 in Hrg1f.
    pose proof Hr1 as Hr1f; rewrite <- Hidx1 in Hr1f.
    pose proof Hb1 as Hb1f; rewrite <- Hidx1 in Hb1f.
    pose proof HncP1 as HncP1f; rewrite <- Hidx1 in HncP1f.
    pose proof HnsP1 as HnsP1f; rewrite <- Hidx1 in HnsP1f.
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
                Hb2f
                ltac:(rewrite Lpmpaddr_pc; exact Hrg1f)
                ltac:(rewrite Lpma_pc; exact (proj1 Hr1f))
                (proj2 Hr1f)
                (within_clint_false _ 8 s_pc HncP1f ltac:(lia))
                (within_sig_false _ 8 s_pc HnsP1f ltac:(lia))
                (within_htif_false _ 8 s_pc Lhtif_pc)
                Hb1f
                ltac:(rewrite Lpmpaddr_pc; exact Hrgfx)
                ltac:(rewrite Lpma_pc; exact (proj1 Hr0f))
                (proj2 Hr0f)
                (within_clint_false _ 8 s_pc HncP0f ltac:(lia))
                (within_sig_false _ 8 s_pc HnsP0f ltac:(lia))
                (within_htif_false _ 8 s_pc Lhtif_pc)
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
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
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
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
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
