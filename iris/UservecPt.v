(* UservecPt.v -- the uservec (trap-entry) instruction leaves over
   [utlb_inv_pt]: the STORE mirror of UserretPt.v's [wp_uld_pt], plus the
   two sscratch CSR leaves.

   uservec runs on the TRAMPOLINE page with the USER page table installed,
   so every instruction fetch goes through the user table's trampoline leaf
   (the [wp_instr_u_pt] engine of TrampStepPt.v) and every data access goes
   through the user table's TRAPFRAME leaf -- physical words [tfpa ↦ₚ₈].

   - [wp_usd_pt]   : sd rs2, imm(a0)      (the [wp_uld_pt] mirror)
   - [wp_ucsrw_sscratch_pt] : csrw sscratch, rs1
   - [wp_ucsrr_sscratch_pt] : csrr rd, sscratch

   The width-8 store execute tower is REUSED verbatim from
   WpSmodePtLeaves.v ([exec_execute_STORE_8_gpr_S_walk_pt]) -- it is already
   state-generic AND pa-generic ([Variable s s'], [Variable pa]), which is
   exactly the pa-form UserretPt.v had to clone for the load side only
   because its load tower derives the effective-address transform from the
   config facts instead of taking it as a hypothesis.  The store tower takes
   that transform as the hypothesis [Htea], so the ONE thing missing here is
   its S-mode discharge ([exec_transform_effective_address_store_S]). *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import ExecCommon WpGpr WpMmodeLeafBase.
Require Import WpGprCsrwCommon WpGprCsrrCommon.
Require Import SmodePte TrampPt.
Require Import SmodeCorePt WpSmodeGpr UptTree.
Require Import PtTree PtAdBits PtTreeAdue.
Require Import SRegime WpSmodePtLeaves.
Require Import TrampStepPt.
Require Import UserretDefs UserretPt.
Require Import RegFile.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The S-mode effective-address transform for a STORE.                 *)
(*    (the [exec_transform_effective_address_load_S] twin -- the only     *)
(*    premise of WpSmodePtLeaves' pa-generic width-8 store tower that is  *)
(*    not already supplied by the absorption theorem.)                    *)
(* ===================================================================== *)

Lemma exec_transform_effective_address_store_S (ea : mword 64) (satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm.
  assert (Hgen : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                 = Some (pm_transform_VA (Virtaddr ea) 0, s)).
  { unfold transform_effective_address.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S _ s Hmprv)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_store_S s Hmxr Hpmm)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
    apply exec_returnM. }
  rewrite Hgen. rewrite pm_transform_VA_0. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The TRAPFRAME leaf passes the S-mode STORE permission check on any  *)
(*    A/D variant (PTE_TF = 0xC7 is R|W with U=0), and the user           *)
(*    invariant therefore absorbs a trapframe STORE translation.          *)
(*    (the [tf_variant_check_load]/[utlb_inv_pt_translateAddr_tf_load]    *)
(*    twins of UptTree.v §1/§4.)                                          *)
(* ===================================================================== *)

Lemma tf_variant_check_store (tfp : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Store Data) Supervisor mxr do_sum (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Section UptTranslateStore.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma utlb_inv_pt_translateAddr_tf_store (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (Store Data)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (Store Data)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tf tfp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tf_variant_ppn tfp ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (Store Data) Supervisor uroot tfp um (pte_tf tfp) va pa σ
             (fun a d mxr do_sum => tf_variant_check_store tfp a d mxr do_sum)
             (or_intror (or_introl (conj Hvpn eq_refl)))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

End UptTranslateStore.

(* ===================================================================== *)
(* §3 [wp_usd_pt] -- sd rs2, imm(a0) inside uservec: instruction on the    *)
(*    TRAMPOLINE page, data through the user table's TRAPFRAME leaf.       *)
(*    Exactly [wp_uld_pt]'s signature with the load's [rd]/read swapped    *)
(*    for the store's [rs2]/write.                                         *)
(* ===================================================================== *)

Section WpUsdPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_usd_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (Φ : mval -> iProp Σ)
      (off immz : Z) (rs2 : mword 5) (is_rvc : bool)
      (m : regfile) (wold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    let imm : mword 12 := mword_of_int immz in
    let iva : mword 64 := mword_of_int (TRAPFRAME + immz) in
    let tfpa : mword 64 := zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0)) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* GPR: a0 holds TRAPFRAME *)
    m !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    (* data va geometry (vm_compute per instruction) *)
    add_vec (mword_of_int TRAPFRAME) (sign_extend' 64 imm) = iva ->
    neq_vec (bits_of_virtaddr (Virtaddr iva))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub 39 1) 0)) = false ->
    svpn_of iva = tf_vpn ->
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
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8)) -∗
    tfpa ↦ₚ₈ wold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      tfpa ↦ₚ₈ (m !!! Regidx rs2 : mword 64) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va pa imm iva tfpa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
      Heva Hcanond Hvpnd Halignd Hmod8.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb
             [Hpc Hnpc] Hfile Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_tf.
    iDestruct "Hbw" as "[%Hbal Hbytes]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all tfpa 8
                 (pma_access_ram _ _ Hram_tf (pma_width_ok 8 eq_refl eq_refl))) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_u_pt uroot tfp um Φ va pa is_rvc
              (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8))
              mstatus0 mie_v mdv0 menvcfg0 dq
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts, then reassemble *)
    iDestruct "Hutlb" as (usatp tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (utlb_inv_pt uroot tfp um) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Hutlb".
    { iExists usatp, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hwf |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma0v : m (Regidx (mword_of_int 10 : mword 5)) = mword_of_int TRAPFRAME)
      by exact Ha0.
    iAssert (⌜addr_is_ram tfpa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add tfpa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint tfpa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint tfpa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint tfpa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add tfpa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w tfpa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    pose proof (tfcat_aligned8 tfp _ Hmod8) as Hpalign8.
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (gpr_file_lookup_acc m (Regidx (mword_of_int 10 : mword 5)) with "Hfile") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) _ s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 _ s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfile".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = usatp)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    assert (Hif : (if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s_pc.(sregs))
                  = mword_of_int TRAPFRAME).
    { rewrite Lva. exact Hma0v. }
    (* the effective-address transform at s_pc *)
    pose proof (exec_transform_effective_address_store_S
                  (add_vec (if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s_pc.(sregs))
                           (sign_extend' 64 imm))
                  usatp s_pc Lpriv_pc LSXL_pc Lsatp_pc Hmode
                  ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm)) as Htea.
    (* the trapframe data translate through the absorption theorem *)
    iMod (utlb_inv_pt_translateAddr_tf_store uroot tfp um iva tfpa s_pc
            Hvpnd Hcanond eq_refl
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Hutlb")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Hutlb)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false tfpa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false tfpa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false tfpa 8 s_tr Lhtif_tr) as Hwh.
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx (mword_of_int 10), 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) tfpa 8 (m !!! Regidx rs2))
                              s_tr.(mdev))).
    { pose proof (exec_execute_STORE_8_gpr_S_walk_pt rs2 (mword_of_int 10) imm region_st s_pc s_tr tfpa
               Htea
               ltac:(rewrite Hif subrange_id sign_extend'_id Heva; exact Halignd)
               ltac:(rewrite Hif subrange_id sign_extend'_id Heva;
                     cbn [bits_of_virtaddr]; rewrite avi0_mul8; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               Hpalign8
               Hwrite_st Hwc Hws Hwh
               ltac:(exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 in H0. exact H0. }
    iDestruct (phys_word_pointsto_intro tfpa (DfracOwn 1) wold Hpalign8 with "Hbytes") as "Hbytes".
    iMod (phys_word_pointsto_write s_tr.(mem) tfpa wold (m !!! Regidx rs2) with "Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) tfpa 8 (m !!! Regidx rs2)) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) tfpa 8 (m !!! Regidx rs2)) s_tr.(mdev)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hutlb
                          [$Hpc' $Hnpc] Hfile Hbytes").
  Qed.

End WpUsdPt.

(* ===================================================================== *)
(* §4 sscratch: the S-mode csrw/csrr execute reductions.                  *)
(*    sscratch (0x140) is Ext_S-gated ([is_CSR_accessible] reduces to     *)
(*    [currentlyEnabled Ext_S]) with NO TVM gate and NO legalization --   *)
(*    [write_CSR] writes the value verbatim and reads it straight back.   *)
(* ===================================================================== *)

Definition csr_sscratch : mword 12 := mword_of_int 0x140.

Lemma exec_is_CSR_accessible_sscratch_S (acc : CSRAccessType) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_sscratch Supervisor acc) s = Some (true, s).
Proof.
  intro HS.
  assert (Hred : is_CSR_accessible csr_sscratch Supervisor acc = currentlyEnabled Ext_S)
    by csr_dispatch_eq.
  rewrite Hred.
  rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
Qed.

Lemma exec_check_CSR_result_csrw_sscratch_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sscratch Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_sscratch Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_sscratch_S. exact HS.
  - assert (H : stateen_allows_CSR_access csr_sscratch Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_check_CSR_result_csrr_sscratch_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sscratch Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - assert (H : check_CSR_priv csr_sscratch Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_sscratch_S. exact HS.
  - assert (H : stateen_allows_CSR_access csr_sscratch Supervisor CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_write_CSR_sscratch (v : mword 64) s :
  exec (write_CSR csr_sscratch v) s = Some (Ok v, set_reg s sscratch v).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sscratch v s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sscratch (set_reg s sscratch v))).
  rewrite register_lookup_set. apply exec_returnM.
Qed.

Lemma exec_read_CSR_sscratch s :
  exec (read_CSR csr_sscratch) s = Some (register_lookup sscratch s.(sregs), s).
Proof. drive_csr. exact (exec_read_reg sscratch s). Qed.

Lemma exec_csr_id_write_callback_sscratch (d : mword 64) s :
  exec (csr_id_write_callback csr_sscratch d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sscratch d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_csr_id_read_callback_sscratch (d : mword 64) s :
  exec (csr_id_read_callback csr_sscratch d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sscratch d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* csrw sscratch,rs1 in S-mode: sscratch := rs1's value (no legalization). *)
Lemma exec_execute_csrw_sscratch_S (rs1 : mword 5) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s sscratch
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
Proof.
  intros Hpriv HS.
  change (execute (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_sscratch (Regidx rs1) zreg CSRRW).
  apply (exec_execute_csrw_gpr_p Supervisor csr_sscratch rs1 s _
           (if Z.eqb (uint rs1) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_sscratch_S. exact HS.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sscratch.
  - apply exec_csr_id_write_callback_sscratch.
Qed.

(* csrr rd,sscratch (= csrrs rd,sscratch,x0) in S-mode. *)
Lemma exec_execute_csrr_sscratch_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup sscratch s.(sregs)))).
Proof.
  intros Hrd Hpriv HS.
  change (execute (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sscratch zreg (Regidx rd) CSRRS).
  apply (csrr_read_step_p Supervisor csr_sscratch rd
           (register_lookup sscratch s.(sregs)) s _ Hpriv).
  - apply exec_check_CSR_result_csrr_sscratch_S. exact HS.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_sscratch.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sscratch.
  - rewrite (exec_wX_bits_gpr rd (register_lookup sscratch s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* §5 The two sscratch CSR leaves over the uservec trampoline engine.     *)
(*    Same shape as [wp_ualu_pt] (no data access), with the sscratch cell *)
(*    threaded as an extra resource.                                      *)
(* ===================================================================== *)

Section WpUCsrPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_ucsrw_sscratch_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (Φ : mval -> iProp Σ)
      (off : Z) (is_rvc : bool) (rs1 : mword 5)
      (m : regfile) (sscr0 : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sscratch ↦ᵣ sscr0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sscratch ↦ᵣ (m !!! Regidx rs1 : mword 64) -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
             [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_u_pt uroot tfp um Φ va pa is_rvc
              (CSRReg (csr_sscratch, Regidx rs1, zreg, CSRRW))
              mstatus0 mie_v mdv0 menvcfg0 dq
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* tick nextPC *)
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 _ s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (HS_pc : eq_vec (_get_Misa_S (register_lookup misa s_pc.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_pc; exact HmisaS).
    pose proof (exec_execute_csrw_sscratch_S rs1 s_pc Lpriv_pc HS_pc) as Hexec0.
    rewrite Lva in Hexec0.
    (* mirror the physical write on the ghost cell *)
    iMod (reg_update _ sscratch _ (m !!! Regidx rs1 : mword 64) with "Hreg Hsscr") as "[Hreg Hsscr]".
    iModIntro.
    iExists (set_reg s_pc sscratch (m !!! Regidx rs1 : mword 64)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec0. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc sscratch (m !!! Regidx rs1 : mword 64)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
                          [$Hpc' $Hnpc] Hfile").
  Qed.

  Lemma wp_ucsrr_sscratch_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (Φ : mval -> iProp Σ)
      (off : Z) (is_rvc : bool) (rd : mword 5)
      (m : regfile) (sv : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq dqs : dfrac} :
    let va := uva off in
    let pa := upa off in
    uint rd <> 0 ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sscratch ↦ᵣ{ dqs } sv -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sscratch ↦ᵣ{ dqs } sv -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg sv]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va pa Hrd HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
             [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_u_pt uroot tfp um Φ va pa is_rvc
              (CSRReg (csr_sscratch, zreg, Regidx rd, CSRRS))
              mstatus0 mie_v mdv0 menvcfg0 dq
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hsscr") as %Lsscr.
    (* tick nextPC *)
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lsscr_pc : register_lookup sscratch s_pc.(sregs) = sv)
      by (unfold s_pc; tmig; exact Lsscr).
    assert (HS_pc : eq_vec (_get_Misa_S (register_lookup misa s_pc.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_pc; exact HmisaS).
    pose proof (exec_execute_csrr_sscratch_S rd s_pc Hrd Lpriv_pc HS_pc) as Hexec0.
    rewrite Lsscr_pc in Hexec0.
    (* rd := sv in the ghost gpr file *)
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg sv) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg sv)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg sv)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec0. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg sv)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb
                          [$Hpc' $Hnpc] Hfile").
  Qed.

End WpUCsrPt.
