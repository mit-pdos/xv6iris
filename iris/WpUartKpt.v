(* UART S-mode device access under the NATIVE kernel page table (kvmmake-faithful
   all-4KB PT).  The refactored [tlb_inv root_ppn] already maps the UART (device
   vpn 0x10000, PTE_DEV) via [kpt_bytes]/[P_kpt], so the device leaves no longer
   need the [tlb_inv_gen (P_uart4k …)] switch or the client [uart_map] resource:
   the three UART PTE bytes come straight from the invariant's [kpt_bytes].

   This file provides the pure bridge lemmas (Phase 1): the UART page's kernel-PT
   walk pages, its byte/RAM facts sourced from [kpt_mem], its [P_kpt] membership +
   fill, and [tlb_consistent] monotonicity (which lets the reworked leaves feed
   the invariant's [tlb_consistent (P_kpt root)] straight into the unchanged
   [exec_translateAddr_uart], since P_kpt ⟹ P_uart4k). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodePte Pt4kWalk KptPt SmodeCore.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import WpSmodeGpr.
Require Import WpUart WpSmodeUart.
Require Import Pt4kWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Phase 1: pure bridge lemmas.                                            *)
(* ===================================================================== *)

(* [tlb_consistent] is monotone in the legal-entry predicate. *)
Lemma tlb_consistent_mono (P Q : TLB_Entry -> Prop) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall e, P e -> Q e) -> tlb_consistent P tlbvec -> tlb_consistent Q tlbvec.
Proof.
  intros HPQ HP i Hi. destruct (HP i Hi) as [Hn | (e & He & HPe)].
  - left; exact Hn.
  - right; exists e; split; [exact He | apply HPQ; exact HPe].
Qed.

(* the UART page is a mapped (device) vpn. *)
Lemma uart_kpt_mapped : kpt_mapped uart_vpn.
Proof.
  right. unfold kpt_dev_vpn.
  assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia.
Qed.

(* the UART leaf is a legal kernel-PT TLB entry. *)
Lemma P_kpt_uart (root : mword 44) : P_kpt root (kpt_tlb_ent root uart_vpn).
Proof. exists uart_vpn. split; [exact uart_kpt_mapped | reflexivity]. Qed.

(* the UART vpn's kernel-PT walk pages: root -> l1_dev -> l0_dev 32. *)
Lemma uart_l0_of_eq (root : mword 44) : kpt_l0_of root uart_vpn = kpt_l0_dev root 32.
Proof.
  unfold kpt_l0_of.
  assert (Z.leb 0x80000 (bv_unsigned uart_vpn) = false) as -> by (vm_compute; reflexivity).
  assert (bv_unsigned (vpn1_of uart_vpn) = 128) as -> by (vm_compute; reflexivity).
  unfold kpt_l0_dev. reflexivity.
Qed.

(* the UART leaf PTE flags are the device flags. *)
Lemma uart_lflags_eq : kpt_lflags uart_vpn = PTE_DEV.
Proof.
  unfold kpt_lflags.
  assert (Z.leb 0x80000 (bv_unsigned uart_vpn) = false) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* the three UART PTE-page slot addresses sit in RAM (both word ends). *)
Lemma uart_kpt_ram (root : mword 44) :
  kpt_ok root ->
  addr_is_ram (pte_addr_at root (subrange_vec_dec uart_vpn 26 18))
  /\ addr_is_ram (pa_add (pte_addr_at root (subrange_vec_dec uart_vpn 26 18)) 7)
  /\ addr_is_ram (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9))
  /\ addr_is_ram (pa_add (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9)) 7)
  /\ addr_is_ram (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0))
  /\ addr_is_ram (pa_add (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0)) 7).
Proof.
  intros Hok.
  pose proof (kpt_slot_ram root 0 (subrange_vec_dec uart_vpn 26 18) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr2 Hr2'].
  rewrite kpt_page_0 in Hr2. rewrite kpt_page_0 in Hr2'.
  pose proof (kpt_slot_ram root 1 (subrange_vec_dec uart_vpn 17 9) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr1 Hr1'].
  pose proof (kpt_slot_ram root 34 (subrange_vec_dec uart_vpn 8 0) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr0 Hr0'].
  change (kpt_l1_dev root) with (kpt_page root 1).
  rewrite uart_l0_of_eq. change (kpt_l0_dev root 32) with (kpt_page root 34).
  split; [exact Hr2|]. split; [exact Hr2'|]. split; [exact Hr1|].
  split; [exact Hr1'|]. split; [exact Hr0 | exact Hr0'].
Qed.

(* the three UART PTE bytes, sourced from the invariant's [kpt_mem]: the
   walk reads root[0]->l1_dev, l1_dev[128]->l0_dev 32, l0_dev 32[0]->uart leaf. *)
Lemma uart_kpt_bytes (root : mword 44) (s : mstate) :
  kpt_mem s root ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at root (subrange_vec_dec uart_vpn 26 18)) j)
     = Some (nth_byte (mk_pte (kpt_l1_dev root) PTE_PTR) j))
  /\ (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9)) j)
     = Some (nth_byte (mk_pte (kpt_l0_of root uart_vpn) PTE_PTR) j))
  /\ (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0)) j)
     = Some (nth_byte (mk_pte (kpt_leaf_ppn uart_vpn) PTE_DEV) j)).
Proof.
  intros (H0 & _H2 & Hl1 & _Hl2 & Hleaf).
  assert (Huv2 : subrange_vec_dec uart_vpn 26 18 = (mword_of_int 0 : mword 9))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Huv1 : subrange_vec_dec uart_vpn 17 9 = (mword_of_int 128 : mword 9))
    by (apply bv_eq; vm_compute; reflexivity).
  split; [| split].
  - (* root[0] -> l1_dev *)
    rewrite Huv2. exact H0.
  - (* l1_dev[128] -> l0_dev 32 = l0_of uart_vpn *)
    intros j Hj.
    specialize (Hl1 (subrange_vec_dec uart_vpn 17 9)).
    rewrite Huv1 in Hl1.
    assert (Hi : 96 <= bv_unsigned (mword_of_int 128 : mword 9) < 129)
      by (assert (bv_unsigned (mword_of_int 128 : mword 9) = 128) as -> by (vm_compute; reflexivity); lia).
    specialize (Hl1 Hi j Hj).
    (* l0_dev (128-96) = l0_dev 32 = l0_of uart_vpn *)
    assert (Hle : kpt_l0_dev root (bv_unsigned (mword_of_int 128 : mword 9) - 96) = kpt_l0_of root uart_vpn).
    { rewrite uart_l0_of_eq. reflexivity. }
    rewrite Hle in Hl1. rewrite Huv1. exact Hl1.
  - (* l0 leaf -> uart leaf *)
    intros j Hj.
    specialize (Hleaf uart_vpn uart_kpt_mapped j Hj).
    unfold kpt_slot0_pa, vpn0_of, kpt_leaf_pte in Hleaf.
    rewrite uart_lflags_eq in Hleaf.
    exact Hleaf.
Qed.

(* the filled entry the UART walk installs IS the kernel PT's own uart entry. *)
Lemma uart_filled_is_kpt (root : mword 44) :
  uart_tlb_ent (kpt_leaf_ppn uart_vpn) (mk_pte (kpt_leaf_ppn uart_vpn) PTE_DEV)
    (kpt_slot0_pa root uart_vpn)
  = kpt_tlb_ent root uart_vpn.
Proof.
  unfold uart_tlb_ent, kpt_tlb_ent, kpt_leaf_pte. rewrite uart_lflags_eq. reflexivity.
Qed.

(* filling the UART hash slot with the uart entry preserves [tlb_consistent (P_kpt root)]. *)
Lemma uart_kpt_fill (root : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_consistent (P_kpt root) tlbvec ->
  tlb_consistent (P_kpt root)
    (vec_update_dec tlbvec (tlb_hash (__id 39) uart_vpn) (Some (kpt_tlb_ent root uart_vpn))).
Proof.
  intro Hcons.
  apply (tlb_consistent_fill (P_kpt root) tlbvec (kpt_tlb_ent root uart_vpn)
           (tlb_hash (__id 39) uart_vpn) (tlb_hash_range uart_vpn) (P_kpt_uart root) Hcons).
Qed.

(* ===================================================================== *)
(* Phase 2: the reworked device leaves, under the NATIVE kernel PT.        *)
(*   Plain [tlb_inv root_ppn] (which already maps the UART); NO [uart_map]  *)
(*   client resource -- the three UART PTE bytes come from the invariant's  *)
(*   [kpt_bytes] via [kpt_bytes_body_mem]->[kpt_mem]->[uart_kpt_bytes].     *)
(*   The walk pages/leaf are pinned to the kernel PT's own ([kpt_l1_dev],   *)
(*   [kpt_l0_of], [kpt_leaf_ppn], PTE_DEV), so the installed TLB entry IS    *)
(*   [kpt_tlb_ent root uart_vpn] and the fill re-seals [tlb_pt_consistent]. *)
(* ===================================================================== *)

Section UartKptWp.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{CID : CpuId}.
Existing Instance riscv_memGS.

Lemma wp_sb_uart_s_kpt (root_ppn : mword 44) (γ : gname) (off : Z) E (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : gmap regidx (mword 64)) (u u' : uart_state) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) in
  let p1 := kpt_l1_dev root_ppn in
  let p0 := kpt_l0_of root_ppn uart_vpn in
  let lppn := kpt_leaf_ppn uart_vpn in
  let lflags := PTE_DEV in
  let a0addr := pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0) in
  ↑minstretN ⊆ E ->
  (0 <= off < uart_size)%Z ->
  (* leaf-PTE facts (UART leaf: V set, R|W leaf, U/G clear, A/D preset) *)
  0 <= lflags < 256 ->
  (forall s', exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0))) s' = Some (false, s')) ->
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int lflags : mword 8)) = false ->
  (forall (mxr do_sum : bool) s', exec (check_PTE_permission (Store Data) Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s')) ->
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int lflags : mword 8))) ('b"1") = false ->
  update_PTE_Bits (mk_pte lppn lflags) (Store Data) = None ->
  (* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the walk's
     output page composes to [uart_pa off] (the UART identity mapping). *)
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  (* device write advances the UART *)
  uart_write u off storebyte = Some u' ->
  smode_config γ dq -∗
  tlb_inv root_ppn -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
  uart_frag u -∗
  ( smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗ gpr_file m -∗
    uart_frag u' -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) @ E {{ Φ }}.
Proof.
  intros ea a8 storebyte p1 p0 lppn lflags a0addr HN Hoff
    Hlf Hinv0 Hnl0 Hchk0 HG0 Hupd0 Hcanon Hvpn_def Hident Hpa Hwrite_u.
  iIntros "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Huf Hcont".
  iDestruct (smode_config_unbundle with "Hsm") as
    "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
  iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
  iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
  iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 1)) mstatus0 mie_v mdv0 menvcfg0
            HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
            with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
  iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
    "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
  iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
    "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
  iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
  iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1)) by (apply lookup_lookup_total_dom; apply Hdom).
  assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2)) by (apply lookup_lookup_total_dom; apply Hdom).
  (* SOURCE the PTE bytes + RAM facts from the invariant's kpt_bytes *)
  iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
  iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hkptmem.
  pose proof (uart_kpt_bytes root_ppn σ Hkptmem) as (Hb2 & Hb1 & Hb0).
  pose proof (uart_kpt_ram root_ppn Hok) as (Hram2 & Hram2' & Hram1 & Hram1' & Hram0 & Hram0').
  iDestruct "Hdev" as "[Hua Hpldev]".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0) by (unfold s_pc; tmig; exact Lsatp).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0) by (unfold s_pc; tmig; exact Lpmpc).
  assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00) by (unfold s_pc; tmig; exact Lpmpaddr).
  assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f) by (unfold s_pc; tmig; exact Ltlb).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Hmem_pc : s_pc.(mem) = σ.(mem)) by (unfold s_pc, set_reg; reflexivity).
  assert (Hmdev_pc : s_pc.(mdev) = σ.(mdev)) by (unfold s_pc, set_reg; reflexivity).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at root_ppn (subrange_vec_dec uart_vpn 26 18))) as (region2 & Hm2r & Hpte2).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9))) as (region1 & Hm1r & Hpte1).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0))) as (region0 & Hm0r & Hpte0).
  assert (Hmatch2 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at root_ppn (subrange_vec_dec uart_vpn 26 18))) 8 = Some region2)
    by (rewrite Lpma_pc; exact Hm2r).
  assert (Hmatch1 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9))) 8 = Some region1)
    by (rewrite Lpma_pc; exact Hm1r).
  assert (Hmatch0 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0))) 8 = Some region0)
    by (rewrite Lpma_pc; exact Hm0r).
  assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s_pc.(sregs)) Supervisor) s_pc = Some (Supervisor, s_pc)).
  { unfold effectivePrivilege. cbn [generic_neq generic_eq].
    rewrite Lms_pc. rewrite HMPRV. cbn [andb]. apply exec_returnm. }
  assert (Hss : exec (is_shadow_stack_access (Store Data)) s_pc = Some (false, s_pc))
    by (unfold is_shadow_stack_access; apply exec_returnM).
  assert (HSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (HmisaS_pc : eq_vec (_get_Misa_S (register_lookup misa s_pc.(sregs))) ('b"1") = true) by (rewrite Lmisa_pc; exact HmisaS).
  assert (HA_pc : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s_pc.(sregs)) 0)) = TOR) by (rewrite Lpmpc_pc; exact HA0).
  assert (Hord_pc : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s_pc.(sregs)) 0) = false) by (rewrite Lpmpaddr_pc; exact Hord0).
  assert (HR_pc : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s_pc.(sregs)) 0)) ('b"1") = true) by (rewrite Lpmpc_pc; exact HR).
  assert (Hcov_pc : ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s_pc.(sregs)) 0) * 4) by (rewrite Lpmpaddr_pc; exact Hcov).
  (* the UART data translate, feeding the invariant's [P_kpt] consistency
     weakened to [P_uart4k] (P_kpt ⟹ P_uart4k by or_introl). *)
  destruct (exec_translateAddr_uart (Store Data) root_ppn p1 p0 lppn lflags
              region2 region1 region0 menvcfg0 satp0 a8 (uart_pa off) s_pc
              Hlf Hinv0 Hnl0 Hchk0 HG0 Hupd0 Heff Hss
              Lpriv_pc HSXL_pc Lsatp_pc Hmode Hppn Hasid HmisaS_pc Lmenv_pc HPBMTE
              HA_pc Hord_pc HR_pc Hcov_pc
              Hram2 Hram2' Hram1 Hram1' Hram0 Hram0'
              Hmatch2 Hpte2 Hmatch1 Hpte1 Hmatch0 Hpte0
              Hb2 Hb1 Hb0 Lhtif_pc Hcanon Hvpn_def Hident
              tlbvec_f eq_refl eq_refl Ltlb_pc
              (tlb_consistent_mono (P_kpt root_ppn)
                 (P_uart4k root_ppn lppn (mk_pte lppn lflags) a0addr) tlbvec_f
                 (fun e HP => or_introl HP) Hconsf))
    as (s' & Htr_uart & Hs'case).
  destruct (Hpma_all (uart_pa off) 1) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  assert (Hmem_s' : s'.(mem) = s_pc.(mem)) by (destruct Hs'case as [H|H]; rewrite H; reflexivity).
  assert (Hmdev_s' : s'.(mdev) = σ.(mdev))
    by (destruct Hs'case as [H|H]; rewrite H; [exact Hmdev_pc | unfold set_reg; cbn [mdev]; exact Hmdev_pc]).
  assert (Ls'cp : register_lookup cur_privilege s'.(sregs) = Supervisor) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpriv_pc | tmig; exact Lpriv_pc]).
  assert (Ls'ms : register_lookup mstatus s'.(sregs) = mstatus0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lms_pc | tmig; exact Lms_pc]).
  assert (Ls'pmpc : register_lookup pmpcfg_n s'.(sregs) = pmpcfg0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpmpc_pc | tmig; exact Lpmpc_pc]).
  assert (Ls'pmpaddr : register_lookup pmpaddr_n s'.(sregs) = pmpaddr00) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpmpaddr_pc | tmig; exact Lpmpaddr_pc]).
  assert (Ls'pma : register_lookup pma_regions s'.(sregs) = pmar0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpma_pc | tmig; exact Lpma_pc]).
  assert (Ls'htif : register_lookup htif_tohost_base s'.(sregs) = None) by (destruct Hs'case as [H|H]; rewrite H; [exact Lhtif_pc | tmig; exact Lhtif_pc]).
  assert (Hwr_uart : dev_write s'.(mdev) (uart_pa off) 1 storebyte = Some (set_duart σ.(mdev) u')).
  { rewrite Hmdev_s'. apply (dev_write_uart σ.(mdev) off storebyte u' Hoff). rewrite <- Hduart. exact Hwrite_u. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := MState s'.(sregs) s_pc.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_1_gpr_S_walk_dev rs2 rs1 imm region_st satp0 s_pc s' d'
               Hmem_s' Lpriv_pc HSXL_pc Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva Hpa; change (0 * 1)%Z with 0%Z; rewrite avi0; exact Htr_uart)
               Ls'cp ltac:(rewrite Ls'ms; exact HMPRV)
               ltac:(rewrite Ls'pmpc; exact HA0) ltac:(rewrite Ls'pmpaddr; exact Hord0)
               ltac:(rewrite Ls'pmpaddr !Lva Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov])
               ltac:(rewrite Ls'pmpc; exact HW)
               ltac:(rewrite Ls'pma !Lva Hpa; exact Hmatch_st)
               Hwrite_st
               ltac:(rewrite !Lva Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
               ltac:(rewrite !Lva Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
               ltac:(rewrite !Lva Hpa; apply within_htif_writable_false; exact Ls'htif)
               ltac:(rewrite !Lva Hpa; apply dev_addr_uart; exact Hoff)
               ltac:(rewrite !Lva !Lv2 Hpa; exact Hwr_uart)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev] Huf") as "[Hdev' Huf']".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { subst s_x; cbn [sregs]. destruct Hs'case as [H|H]; rewrite H; unfold s_pc; cbn [sregs].
    - rewrite register_lookup_set. reflexivity.
    - tmig. rewrite register_lookup_set. reflexivity. }
  (* the filled entry is the kernel PT's own uart entry *)
  assert (Hfe : uart_tlb_ent lppn (mk_pte lppn lflags) a0addr = kpt_tlb_ent root_ppn uart_vpn)
    by exact (uart_filled_is_kpt root_ppn).
  destruct Hs'case as [Hs'eq | Hs'eq].
  - (* TLB HIT: tlb cell unchanged, re-seal with Hconsf *)
    iModIntro. iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). exact Hstore. }
    iSplitL "Hreg Hmem Hdev'".
    { subst s_x; rewrite Hs'eq. unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
    iIntros "Hhs' Hpc'". iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytesb Hpmpc Hpmpa] [$Hpc' $Hnpc] [Hfmap] Huf'").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb [Hpbytesb] [Hpmpc Hpmpa]").
      - iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"].
      - iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  - (* TLB WALK: update the tlb cell, re-seal via the P_kpt fill *)
    set (tlbf := vec_update_dec tlbvec_f (tlb_hash (__id 39) uart_vpn) (Some (uart_tlb_ent lppn (mk_pte lppn lflags) a0addr))).
    iMod (reg_update _ tlb _ tlbf with "Hreg Htlb") as "[Hreg Htlb]".
    iModIntro. iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). exact Hstore. }
    iSplitL "Hreg Hmem Hdev'".
    { subst s_x; rewrite Hs'eq. unfold tlbf, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
    iIntros "Hhs' Hpc'". iEval (rewrite Lnpc) in "Hpc'".
    assert (Hfill : tlb_pt_consistent root_ppn tlbf).
    { unfold tlb_pt_consistent, tlbf. rewrite Hfe. apply uart_kpt_fill. exact Hconsf. }
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytesb Hpmpc Hpmpa] [$Hpc' $Hnpc] [Hfmap] Huf'").
    { iApply (tlb_inv_close root_ppn satp0 tlbf Hmode Hasid Hppn Hfill with "Hsatp Htlb [Hpbytesb] [Hpmpc Hpmpa]").
      - iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"].
      - iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
Qed.

(* The reworked S-mode UART LOAD (LB / LBU), mirror of the store. *)
Lemma wp_lb_uart_s_kpt (root_ppn : mword 44) (γ : gname) (off : Z) E (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) (imm : mword 12) (b : bv 8)
    (m : gmap regidx (mword 64)) (u u' : uart_state) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval : mword 64 := extend_value is_unsigned (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) b) in
  let p1 := kpt_l1_dev root_ppn in
  let p0 := kpt_l0_of root_ppn uart_vpn in
  let lppn := kpt_leaf_ppn uart_vpn in
  let lflags := PTE_DEV in
  let a0addr := pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0) in
  ↑minstretN ⊆ E ->
  (0 <= off < uart_size)%Z ->
  uint rd <> 0 ->
  0 <= lflags < 256 ->
  (forall s', exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0))) s' = Some (false, s')) ->
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int lflags : mword 8)) = false ->
  (forall (mxr do_sum : bool) s', exec (check_PTE_permission (Load Data) Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s')) ->
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int lflags : mword 8))) ('b"1") = false ->
  update_PTE_Bits (mk_pte lppn lflags) (Load Data) = None ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  uart_read u off = Some (b, u') ->
  smode_config γ dq -∗
  tlb_inv root_ppn -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
  uart_frag u -∗
  ( smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    gpr_file (<[Regidx rd := regval_into_reg ldval]> m) -∗
    uart_frag u' -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) @ E {{ Φ }}.
Proof.
  intros ea a8 ldval p1 p0 lppn lflags a0addr HN Hoff Hrd
    Hlf Hinv0 Hnl0 Hchk0 HG0 Hupd0 Hcanon Hvpn_def Hident Hpa Hread_u.
  iIntros "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Huf Hcont".
  iDestruct (smode_config_unbundle with "Hsm") as
    "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
  iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
  iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
  iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) mstatus0 mie_v mdv0 menvcfg0
            HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
            with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
  iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
    "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
  iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
    "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
  iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
  iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1)) by (apply lookup_lookup_total_dom; apply Hdom).
  assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd)) by (apply lookup_lookup_total_dom; apply Hdom).
  iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
  iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hkptmem.
  pose proof (uart_kpt_bytes root_ppn σ Hkptmem) as (Hb2 & Hb1 & Hb0).
  pose proof (uart_kpt_ram root_ppn Hok) as (Hram2 & Hram2' & Hram1 & Hram1' & Hram0 & Hram0').
  iDestruct "Hdev" as "[Hua Hpldev]".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0) by (unfold s_pc; tmig; exact Lsatp).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0) by (unfold s_pc; tmig; exact Lpmpc).
  assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00) by (unfold s_pc; tmig; exact Lpmpaddr).
  assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f) by (unfold s_pc; tmig; exact Ltlb).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Hmem_pc : s_pc.(mem) = σ.(mem)) by (unfold s_pc, set_reg; reflexivity).
  assert (Hmdev_pc : s_pc.(mdev) = σ.(mdev)) by (unfold s_pc, set_reg; reflexivity).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at root_ppn (subrange_vec_dec uart_vpn 26 18))) as (region2 & Hm2r & Hpte2).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9))) as (region1 & Hm1r & Hpte1).
  destruct (Hpma_imp pmar0 Hpma_all (pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0))) as (region0 & Hm0r & Hpte0).
  assert (Hmatch2 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at root_ppn (subrange_vec_dec uart_vpn 26 18))) 8 = Some region2) by (rewrite Lpma_pc; exact Hm2r).
  assert (Hmatch1 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9))) 8 = Some region1) by (rewrite Lpma_pc; exact Hm1r).
  assert (Hmatch0 : matching_pma_region (register_lookup pma_regions s_pc.(sregs))
            (Physaddr (pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0))) 8 = Some region0) by (rewrite Lpma_pc; exact Hm0r).
  assert (Heff : exec (effectivePrivilege (Load Data) (register_lookup mstatus s_pc.(sregs)) Supervisor) s_pc = Some (Supervisor, s_pc)).
  { unfold effectivePrivilege. cbn [generic_neq generic_eq]. rewrite Lms_pc. rewrite HMPRV. cbn [andb]. apply exec_returnm. }
  assert (Hss : exec (is_shadow_stack_access (Load Data)) s_pc = Some (false, s_pc))
    by (unfold is_shadow_stack_access; apply exec_returnM).
  assert (HSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (HmisaS_pc : eq_vec (_get_Misa_S (register_lookup misa s_pc.(sregs))) ('b"1") = true) by (rewrite Lmisa_pc; exact HmisaS).
  assert (HA_pc : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s_pc.(sregs)) 0)) = TOR) by (rewrite Lpmpc_pc; exact HA0).
  assert (Hord_pc : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s_pc.(sregs)) 0) = false) by (rewrite Lpmpaddr_pc; exact Hord0).
  assert (HR_pc : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s_pc.(sregs)) 0)) ('b"1") = true) by (rewrite Lpmpc_pc; exact HR).
  assert (Hcov_pc : ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s_pc.(sregs)) 0) * 4) by (rewrite Lpmpaddr_pc; exact Hcov).
  destruct (exec_translateAddr_uart (Load Data) root_ppn p1 p0 lppn lflags
              region2 region1 region0 menvcfg0 satp0 a8 (uart_pa off) s_pc
              Hlf Hinv0 Hnl0 Hchk0 HG0 Hupd0 Heff Hss
              Lpriv_pc HSXL_pc Lsatp_pc Hmode Hppn Hasid HmisaS_pc Lmenv_pc HPBMTE
              HA_pc Hord_pc HR_pc Hcov_pc
              Hram2 Hram2' Hram1 Hram1' Hram0 Hram0'
              Hmatch2 Hpte2 Hmatch1 Hpte1 Hmatch0 Hpte0
              Hb2 Hb1 Hb0 Lhtif_pc Hcanon Hvpn_def Hident
              tlbvec_f eq_refl eq_refl Ltlb_pc
              (tlb_consistent_mono (P_kpt root_ppn)
                 (P_uart4k root_ppn lppn (mk_pte lppn lflags) a0addr) tlbvec_f
                 (fun e HP => or_introl HP) Hconsf))
    as (s' & Htr_uart & Hs'case).
  destruct (Hpma_all (uart_pa off) 1) as (region_ld & Hmatch_ld & _ & Hread_ld & _ & _).
  assert (Hmdev_s' : s'.(mdev) = σ.(mdev))
    by (destruct Hs'case as [H|H]; rewrite H; [exact Hmdev_pc | unfold set_reg; cbn [mdev]; exact Hmdev_pc]).
  assert (Hmem_s' : s'.(mem) = s_pc.(mem)) by (destruct Hs'case as [H|H]; rewrite H; reflexivity).
  assert (Ls'cp : register_lookup cur_privilege s'.(sregs) = Supervisor) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpriv_pc | tmig; exact Lpriv_pc]).
  assert (Ls'ms : register_lookup mstatus s'.(sregs) = mstatus0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lms_pc | tmig; exact Lms_pc]).
  assert (Ls'pmpc : register_lookup pmpcfg_n s'.(sregs) = pmpcfg0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpmpc_pc | tmig; exact Lpmpc_pc]).
  assert (Ls'pmpaddr : register_lookup pmpaddr_n s'.(sregs) = pmpaddr00) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpmpaddr_pc | tmig; exact Lpmpaddr_pc]).
  assert (Ls'pma : register_lookup pma_regions s'.(sregs) = pmar0) by (destruct Hs'case as [H|H]; rewrite H; [exact Lpma_pc | tmig; exact Lpma_pc]).
  assert (Ls'htif : register_lookup htif_tohost_base s'.(sregs) = None) by (destruct Hs'case as [H|H]; rewrite H; [exact Lhtif_pc | tmig; exact Lhtif_pc]).
  assert (Hdrd_uart : dev_read s'.(mdev) (uart_pa off) 1 = Some (b, set_duart σ.(mdev) u')).
  { rewrite Hmdev_s'. apply (dev_read_uart σ.(mdev) off b u' Hoff). rewrite <- Hduart. exact Hread_u. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := set_reg (MState s'.(sregs) s'.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg ldval)).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x ldval.
    apply (exec_execute_LOAD_1_gpr_S_walk_dev rs1 rd imm is_unsigned b d' region_ld satp0 s_pc s'
             Hrd Lpriv_pc HSXL_pc Lsatp_pc Hmode
             ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
             ltac:(rewrite Lmenv_pc; exact Hpmm)
             ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
             ltac:(cbn [bits_of_virtaddr]; rewrite !Lva Hpa; change (0 * 1)%Z with 0%Z; rewrite avi0; exact Htr_uart)
             Ls'cp ltac:(rewrite Ls'ms; exact HMPRV)
             ltac:(rewrite Ls'pmpc; exact HA0) ltac:(rewrite Ls'pmpaddr; exact Hord0)
             ltac:(rewrite Ls'pmpaddr !Lva Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov])
             ltac:(rewrite Ls'pmpc; exact HR)
             ltac:(rewrite Ls'pma !Lva Hpa; exact Hmatch_ld)
             Hread_ld
             ltac:(rewrite !Lva Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
             ltac:(rewrite !Lva Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
             ltac:(rewrite !Lva Hpa; apply within_htif_false; exact Ls'htif)
             ltac:(rewrite !Lva Hpa; apply dev_addr_uart; exact Hoff)
             ltac:(rewrite !Lva Hpa; exact Hdrd_uart)). }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev] Huf") as "[Hdev' Huf']".
  assert (Hfe : uart_tlb_ent lppn (mk_pte lppn lflags) a0addr = kpt_tlb_ent root_ppn uart_vpn)
    by exact (uart_filled_is_kpt root_ppn).
  destruct Hs'case as [Hs'eq | Hs'eq].
  - (* TLB HIT *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg ldval) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg ldval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro. iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). exact Hload. }
    iSplitL "Hreg Hmem Hdev'".
    { subst s_x; rewrite Hs'eq. unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { subst s_x; cbn [sregs]. rewrite Hs'eq. tmig. unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytesb Hpmpc Hpmpa] [$Hpc' $Hnpc] [Hfmap] Huf'").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb [Hpbytesb] [Hpmpc Hpmpa]").
      - iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"].
      - iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iSplitR; [iPureIntro; intro r; rewrite dom_insert_L; apply elem_of_union_r; apply Hdom | iExact "Hfmap"].
  - (* TLB WALK: re-seal via the P_kpt fill *)
    set (tlbf := vec_update_dec tlbvec_f (tlb_hash (__id 39) uart_vpn) (Some (uart_tlb_ent lppn (mk_pte lppn lflags) a0addr))).
    iMod (reg_update _ tlb _ tlbf with "Hreg Htlb") as "[Hreg Htlb]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg ldval) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg ldval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro. iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). exact Hload. }
    iSplitL "Hreg Hmem Hdev'".
    { subst s_x; rewrite Hs'eq. unfold tlbf, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { subst s_x; cbn [sregs]. rewrite Hs'eq. tmig. unfold tlbf, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hfill : tlb_pt_consistent root_ppn tlbf).
    { unfold tlb_pt_consistent, tlbf. rewrite Hfe. apply uart_kpt_fill. exact Hconsf. }
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytesb Hpmpc Hpmpa] [$Hpc' $Hnpc] [Hfmap] Huf'").
    { iApply (tlb_inv_close root_ppn satp0 tlbf Hmode Hasid Hppn Hfill with "Hsatp Htlb [Hpbytesb] [Hpmpc Hpmpa]").
      - iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"].
      - iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iSplitR; [iPureIntro; intro r; rewrite dom_insert_L; apply elem_of_union_r; apply Hdom | iExact "Hfmap"].
Qed.

End UartKptWp.
