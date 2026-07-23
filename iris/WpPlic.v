(* WpPlic.v: the S-mode, width-4 PLIC MMIO STORE weakest-precondition over
   the SIE-agnostic [sconf] bundle.

   A width-1 -> width-4 adaptation of [wp_sb_uart_s_sconf] (WpSconfUart.v),
   with the UART device leaf swapped for the width-4 PLIC device-store tower
   ([exec_execute_STORE_4_gpr_S_walk_dev], WpPlicExec.v).  The device ghost is
   handled through the RAW [plic_frag] half (the caller owns [plic_frag p] and
   gets back [plic_frag p'] in the continuation) instead of through a
   [dev_inv] invariant + uart-style accessor.  The translate side still runs
   REGIME-BLIND through [sr_transform]/[sr_absorb_dev] at the derived regime
   instance [strans_regime] (the folded translation slot [Htr] threads
   straight through, no skolem-root open or repack), absorbing the
   device walk for ANY device vpn ([kpt_dev_vpn]).                          *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import DevModel RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import KptPt.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt SRegime.
Require Import PlicPlan WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpPlicExec.
Import Defs.

(* the width-4 store tower's store word [wv] is a double [autocast]/subrange of
   the register value: [wv = autocast (subrange_vec_dec vrs2 31 0)] with
   [vrs2 : mword 32].  Collapsing the redundant outer layer bridges it to the
   caller-facing single-layer [storeword]. *)
Lemma subrange32_31_0_id (x : mword 32) : subrange_vec_dec x 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N in Hx.
  exact Hx.
Qed.

Lemma wv32_collapse (x : mword 32) :
  autocast (T := mword) (subrange_vec_dec x 31 0) = x.
Proof. rewrite subrange32_31_0_id. apply autocast_id. Qed.

Section WpPlic.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{!uartGhostG Σ}.
Context `{CID : CpuId}.
Existing Instance riscv_memGS.

Lemma wp_sw_plic_s_sconf (γ : gname)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : regfile) (n : nat) (p p' : plic_state) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8)) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
  plic_write p (uint a8 - plic_base)%Z storeword = Some p' ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  plic_frag p -∗
  ( sie_cap_gpr γ m n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    plic_frag p' -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hident Hpw.
  iIntros "Hcg Hpc Hinstr Hp Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  destruct (Hpma_all a8 4) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "[Hua Hpldev]".
  iDestruct (plic_agree with "Hpldev Hp") as %Hpeq.
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  iMod (sr_absorb_dev strans_regime (Store Data) a8 s_pc
          (or_intror eq_refl) Hdevvpn Hcanon Hident
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' with "Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_plic : dev_write s_tr.(mdev) a8 4 storeword = Some (set_dplic σ.(mdev) p')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_write_plic σ.(mdev) a8 storeword p' Hrange).
    rewrite <- Hpeq. exact Hpw. }
  pose (d' := set_dplic σ.(mdev) p').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply plic_pmp_match4; [exact Hrange | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_st)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
               Hwrite_st
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_plic; [exact Hrange | lia])
               ltac:(apply within_sig_plic)
               ltac:(apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_plic; exact Hrange)
               ltac:(rewrite !Lva !Lv2; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id;
                     change (8 * (0 + 1) * 4 - 1)%Z with 31%Z; change (8 * 0 * 4)%Z with 0%Z;
                     rewrite wv32_collapse; exact Hwr_plic)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_plic σ.(mdev) p p' with "[$Hua $Hpldev] Hp") as "[Hdev' Hp']".
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hp'").
Qed.

(* The SAME width-4 PLIC store, but for code that runs CONCURRENTLY on every
   hart and therefore cannot own [plic_frag] across its step: the shared half
   lives in the device invariant and this leaf borrows it by opening [dev_inv]
   around the (atomic) write.  Nothing about the PLIC survives into the
   continuation -- what the caller gets instead is that the invariant, i.e.
   the kernel's PLIC plan [plic_ok] (PlicPlan.v), still holds.  The caller's
   obligation is correspondingly universal: the write must be DEFINED and must
   preserve the plan at EVERY state the plan admits, since the caller cannot
   know what the other harts have written. *)
Lemma wp_sw_plic_dev_s_sconf (γ : gname) (γd : uart_names)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : regfile) (n : nat) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8)) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
  (forall p, plic_ok p ->
     exists p', plic_write p (uint a8 - plic_base)%Z storeword = Some p' /\ plic_ok p') ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  dev_inv γd -∗
  ( sie_cap_gpr γ m n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hident Hwrite.
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  destruct (Hpma_all a8 4) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "[Hua Hpldev]".
  iInv "Hdinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u p) "(Huf & Hplf & Hg & %Hpok)".
  iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
  destruct (Hwrite p Hpok) as (p' & Hpw & Hpok').
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  iMod (sr_absorb_dev strans_regime (Store Data) a8 s_pc
          (or_intror eq_refl) Hdevvpn Hcanon Hident
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' with "Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_plic : dev_write s_tr.(mdev) a8 4 storeword = Some (set_dplic σ.(mdev) p')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_write_plic σ.(mdev) a8 storeword p' Hrange).
    rewrite <- Hpeq. exact Hpw. }
  pose (d' := set_dplic σ.(mdev) p').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply plic_pmp_match4; [exact Hrange | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_st)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
               Hwrite_st
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_plic; [exact Hrange | lia])
               ltac:(apply within_sig_plic)
               ltac:(apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_plic; exact Hrange)
               ltac:(rewrite !Lva !Lv2; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id;
                     change (8 * (0 + 1) * 4 - 1)%Z with 31%Z; change (8 * 0 * 4)%Z with 0%Z;
                     rewrite wv32_collapse; exact Hwr_plic)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_plic σ.(mdev) p p' with "[$Hua $Hpldev] Hplf") as "[Hdev' Hp']".
  iMod ("Hdclose" with "[Huf Hp' Hg]") as "_".
  { iNext. iExists u, p'. iFrame. iPureIntro. exact Hpok'. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
Qed.

(* The width-4 PLIC MMIO LOAD, dual to [wp_sw_plic_dev_s_sconf].  A PLIC read
   can MUTATE the device (a claim takes a source: it clears that source's
   pending bit and marks it claimed), so it too runs with [dev_inv] open across
   the step.  The caller's obligation is again universal over every state the
   kernel's plan admits, and in exchange it may name a property [P] of the value
   read that holds at all of them -- that is how [plic_claim] learns its result
   is one of the machine's own interrupt ids. *)
Lemma wp_lw_plic_dev_s_sconf (γ : gname) (γd : uart_names)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5)
    (imm : mword 12) (m : regfile) (n : nat) (P : bv 32 -> Prop) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval := fun (v : bv 32) =>
        (extend_value is_unsigned
           (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v) : mword 64) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8)) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
  uint rd <> 0 ->
  rd <> csp_rs1 ->
  (forall p, plic_ok p ->
     exists v p', plic_read p (uint a8 - plic_base)%Z = Some (v, p') /\ plic_ok p' /\ P v) ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  dev_inv γd -∗
  ( ∀ v : bv 32,
    ⌜ P v ⌝ -∗
    sie_cap_gpr γ (<[Regidx rd := regval_into_reg (ldval v)]> m) n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hident Hrd Hrdsp Hread.
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  destruct (Hpma_all a8 4) as (region_ld & Hmatch_ld & _ & Hread_ld & _ & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "[Hua Hpldev]".
  iInv "Hdinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u p) "(Huf & Hplf & Hg & %Hpok)".
  iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
  destruct (Hread p Hpok) as (v & p' & Hrd_p & Hpok' & HPv).
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Load Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  iMod (sr_absorb_dev strans_regime (Load Data) a8 s_pc
          (or_introl eq_refl) Hdevvpn Hcanon Hident
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' with "Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hdrd_plic : dev_read s_tr.(mdev) a8 4 = Some (v, set_dplic σ.(mdev) p')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_read_plic σ.(mdev) a8 v p' Hrange).
    rewrite <- Hpeq. exact Hrd_p. }
  pose (d' := set_dplic σ.(mdev) p').
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) d')
                 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ldval v))).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s_pc
                  = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_4_gpr_S_walk_dev rs1 rd imm is_unsigned v d' region_ld s_pc s_tr
             Hrd Htea
             ltac:(rewrite !Lva; exact Halign)
             ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply plic_pmp_match4; [exact Hrange | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_ld)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
             Hread_ld
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_plic; [exact Hrange | lia])
             ltac:(apply within_sig_plic)
             ltac:(apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_plic; exact Hrange)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hdrd_plic)). }
  iMod (dev_interp_update_plic σ.(mdev) p p' with "[$Hua $Hpldev] Hplf") as "[Hdev' Hp']".
  iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (ldval v)) with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz rd _ Hrd).
  iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ldval v)) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
  iMod ("Hdclose" with "[Huf Hp' Hg]") as "_".
  { iNext. iExists u, p'. iFrame. iPureIntro. exact Hpok'. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x, set_reg; cbn [sregs]. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (ldval v)]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_retarget γ m
               (<[Regidx rd := regval_into_reg (ldval v)]> m) n Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" $! v with "[%] Hcg [$Hpc' $Hnpc]").
  { exact HPv. }
Qed.

End WpPlic.
