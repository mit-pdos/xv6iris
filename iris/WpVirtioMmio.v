(* WpVirtioMmio.v: the S-mode, width-4 virtio-mmio STORE and LOAD
   weakest-preconditions over the SIE-agnostic [sconf] bundle, stated against
   the RAW [virtio_frag] half.

   These are the instruction leaves [virtio_disk_init] (SpecVirtioDiskInit.v)
   is built from.  Like [uartinit]'s [wp_sb_uart_frag_s_sconf], they run
   BEFORE [dev_inv] is allocated -- [virtio_disk_init] RESETS the device
   (STATUS <- 0) and reprograms its queue, which no device invariant could
   tolerate -- so the caller OWNS [virtio_frag v] outright and gets
   [virtio_frag v'] back, rather than borrowing the shared half from
   [dev_inv].  Agreement against the authoritative half in [state_interp] is
   [WpVirtio.dev_interp_agree_virtio] / [dev_interp_update_virtio].

   The exec-level towers are WpPlicExec's width-4 device STORE/LOAD towers,
   which are window-generic (they take [dev_addr pa = true] plus the
   [dev_write]/[dev_read] transaction as premises); the virtio window's own
   geometry -- the routing past the uart and plic windows, the PMP/CLINT
   facts -- is WpVirtioExec.v.

   The translate side runs REGIME-BLIND through [sr_transform]/[sr_absorb]
   at [strans_regime], absorbing the device walk for any device vpn
   ([kpt_dev_vpn]); [kvmmake]'s [kvmmap(VIRTIO0,VIRTIO0,PGSIZE,R|W)] puts the
   virtio page (vpn 0x10001) inside that class.

   Structural note: a virtio-mmio READ does NOT change the device (no
   virtio-mmio register is read-sensitive, unlike the UART's RHR or a PLIC
   claim), so the LOAD leaf below leaves [state_interp]'s device half
   completely untouched -- it hands the SAME [virtio_frag v] back.          *)
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
Require Import KptPt KMap.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt SRegime.
Require Import IntrDefs WpSmodeIntr.
Require Import VirtioModel.
Require Import WpVirtio.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpVirtioExec.
Import Defs.

(* the width-4 store tower's store word [wv] is a double [autocast]/subrange of
   the register value: [wv = autocast (subrange_vec_dec vrs2 31 0)] with
   [vrs2 : mword 32].  Collapsing the redundant outer layer bridges it to the
   caller-facing single-layer [storeword].  (Same fact as WpPlic's twin; kept
   local so this file does not depend on the PLIC WP layer.) *)
Lemma v_subrange32_31_0_id (x : mword 32) : subrange_vec_dec x 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0%Z.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N in Hx.
  exact Hx.
Qed.

Lemma v_wv32_collapse (x : mword 32) :
  autocast (T := mword) (subrange_vec_dec x 31 0) = x.
Proof. rewrite v_subrange32_31_0_id. apply autocast_id. Qed.

Section WpVirtioMmio.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{CID : CpuId}.
Existing Instance riscv_memGS.

(* ===================================================================== *)
(* the raw-fragment width-4 virtio-mmio STORE                             *)
(* ===================================================================== *)

Lemma wp_sw_virtio_frag_s_sconf (γ : gname)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : regfile) (n : nat) (v v' : virtio_state) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  virtio_write v (uint a8 - virtio_base)%Z storeword = Some v' ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  virtio_frag v -∗
  ( sie_cap_gpr γ m n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    virtio_frag v' -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hvw.
  iIntros "Hcg Hpc Hinstr Hv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (Hpma_all a8 4) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hveq.
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
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iMod (sr_absorb strans_regime (Store Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc
          (or_intror (or_intror (or_introl eq_refl))) eq_refl Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
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
  assert (Hwr_virtio : dev_write s_tr.(mdev) a8 4 storeword = Some (set_dvirtio σ.(mdev) v')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_write_virtio σ.(mdev) a8 storeword v' Hrange).
    rewrite Hveq. exact Hvw. }
  pose (d' := set_dvirtio σ.(mdev) v').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply virtio_pmp_match4; [exact Hrange | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_st)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
               Hwrite_st
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_virtio; [exact Hrange | lia])
               ltac:(apply within_sig_virtio)
               ltac:(apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_virtio; exact Hrange)
               ltac:(rewrite !Lva !Lv2; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id;
                     change (8 * (0 + 1) * 4 - 1)%Z with 31%Z; change (8 * 0 * 4)%Z with 0%Z;
                     rewrite v_wv32_collapse; exact Hwr_virtio)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_virtio σ.(mdev) v v' with "Hdev Hv") as "[Hdev' Hv']".
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
  iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hv'").
Qed.

(* ===================================================================== *)
(* the raw-fragment width-4 virtio-mmio LOAD                              *)
(* ===================================================================== *)

(* Dual to [wp_sw_virtio_frag_s_sconf].  Because a virtio-mmio read leaves the
   device alone, the loaded word is DETERMINED by the owned [virtio_frag v]
   (premise [virtio_read v off = Some w]) and the same fragment comes back --
   there is no ghost update at all.  [rd] gets [extend_value is_unsigned] of
   the 32-bit word placed in the low half of a 64-bit zero word: for LW
   ([is_unsigned = false]) that is the SIGN-EXTENDED value, exactly as in the
   [dev_inv]-borrowing PLIC twin. *)
Lemma wp_lw_virtio_frag_s_sconf (γ : gname)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5)
    (imm : mword 12) (m : regfile) (n : nat) (v : virtio_state) (w : bv 32) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval : mword 64 :=
        extend_value is_unsigned
          (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) w) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  uint rd <> 0 ->
  rd <> csp_rs1 ->
  virtio_read v (uint a8 - virtio_base)%Z = Some w ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  virtio_frag v -∗
  ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg ldval]> m) n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    virtio_frag v -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hrdnz Hrdsp Hvr.
  iIntros "Hcg Hpc Hinstr Hv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (Hpma_all a8 4) as (region_ld & Hmatch_ld & _ & Hread_ld & _ & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hveq.
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
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iMod (sr_absorb strans_regime (Load Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc
          (or_intror (or_introl eq_refl)) I Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
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
  (* the virtio read does NOT advance the device: the post-read device state is
     the ENTRY device state, so [state_interp]'s device half needs no update *)
  assert (Hdrd_virtio : dev_read s_tr.(mdev) a8 4 = Some (w, σ.(mdev))).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_read_virtio σ.(mdev) a8 w Hrange).
    rewrite Hveq. exact Hvr. }
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) σ.(mdev))
                 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg ldval)).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s_pc
                  = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_4_gpr_S_walk_dev rs1 rd imm is_unsigned w σ.(mdev) region_ld s_pc s_tr
             Hrdnz Htea
             ltac:(rewrite !Lva; exact Halign)
             ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply virtio_pmp_match4; [exact Hrange | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_ld)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
             Hread_ld
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_virtio; [exact Hrange | lia])
             ltac:(apply within_sig_virtio)
             ltac:(apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_virtio; exact Hrange)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hdrd_virtio)). }
  iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg ldval) with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz rd _ Hrdnz).
  iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg ldval) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz rd _ Hrdnz). iExact "Hrdc". }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev".
  { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x, set_reg; cbn [sregs]. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg ldval]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_retarget γ m
               (<[Regidx rd := regval_into_reg ldval]> m) n Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hv").
Qed.

End WpVirtioMmio.
