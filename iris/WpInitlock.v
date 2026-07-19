(* WpInitlock.v -- whole-function S-mode WP for xv6's initlock().

     void initlock(struct spinlock *lk, char *name) {
       lk->name = name;   // c.sd  a1,8(a0)
       lk->locked = 0;    // sw    zero,0(a0)
       lk->cpu = 0;       // sd    zero,16(a0)
     }

   initlock @ 0x80000b88 (offsets +0x00 .. +0x18), 11 instructions:
     +0x00  1141      c.addi  sp,sp,-16
     +0x02  e406      c.sdsp  ra,8(sp)
     +0x04  e022      c.sdsp  s0,0(sp)
     +0x06  0800      c.addi4spn s0,sp,16
     +0x08  e50c      c.sd    a1,8(a0)      lk->name = name
     +0x0a  00052023  sw      zero,0(a0)    lk->locked = 0
     +0x0e  00053823  sd      zero,16(a0)   lk->cpu = 0
     +0x12  60a2      c.ldsp  ra,8(sp)
     +0x14  6402      c.ldsp  s0,0(sp)
     +0x16  0141      c.addi  sp,sp,16
     +0x18  8082      c.ret

   The function makes no sub-calls, holds ONE [smode_config] end-to-end, and
   never touches the interrupt-nesting state -- so its spec needs neither a
   ghost SIE half nor [intr_count].  It owns the spinlock's three struct fields
   (locked : 4B @ +0, name : 8B @ +8, cpu : 8B @ +16) as raw memory and hands
   them back initialised.  The [locked := 0] store is a plain 4-byte zero store
   over a PLAINLY-owned word (the lock is not yet an invariant) -- for that we
   build [wp_sw_zero_s], the width-4 sibling of [wp_sd_zero_s]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtTreeAdue.
Require Import SmodeCore WpSmodeGpr WpPushOffMem WpAmo WpLock.
Require Import KptTree SmodeCorePt SRegime WpSmodePtLeaves WpSmodePtMem.
Require Import WpSmodePtAlu WpSmodePtCtl WpSmodePtMemWrap.
Require Import WpRelease.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode facts specific to initlock: the c.sd (CS-form) and the two      *)
(* 32-bit zero stores.  (The prologue/epilogue RVC decodes reuse the      *)
(* shared [mdec_*] from KernelRvcDecode.v.)                               *)
(* ===================================================================== *)
Lemma ildc_e50c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe50c : mword 16)) s
  = Some (C_SD (mword_of_int 1, Cregidx (mword_of_int 2), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma ildb_00052023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00052023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma ildb_00053823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00053823 : mword 32)) s
  = Some (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8), s).
Proof. decode_bridge_ms. Qed.

Section InitlockLeaf.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ===== the plain 4-byte zero store [sw zero, imm(rs1)] over a PLAINLY-  *)
  (*       owned word.  Width-4 sibling of [wp_sd_zero_s_r]; cloned from    *)
  (*       it with the width-8 store tower swapped for the width-4 one.     *)
  Lemma wp_sw_zero_s_r (Rg : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (mword_of_int 0 : mword 32) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv Rg -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (word4_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_s_config_regime Rg Φ pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (word4_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (word4_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hb") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform Rg (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htlbinv") as %Htea.
    iMod (sr_absorb Rg (Store Data) a8 s_pc
            (or_intror (or_intror (or_introl eq_refl))) Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)".
    destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
    pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov1) as Hrange_st.
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      replace pa with a8 by (unfold pa; reflexivity).
      exact Htr0. }
    pose (s_x := MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) HW1
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      rewrite H0. subst s_x. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iDestruct (word4_pointsto_bytes with "Hbytes") as "Hraw".
    iMod (upd_window_4 s_tr.(mem) pa storeval vold with "Hmem Hraw") as "[Hmem Hraw]".
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) storeval Hpalign4 with "Hraw") as "Hbytes".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { unfold s_x; cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sw_zero_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      ea ↦₄ (mword_of_int 0 : mword 32) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_sw_zero_s_r (kpt_regime root_ppn) Φ pc rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_sw_zero_s_scfg_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ sr_inv Rg -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₄ (mword_of_int 0 : mword 32) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sw_zero_s_r Rg Φ pc rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_zero_s_scfg (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₄ (mword_of_int 0 : mword 32) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_sw_zero_s_scfg_r (kpt_regime root_ppn) γ Φ pc rs1 imm m vold (dq:=dq)).
  Qed.

End InitlockLeaf.

(* initlock's epilogue [c.addi sp,+16] undoes its prologue [c.addi sp,-16].
   (mword_of_int 48 : mword 6) is -16 in 6-bit two's complement. *)
Lemma initlock_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64) = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64) = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section Initlock.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation IL := KernelSyms.initlock.

  (* ===== instruction-DECODE facts (the [kernel_text -* instr] window) ===== *)
  Lemma ini_00 : kernel_text -∗ instr (mword_of_int (IL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IL + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (IL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma ini_02 : kernel_text -∗ instr (mword_of_int (IL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (IL + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (IL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma ini_04 : kernel_text -∗ instr (mword_of_int (IL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (IL + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (IL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma ini_06 : kernel_text -∗ instr (mword_of_int (IL + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (IL + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (IL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma ini_08 : kernel_text -∗ instr (mword_of_int (IL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)).
  Proof. mk_rvc (IL + 0x08)%Z (mword_of_int 0xe50c : mword 16)
    (mword_of_int (IL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)) ildc_e50c exec_execute_C_SD. Qed.

  Lemma ini_0a : kernel_text -∗ instr (mword_of_int (IL + 0x0a) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (IL + 0x0a)%Z (mword_of_int 0x00052023 : mword 32)
    (mword_of_int (IL + 0x0a) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)) ildb_00052023. Qed.

  Lemma ini_0e : kernel_text -∗ instr (mword_of_int (IL + 0x0e) : mword 64) false (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (IL + 0x0e)%Z (mword_of_int 0x00053823 : mword 32)
    (mword_of_int (IL + 0x0e) : mword 64) (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)) ildb_00053823. Qed.

  Lemma ini_12 : kernel_text -∗ instr (mword_of_int (IL + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (IL + 0x12)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (IL + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma ini_14 : kernel_text -∗ instr (mword_of_int (IL + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (IL + 0x14)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (IL + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma ini_16 : kernel_text -∗ instr (mword_of_int (IL + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IL + 0x16)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (IL + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma ini_18 : kernel_text -∗ instr (mword_of_int (IL + 0x18) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IL + 0x18)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (IL + 0x18) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* ============================================================= *)
  (* initlock: whole-function S-mode WP.  Owns the spinlock's three  *)
  (* struct fields as raw memory and returns them initialised;       *)
  (* makes no sub-calls (a pure prologue / three stores / epilogue). *)
  (* ============================================================= *)
  Lemma wp_initlock_r (Rg : s_regime) (Φ : mval -> iProp Σ)
      (γc : gname) (m : gmap regidx (mword 64))
      (vlock : bv 32) (vname vcpu : bv 64)
      (n : nat) {dq : dfrac} :
    let pcE : mword 64 := mword_of_int IL in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let name := m !!! Regidx (mword_of_int 11 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let c_name := add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)) in
    let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
    (2 <= n)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc dq -∗ sr_inv Rg -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    lk ↦₄ vlock -∗
    c_name ↦₈ vname -∗
    c_cpu ↦₈ vcpu -∗
    stack_own sp0 n -∗
    ( ∀ mr,
      smode_config γc dq -∗ sr_inv Rg -∗
      pc_is ret_tgt -∗ gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      c_name ↦₈ name -∗
      c_cpu ↦₈ (zero_reg : mword 64) -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE lk name sp0 ret_tgt c_name c_cpu Hn Hretm.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcfg Htlbinv #Htext Hpc Hfile Hlock Hname Hcpu Hstk Hcont".
    (* peel the 2-slot frame [spr, spr+16); the deep tail is held untouched. *)
    iDestruct (stack_own_split_1 sp0 2 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hras". iEval (rewrite -Hb2) in "Hs0s".
    iPoseProof (ini_00 with "Htext") as "Hi00".
    iPoseProof (ini_02 with "Htext") as "Hi02".
    iPoseProof (ini_04 with "Htext") as "Hi04".
    iPoseProof (ini_06 with "Htext") as "Hi06".
    iPoseProof (ini_08 with "Htext") as "Hi08".
    iPoseProof (ini_0a with "Htext") as "Hi0a".
    iPoseProof (ini_0e with "Htext") as "Hi0e".
    iPoseProof (ini_12 with "Htext") as "Hi12".
    iPoseProof (ini_14 with "Htext") as "Hi14".
    iPoseProof (ini_16 with "Htext") as "Hi16".
    iPoseProof (ini_18 with "Htext") as "Hi18".
    (* +0x00 c.addi sp,-16 *)
    iApply (wp_caddi_gpr_s_config_scfg_r Rg γc Φ pcE csp_rs1 (mword_of_int 48 : mword 6) m
              (dq:=dq) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (IL + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 vra0 (dq:=dq) with "Hcfg Htlbinv Hpc Hfile Hi02 [Hras] [-]").
    { iEval (rewrite HspR1). iExact "Hras". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hras".
    iEval (rewrite HspR1) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (IL + 0x02) : mword 64) 2 = mword_of_int (IL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 vs00 (dq:=dq) with "Hcfg Htlbinv Hpc Hfile Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1). iExact "Hs0s". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hs0s".
    iEval (rewrite HspR1) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (IL + 0x04) : mword 64) 2 = mword_of_int (IL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_gpr_s_config_scfg_r Rg γc Φ (mword_of_int (IL + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (dq:=dq) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HspR2 : R2 !!! Regidx csp_rs1 = spr).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (Hpp08 : add_vec_int (mword_of_int (IL + 0x06) : mword 64) 2 = mword_of_int (IL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sd a1,8(a0):  lk->name := a1 *)
    assert (Hea_name : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))) = c_name).
    { rewrite HR2a0. unfold c_name. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) R2 vname (dq:=dq)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [Hname] [-]").
    { iEval (rewrite Hea_name). iExact "Hname". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hname".
    iEval (rewrite Hea_name HR2a1) in "Hname".
    assert (Hpp0a : add_vec_int (mword_of_int (IL + 0x08) : mword 64) 2 = mword_of_int (IL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a sw zero,0(a0):  lk->locked := 0 *)
    assert (Hea_lock : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HR2a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_sw_zero_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x0a)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) R2 vlock (dq:=dq)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [Hlock] [-]").
    { iEval (rewrite Hea_lock). iExact "Hlock". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hlock".
    iEval (rewrite Hea_lock) in "Hlock".
    assert (Hpp0e : add_vec_int (mword_of_int (IL + 0x0a) : mword 64) 4 = mword_of_int (IL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e sd zero,16(a0):  lk->cpu := 0 *)
    assert (Hea_cpu : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x10 : mword 12)) = c_cpu).
    { rewrite HR2a0. reflexivity. }
    iApply (wp_sd_zero_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x0e)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x10 : mword 12) R2 vcpu (dq:=dq)
              with "Hcfg Htlbinv Hpc Hfile Hi0e [Hcpu] [-]").
    { iEval (rewrite Hea_cpu). iExact "Hcpu". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite Hea_cpu) in "Hcpu".
    assert (Hpp12 : add_vec_int (mword_of_int (IL + 0x0e) : mword 64) 4 = mword_of_int (IL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R2 (R1 !!! Regidx (mword_of_int 1 : mword 5)) (dq:=dq) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) with "Hcfg Htlbinv Hpc Hfile Hi12 [Hras] [-]").
    { iEval (rewrite HspR2). iExact "Hras". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hras".
    iEval (rewrite HspR2) in "Hras".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR2. }
    assert (Hpp14 : add_vec_int (mword_of_int (IL + 0x12) : mword 64) 2 = mword_of_int (IL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_r Rg γc Φ (mword_of_int (IL + 0x14)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R3 (R1 !!! Regidx (mword_of_int 8 : mword 5)) (dq:=dq) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) with "Hcfg Htlbinv Hpc Hfile Hi14 [Hs0s] [-]").
    { iEval (rewrite HspR3). iExact "Hs0s". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hs0s".
    iEval (rewrite HspR3) in "Hs0s".
    set (R4 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR3. }
    assert (Hpp16 : add_vec_int (mword_of_int (IL + 0x14) : mword 64) 2 = mword_of_int (IL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.addi sp,16 *)
    iApply (wp_caddi_gpr_s_config_scfg_r Rg γc Φ (mword_of_int (IL + 0x16)) csp_rs1 (mword_of_int 16 : mword 6) R4
              (dq:=dq) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4).
    assert (HR5ra : R5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert.
      unfold regval_into_reg.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hpp18 : add_vec_int (mword_of_int (IL + 0x16) : mword 64) 2 = mword_of_int (IL + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.ret *)
    iApply (wp_cret_s_zca_scfg_r Rg γc Φ (mword_of_int (IL + 0x18)) (mword_of_int 1) R5
              (dq:=dq) ltac:(vm_compute; discriminate)
              ltac:(rewrite HR5ra; exact Hretm)
              with "Hcfg Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite HR5ra) in "Hpc".
    (* rebundle the 2-slot frame with the untouched deep tail. *)
    iEval (rewrite Hb1) in "Hras". iEval (rewrite Hb2) in "Hs0s".
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Htop".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|].
      done. }
    iDestruct (stack_own_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! R5 with "Hcfg Htlbinv Hpc Hfile [%] Hlock Hname Hcpu Hstk").
    (* callee_saved m R5 *)
    assert (Hthread : forall c : mword 5, c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 1 ->
                R5 !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N1.
      rewrite /R5 lookup_total_insert_ne; [| congruence].
      rewrite /R4 lookup_total_insert_ne; [| congruence].
      rewrite /R3 lookup_total_insert_ne; [| congruence].
      rewrite /R2 lookup_total_insert_ne; [| congruence].
      rewrite /R1 lookup_total_insert_ne; [| congruence].
      reflexivity. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /R5 lookup_total_insert. rewrite HspR4.
      unfold regval_into_reg, spr. apply initlock_sp_cancel. }
    split.
    { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split.
    { (* s0 *)
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert.
      unfold regval_into_reg.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    (* s1..s11: untouched *)
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  Lemma wp_initlock (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γc : gname) (m : gmap regidx (mword 64))
      (vlock : bv 32) (vname vcpu : bv 64)
      (n : nat) {dq : dfrac} :
    let pcE : mword 64 := mword_of_int IL in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let name := m !!! Regidx (mword_of_int 11 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let c_name := add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)) in
    let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
    (2 <= n)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc dq -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    lk ↦₄ vlock -∗
    c_name ↦₈ vname -∗
    c_cpu ↦₈ vcpu -∗
    stack_own sp0 n -∗
    ( ∀ mr,
      smode_config γc dq -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗ gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      c_name ↦₈ name -∗
      c_cpu ↦₈ (zero_reg : mword 64) -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_initlock_r (kpt_regime root_ppn) Φ γc m vlock vname vcpu n (dq:=dq)).
  Qed.

End Initlock.
