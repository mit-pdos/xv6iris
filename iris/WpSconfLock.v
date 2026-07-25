(* WpSconfLock.v -- SIE-agnostic lock-invariant leaves (interrupt-sweep
   stage 5): [sconf]+[sie_cap] twins of WpSmodePtLock.v's leaves.  The
   lock invariant is opened around the funnel callback's own step
   (lockN is disjoint from minstretN and intrN, so the open works in
   BOTH sie_cap arms -- in particular while the absorbing engine's
   interrupt invariant is closed).                                       *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import RegFile.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt WpSmodePtMem WpSmodePtLock WpAmo.
Require Import UserBits.
Require Import WpLock.
Require Import SRegime.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* helper copies (Local in WpSmodePtMem.v / WpSmodePtLock.v). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
  Proof.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
  Qed.

Section WpSconfLock.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!lockG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_clw_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γl lk s R -∗
    ( ∀ v : mword 32,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_instr_s_sconf γ m n Φ pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* the lock word's OWN base claim + canonicality (peek byte 0, refold) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
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
    iMod (sr_absorb strans_regime (Load Data) pa (pa_of ppn pa) ppn KP_rw s_pc
            (or_intror (or_introl eq_refl)) I
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte v) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram3 & Hkd).
    destruct (Hpma_all (pa_of ppn pa) 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr pa))) (Load Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr pa)) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr (pa_of ppn pa) Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; cbn [bits_of_virtaddr]; rewrite avi0_mul4; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               Hrange_ld HR
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hread_ld Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)
               Hbytesf_tr). }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (sign_extend' 64 v)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iMod ("Hclose" with "[Hbytes Hbr]") as "_".
    { iNext. iExists v. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iExact "Hbr". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iApply ("Hcont" $! v with "Hcg [$Hpc' $Hnpc]").
  Qed.

  (* the read-while-HOLDING twin: the free branch of the lock invariant
     is refuted by token exclusivity, so the read provably sees a
     nonzero word and the token rides through untouched.               *)
  Lemma wp_clw_lockinv_locked_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γl lk s R -∗
    locked γl -∗
    ( ∀ v : mword 32,
      ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
      locked γl -∗
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_instr_s_sconf γ m n Φ pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct "Hbr" as "[(_ & >Htok2 & _) | >%Hvnz]".
    { iExFalso. iApply (locked_exclusive with "Htok Htok2"). }
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* the lock word's OWN base claim + canonicality (peek byte 0, refold) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
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
    iMod (sr_absorb strans_regime (Load Data) pa (pa_of ppn pa) ppn KP_rw s_pc
            (or_intror (or_introl eq_refl)) I
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte v) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram3 & Hkd).
    destruct (Hpma_all (pa_of ppn pa) 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr pa))) (Load Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr pa)) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr (pa_of ppn pa) Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; cbn [bits_of_virtaddr]; rewrite avi0_mul4; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               Hrange_ld HR
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hread_ld Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)
               Hbytesf_tr). }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (sign_extend' 64 v)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iMod ("Hclose" with "[Hbytes]") as "_".
    { iNext. iExists v. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iRight. iPureIntro. exact Hvnz. }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iApply ("Hcont" $! v with "[//] Htok Hcg [$Hpc' $Hnpc]").
  Qed.



  (* ------------------------------------------------------------------- *)
  (* sw zero -- release's unlock store through the lock invariant: the    *)
  (* token and R go back in with the zeroed word.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sw_zero_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    is_lock γl lk s R -∗
    locked γl -∗
    R -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk.
    set (storeval := (mword_of_int 0 : mword 32)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok HRes Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes _]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* the lock word's OWN base claim + canonicality (peek byte 0, refold) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
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
    iMod (sr_absorb strans_regime (Store Data) pa (pa_of ppn pa) ppn KP_rw s_pc
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte w) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(_ & Hram0 & Hram3 & Hkd).
    destruct (Hpma_all (pa_of ppn pa) 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr pa))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr pa)) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval)
                              s_tr.(mdev))).
    { pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
 pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr (pa_of ppn pa)
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; cbn [bits_of_virtaddr]; rewrite avi0_mul4; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               Hrange_st HW
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) w Hpalign4 with "Hbytes") as "Hbytes".
    iMod (word4_pointsto_write_c s_tr.(mem) pa ppn w storeval Hcan Hoff with "Hk Hmem Hbytes") as "[Hmem Hbytes]".
    iMod ("Hclose" with "[Hbytes Htok HRes]") as "_".
    { iNext. iExists storeval. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iExact "Hbytes". }
      iLeft. iFrame "Htok HRes". iPureIntro. reflexivity. }
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.



  (* ------------------------------------------------------------------- *)
  (* amoswap.w.aq -- acquire's CAS through the lock invariant: the old    *)
  (* word's disjunct (w=0 ∗ locked ∗ R | w≠0) goes to the caller, the     *)
  (* swapped-in nonzero mark reseals the invariant.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_amoswap_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (zeros' 64) in
    pa = lk ->
    neq_vec (sign_extend' 64 (amoswap_stored (m !!! Regidx rs2))) zero_reg = true ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) -∗
    is_lock γl lk s R -∗
    ( ∀ w : mword 32,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) n -∗
      pc_is (add_vec_int pc 4) -∗
      (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked γl ∗ R
       ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hstz Hrd Hrdsp.
    set (a8 := pa). set (ea := pa).
    iIntros "Hcg Hpc Hinstr #Hlock Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg [Hmem Hdev]]".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    (* the lock word's OWN base claim + canonicality (peek byte 0, refold) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    assert (Halignp4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halignp4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
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
    assert (Hea_pc : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                             (zeros' 64) = pa)
      by (rewrite Lva; reflexivity).
    assert (Ha8_pc : sign_extend' 64 (subrange_vec_dec
                       (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                                (zeros' 64)) (xlen - 0 - 1) 0) = pa)
      by (rewrite Hea_pc subrange_id sign_extend'_id; reflexivity).
    iDestruct (sr_transform strans_regime (Atomic (AMOSWAP, Data, Data))
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (zeros' 64))
                 s_pc (or_intror (or_intror (or_intror eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_amo_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_amo_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iMod (sr_absorb strans_regime (Atomic (AMOSWAP, Data, Data)) pa (pa_of ppn pa) ppn KP_rw s_pc
            (or_intror (or_intror (or_intror eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_amo_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_amo s_pc)
            Lpma_pc' with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_tr with "Hreg Hr2c") as %Lv2_tr.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte w) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram3 & Hkd).
    destruct (Hpma_all (pa_of ppn pa) 4) as (region_amo & Hmatch_amo & _ & Hread_amo & Hwrite_amo & Hatomic_supp_amo).
    assert (Hatomic_amo : pma_allows_atomic_op
              ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
              AMOSWAP 4 = true)
      by (rewrite Hatomic_supp_amo; vm_compute; reflexivity).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwhr.
    pose proof (within_htif_writable_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwhw.
    assert (Htr_pc : exec (translateAddr (Virtaddr pa) (Atomic (AMOSWAP, Data, Data))) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { exact Htr0. }
    pose (s_x := set_reg (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 (amoswap_stored (m !!! Regidx rs2))) s_tr.(mdev))
                   (R_bitvector_64 (gpr_of_Z (uint rd)))
                   (regval_into_reg (amoswap_loaded w))).
    assert (Hexec : exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s_pc
                    = Some (RETIRE_SUCCESS, s_x)).
    { pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
 rewrite (exec_execute_AMOSWAP_4_gpr_S_walk_pt rs2 rs1 rd region_amo w s_pc s_tr (pa_of ppn pa) Hrd
                 Htea
                 ltac:(rewrite Ha8_pc; exact Halignp4)
                 ltac:(rewrite Ha8_pc; exact Htr_pc)
                 Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                 HA0 Hord0
                 Hrange_ld HR
                 HW
                 ltac:(rewrite Lpma_tr; exact Hmatch_amo)
                 (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halignp4)
                 Hread_amo Hwrite_amo Hatomic_amo
                 Hwc Hws Hwhr Hwhw
                 (addr_is_ram_not_dev _ Hram0)
                 Hbytesf_tr).
      subst s_x. unfold amoswap_stored, amoswap_loaded.
      rewrite Lv2_tr. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (amoswap_loaded w)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (amoswap_loaded w))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) w Hpalign4 with "Hbytes") as "Hbytes".
    iMod (word4_pointsto_write_c s_tr.(mem) pa ppn w (amoswap_stored (m !!! Regidx rs2)) Hcan Hoff with "Hk Hmem Hbytes") as "[Hmem Hbytes]".
    iMod ("Hclose" with "[Hbytes]") as "_".
    { iNext. iExists (amoswap_stored (m !!! Regidx rs2)). iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iExact "Hbytes". }
      iRight. iPureIntro. exact Hstz. }
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hexec. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x, set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { unfold s_x, set_reg; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (amoswap_loaded w)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iNext.
    iApply ("Hcont" $! w with "Hcg [$Hpc' $Hnpc] Hbr").
  Qed.


End WpSconfLock.
