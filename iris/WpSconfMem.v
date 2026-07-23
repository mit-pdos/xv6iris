(* WpSconfMem.v -- the SIE-AGNOSTIC data-leaf layer (interrupt-sweep
   stage 5): the [sconf]+[sie_cap] twins of the width-8 RVC LOAD/STORE
   exemplars (WpSmodePtLeaves.v's [wp_cld_s_pt]/[wp_csd_s_pt]), over the
   agnostic funnel [wp_instr_s_sconf].

   The data-side translation runs through the regime-blind absorption
   [sr_absorb strans_regime] INSIDE the funnel's σf-callback: the
   callback threads the FOLDED translation slot [strans_inv] (as "Htr")
   through [strans_regime] with NO skolem-root open, effective-address
   transform comes from [sr_transform strans_regime], and the post-
   translate PMP/PMA facts come from [sr_absorb]'s [pmp_grant_facts]
   conclusion (mirroring the R-generic `_r` data leaves).  The config
   facts (MPRV/SXL/MXR/PMM) come from [sconf]'s bundled fact sets
   instead of eight per-call premises.  Spec cleanups made in this pass:
     - the redundant [let ea := .. let a8 := ea let pa := a8] alias
       chain collapses to the single [let pa := ..];
     - ALL config premises are gone (SIE is decided by the ghost, the
       rest ride in [sconf_ms_facts]/the menvcfg conjunct);
     - the STORE needs no rd-premises at all (it writes no register,
       so [sie_cap] is not even retargeted); the LOAD keeps
       [uint rd <> 0] and [rd <> csp_rs1].
   The remaining WpSmodePtMem widths (4/1, base widths) follow this
   template mechanically.                                                *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodePte PtTreeAdue.
Require Import SmodeCore WpSmodeGpr.
Require Import KptTree SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import WpSmodeMemGen.
Require Import MemAccessGen.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.


(* helper copies (Local in WpSmodePtMem.v). *)
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

Section WpSconfMem.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* helper copies (Local in WpSmodePtMem.v): the width-generic window
     write and its width-4 instance. *)
  Local Lemma upd_window_bw {k : N} (mm : _) (pa : Arch.pa) (vnew vold : bv k)
      (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add pa j := nth_byte vnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof.
    iInduction l as [|x xs IH] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (mem_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x) with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

  Local Lemma upd_window_4 (mm : _) (pa : Arch.pa) (vnew vold : bv 32) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 4 vnew)
      ∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof. unfold write_bytes. change (N.to_nat 4) with 4%nat. apply upd_window_bw. Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ld rd, imm(rs1) -- width-8 RVC load.                               *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mulw (width : Z) (a : mword 64) : add_vec_int a (0 * width) = a.
  Proof. change (0 * width)%Z with 0%Z. apply avi0. Qed.

  Definition wordw_pointsto (width : Z) (a : Arch.pa) (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width), mem_pointsto (pa_add a j) dq (nth_byte w j))%I.

  Lemma wp_load_s_sconf_gen (width : Z) (c : bool) (γ : gname)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) {dqm : dfrac} :
    0 < width -> width <= 8 ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    extend_value false
      (update_subrange_vec_dec (zeros' (8*1*width)) (8*(0+1)*width-1) (8*0*width)
        (autocast (T := mword) v)) = lv ->
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, false, width)) -∗
    wordw_pointsto width pa dqm v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg lv]> m) n -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa dqm v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hw0 Hw8 Huintw Hread_plain Hlv pa Hrd Hrdsp.
    set (wlast := (Z.to_nat width - 1)%nat).
    assert (Hwn : Z.of_nat wlast = width - 1) by (unfold wlast; rewrite Nat2Z.inj_sub; [ rewrite Z2Nat.id; lia | lia ]).
    assert (Hwlt : (wlast < Z.to_nat width)%nat) by (unfold wlast; lia).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    rewrite /wordw_pointsto.
    iDestruct "Hbytes" as "(%Hpalign & Hbytes)".
    assert (Halign : is_aligned_vaddr (Virtaddr pa) width = true) by exact Hpalign.
    iApply (wp_instr_s_sconf γ m n Φ pc c
              (LOAD (imm, Regidx rs1, Regidx rd, false, width))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all pa width) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hmd : rf_to_gmap m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply rf_to_gmap_lookup).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa wlast)⌝)%I as %Hrampal.
    { iDestruct (big_sepL_lookup _ _ wlast wlast with "Hbytes") as "Hbl".
      { rewrite lookup_seq_lt; [reflexivity | exact Hwlt]. }
      iDestruct (mem_ram with "Hbl") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + width <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat wlast < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. rewrite Hwn. lia. }
      pose proof (uint_pa_add pa wlast Hnw) as Heq.
      destruct Hrampal as [_ Hhil]. rewrite Heq in Hhil. rewrite Hwn in Hhil.
      unfold ram_base, ram_size in *. lia. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if c then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if c then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
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
    iMod (sr_absorb_region strans_regime (Load Data) pa s_pc
            (or_intror (or_introl eq_refl)) Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htr")
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
    iAssert (⌜forall j : nat, (N.of_nat j < Z.to_N width)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < Z.to_nat width)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa width s_tr (addr_is_ram_not_in_clint _ Hrampa) Hw0) as Hwc.
    pose proof (within_sig_false pa width s_tr (addr_is_ram_not_in_sig _ Hrampa) Hw0) as Hws.
    pose proof (within_htif_false pa width s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, width))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg lv))).
    { rewrite <- Hlv.
      pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) width Hw0 Huintw Hlo Hfit Hcov) as Hrange_ld.
      apply (exec_execute_LOAD_w_gpr_S_walk_pt width Hw8 Hread_plain rs1 rd imm v region_ld s_pc s_tr Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign) ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hrange_ld) HR
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hpalign)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg lv)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg lv) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap".
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg lv)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg lv)).(sregs)
             = add_vec_int pc (if c then 2 else 4)).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (wordw_pointsto width pa dqm v)%I with "[Hbytes]" as "Hbw".
    { rewrite /wordw_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign. }
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx csp_rs1 ≠ Regidx rd) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg lv]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg lv]> m) n Hsp with "Hcap") as "Hcap".
    iAssert (gpr_file (<[Regidx rd := regval_into_reg lv]> m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; apply rf_to_gmap_dom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hbw").
  Qed.

  (* the loaded-value facts: extend_value of the generic data2 = the
     per-width value written to rd. *)
  Lemma data2_ext_8 (v : mword 64) :
    extend_value false
      (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) (autocast (T := mword) v)) = v.
  Proof. unfold extend_value. rewrite sign_extend'_id. rewrite autocast_id. apply data2_id. Qed.

  Lemma data2_ext_4 (v : mword 32) :
    extend_value false
      (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) (autocast (T := mword) v)) = sign_extend' 64 v.
  Proof.
    unfold extend_value. rewrite autocast_id. f_equal.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
  Qed.

  Lemma wp_cld_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈{ dqm } v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg v]> m) n -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 8 true γ Φ pc rd rs1 imm m n v v
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdsp
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_ld_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈{ dqm } v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg v]> m) n -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 8 false γ Φ pc rd rs1 imm m n v v
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdsp
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_clw_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄{ dqm } v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 4 true γ Φ pc rd rs1 imm m n v (sign_extend' 64 v)
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdsp
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_lw_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄{ dqm } v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 4 false γ Φ pc rd rs1 imm m n v (sign_extend' 64 v)
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdsp
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.sd rs2, imm(rs1) -- width-8 RVC store.  No register write, so no   *)
  (* rd premises and no [sie_cap] retarget.                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wordw_pointsto_write (width : Z) (mm : _) (a : Arch.pa) (vold vnew : mword (8*width)) :
    (0 < width)%Z ->
    gen_heap_interp (hG:=riscv_memGS) mm -∗ wordw_pointsto width a (DfracOwn 1) vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm a (Z.to_N width) vnew) ∗
    wordw_pointsto width a (DfracOwn 1) vnew.
  Proof.
    iIntros (Hw0) "Hm Hw". rewrite /wordw_pointsto.
    iDestruct "Hw" as "(%Hal & Hb)".
    iMod (upd_window_bw mm a vnew vold (seq 0 (Z.to_nat width)) with "Hm Hb") as "[Hm Hb]".
    iModIntro. iSplitL "Hm".
    - unfold write_bytes. replace (N.to_nat (Z.to_N width)) with (Z.to_nat width) by lia. iFrame "Hm".
    - iFrame "Hb". iPureIntro. exact Hal.
  Qed.

  Lemma wp_store_s_sconf_gen (width : Z) (c : bool) (γ : gname)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold sv : mword (8*width)) :
    0 < width -> width <= 8 -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    autocast (T := mword)
      (subrange_vec_dec
         (autocast (T := mword)
            (subrange_vec_dec (m !!! Regidx rs2) (width*8-1) 0) : mword (8*width))
         (8*(0+1)*width-1) (8*0*width)) = sv ->
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    wordw_pointsto width pa (DfracOwn 1) vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa (DfracOwn 1) sv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hw0 Hw8 Huintw Hwrite_plain Hsv pa.
    set (wlast := (Z.to_nat width - 1)%nat).
    assert (Hwn : Z.of_nat wlast = width - 1) by (unfold wlast; rewrite Nat2Z.inj_sub; [ rewrite Z2Nat.id; lia | lia ]).
    assert (Hwlt : (wlast < Z.to_nat width)%nat) by (unfold wlast; lia).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    rewrite /wordw_pointsto.
    iDestruct "Hbytes" as "(%Hpalign & Hbytes)".
    assert (Halign : is_aligned_vaddr (Virtaddr pa) width = true) by exact Hpalign.
    iApply (wp_instr_s_sconf γ m n Φ pc c
              (STORE (imm, Regidx rs2, Regidx rs1, width))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all pa width) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hms2 : rf_to_gmap m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply rf_to_gmap_lookup).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa wlast)⌝)%I as %Hrampal.
    { iDestruct (big_sepL_lookup _ _ wlast wlast with "Hbytes") as "Hbl".
      { rewrite lookup_seq_lt; [reflexivity | exact Hwlt]. }
      iDestruct (mem_ram with "Hbl") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + width <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat wlast < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. rewrite Hwn. lia. }
      pose proof (uint_pa_add pa wlast Hnw) as Heq.
      destruct Hrampal as [_ Hhil]. rewrite Heq in Hhil. rewrite Hwn in Hhil.
      unfold ram_base, ram_size in *. lia. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if c then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if c then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
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
    iAssert (⌜addr_is_kdata pa⌝)%I as %Hkdata.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_kdata with "Hbk") as %Hrk. rewrite pa_add_0 in Hrk. iPureIntro. exact Hrk. }
    iMod (sr_absorb_region strans_regime (Store Data) pa s_pc
            (or_intror (or_intror (or_introl eq_refl))) Hkdata Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htr")
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
    pose proof (within_clint_false pa width s_tr (addr_is_ram_not_in_clint _ Hrampa) Hw0) as Hwc.
    pose proof (within_sig_false pa width s_tr (addr_is_ram_not_in_sig _ Hrampa) Hw0) as Hws.
    pose proof (within_htif_writable_false pa width s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, width))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa (Z.to_N width) sv)
                              s_tr.(mdev))).
    {
      pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) width Hw0 Huintw Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_w_gpr_S_walk_pt width Hw8 Hwrite_plain rs2 rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign) ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hrange_st) HW
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact Hpalign)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mulw subrange_id sign_extend'_id in H0.
      rewrite Lv2 in H0.
      rewrite Hsv in H0.
      exact H0. }
    iMod (wordw_pointsto_write width s_tr.(mem) pa vold sv Hw0 with "Hmem [Hbytes]")
      as "[Hmem Hbytes]".
    { rewrite /wordw_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign. }
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa (Z.to_N width) sv) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa (Z.to_N width) sv) s_tr.(mdev)).(sregs)
             = add_vec_int pc (if c then 2 else 4)).
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
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hbytes").
  Qed.

  Lemma store_ext_8 (r : mword 64) :
    autocast (T := mword)
      (subrange_vec_dec (autocast (T := mword) (subrange_vec_dec r (8*8-1) 0) : mword (8*8))
         (8*(0+1)*8-1) (8*0*8)) = r.
  Proof.
    change (8*(0+1)*8-1) with (8*8-1). change (8*0*8) with 0.
    rewrite (autocast_subrange_id r). apply autocast_subrange_id.
  Qed.

  Lemma autocast_subrange32_id (d : mword 32) :
    autocast (T := mword) (subrange_vec_dec d (8*(0+1)*4-1) (8*0*4)) = d.
  Proof.
    change (8*(0+1)*4-1) with 31. change (8*0*4) with 0.
    unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
    apply bv_eq. rewrite autocast_id.
    unfold to_word_idx, to_word, get_word, MachineWord.slice.
    rewrite MachineWord.cast_idx_refl.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned.
  Qed.

  Lemma store_ext_4 (r : mword 64) :
    autocast (T := mword)
      (subrange_vec_dec (autocast (T := mword) (subrange_vec_dec r (4*8-1) 0) : mword (8*4))
         (8*(0+1)*4-1) (8*0*4)) = trunc32 r.
  Proof. unfold trunc32. apply autocast_subrange32_id. Qed.

  Lemma wp_csd_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 8 true γ Φ pc rs2 rs1 imm m n vold (m !!! Regidx rs2)
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (m !!! Regidx rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  Lemma wp_sd_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 8 false γ Φ pc rs2 rs1 imm m n vold (m !!! Regidx rs2)
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (m !!! Regidx rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_csw_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (m !!! Regidx rs2) in
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 4 true γ Φ pc rs2 rs1 imm m n vold (trunc32 (m !!! Regidx rs2))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (m !!! Regidx rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_sw_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (m !!! Regidx rs2) in
    sie_cap_gpr γ m n -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 4 false γ Φ pc rs2 rs1 imm m n vold (trunc32 (m !!! Regidx rs2))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (m !!! Regidx rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ld / sd -- the base-encoding width-8 pair: identical to the RVC      *)
  (* exemplars up to the fetch width (4-byte advance).                    *)
  (* ------------------------------------------------------------------- *)



  (* ------------------------------------------------------------------- *)
  (* c.lw / c.sw / lw / sw -- the width-4 quartet (lw sign-extends; the   *)
  (* stored word is trunc32 of rs2, definitionally the model's storeval). *)
  (* ------------------------------------------------------------------- *)










  (* ------------------------------------------------------------------- *)
  (* sb -- the width-1 RAM byte store (no alignment premise; the stored  *)
  (* byte is trunc8 of rs2, definitionally the model's storeval).        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mul1 (a : mword 64) : add_vec_int a (0 * 1) = a.
  Proof. change (0 * 1)%Z with 0%Z. apply avi0. Qed.

  Local Lemma is_aligned_vaddr_1 (vaddr : virtaddr) : is_aligned_vaddr vaddr 1 = true.
  Proof. destruct vaddr as [addr]. unfold is_aligned_vaddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Local Lemma is_aligned_paddr_1 (paddr : physaddr) : is_aligned_paddr paddr 1 = true.
  Proof. destruct paddr as [addr]. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Local Lemma write_bytes_1 (mm : _) (pa : Arch.pa) (v : bv 8) :
    write_bytes mm pa 1 v = <[pa := nth_byte v 0]> mm.
  Proof. unfold write_bytes. change (N.to_nat 1) with 1%nat. cbn [seq foldr]. rewrite pa_add_0. reflexivity. Qed.

  Local Lemma mem_update_1 (mm : _) (pa : Arch.pa) (vold vnew : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ pa ↦ₘ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 1 vnew) ∗ pa ↦ₘ (nth_byte vnew 0).
  Proof. rewrite write_bytes_1. apply mem_update. Qed.

  Local Lemma nth_byte0_id (v : bv 8) : nth_byte v 0 = v.
  Proof.
    apply bv_eq. rewrite nth_byte_unsigned.
    change (Z.of_N (8 * N.of_nat 0)) with 0%Z. rewrite Z.shiftr_0_r.
    apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ v) as Hr.
    unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 8)%Z with 256%Z in Hr. change (2 ^ 8)%Z with 256%Z. lia.
  Qed.

  Definition trunc8 (w : mword 64) : mword 8 :=
    autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 1 8) 1) 0).

  Lemma wp_sb_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 8) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc8 (m !!! Regidx rs2) in
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    pa ↦ₘ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦ₘ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbyte Hcont".
    iDestruct (mem_ram with "Hbyte") as %Hrampa.
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 1))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all pa 1) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hms2 : rf_to_gmap m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply rf_to_gmap_lookup).
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 1 <= ram_base + ram_size)%Z)
      by (destruct Hrampa as [_ Hh]; unfold ram_base, ram_size in *; lia).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
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
    iAssert (⌜addr_is_kdata pa⌝)%I as %Hkdata.
    { iDestruct (mem_kdata with "Hbyte") as %Hrk. iPureIntro. exact Hrk. }
    iMod (sr_absorb_region strans_regime (Store Data) pa s_pc
            (or_intror (or_intror (or_introl eq_refl))) Hkdata Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htr")
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
    pose proof (within_clint_false pa 1 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 1 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 1 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 1 storeval)
                              s_tr.(mdev))).
    { pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 1 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_1_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
                    Htea
                    ltac:(apply is_aligned_vaddr_1)
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact Htr_pc)
                    Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                    HA0 Hord0
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact Hrange_st)
                    HW
                    ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact Hmatch_st0)
                    ltac:(apply is_aligned_paddr_1)
                    Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; apply Hwc)
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; apply Hws)
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; apply Hwh)
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id in H0.
      exact H0. }
    iMod (mem_update_1 s_tr.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 1 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 1 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite nth_byte0_id) in "Hbyte".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hbyte").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.ldsp / c.sdsp -- the sp-relative immediate forms, bridged onto     *)
  (* the c.ld / c.sd leaves by [sext9_12_64] (pure immediate rewrite).    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cldsp_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : regfile) (n : nat) (v : mword 64) {dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg v]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm pa Hrd Hrdsp.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_sconf γ Φ pc rd csp_rs1 imm m n v (dqm:=dqm) Hrd Hrdsp).
  Qed.

  Lemma wp_csdsp_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : regfile) (n : nat) (vold : mword 64) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm pa.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_sconf γ Φ pc rs2 csp_rs1 imm m n vold).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* sd zero, imm(rs1) -- release's unconditional zero store.             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sd_zero_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := (zero_reg : mword 64) in
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hb") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
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
    iAssert (⌜addr_is_kdata pa⌝)%I as %Hkdata.
    { iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_kdata with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (sr_absorb_region strans_regime (Store Data) pa s_pc
            (or_intror (or_intror (or_introl eq_refl))) Hkdata Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htr")
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
    pose proof (within_clint_false pa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 8 storeval)
                              s_tr.(mdev))).
    {
      pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_8_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) HW
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id in H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iMod (word_pointsto_write s_tr.(mem) pa vold storeval with "Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 storeval) s_tr.(mdev)).(sregs)
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
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hbytes").
  Qed.

  (* c.sw x0 store (width-4 sibling of wp_sd_zero_s_sconf); moved here from
     ProofInitlock.v -- a store leaf belongs in the leaf file. *)
  Lemma wp_sw_zero_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := (mword_of_int 0 : mword 32) in
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
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
    iAssert (⌜addr_is_kdata pa⌝)%I as %Hkdata.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_kdata with "Hbk") as %Hrk. rewrite pa_add_0 in Hrk. iPureIntro. exact Hrk. }
    iMod (sr_absorb_region strans_regime (Store Data) pa s_pc
            (or_intror (or_intror (or_introl eq_refl))) Hkdata Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htr")
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
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 4 storeval)
                              s_tr.(mdev))).
    { pose proof (ram_pmp_match_w pa (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) HW
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iMod (upd_window_4 s_tr.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc] Hbw").
  Qed.


End WpSconfMem.
