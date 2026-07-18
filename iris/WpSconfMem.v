(* WpSconfMem.v -- the SIE-AGNOSTIC data-leaf layer (interrupt-sweep
   stage 5): the [sconf]+[sie_cap] twins of the width-8 RVC LOAD/STORE
   exemplars (WpSmodePtLeaves.v's [wp_cld_s_pt]/[wp_csd_s_pt]), over the
   agnostic funnel [wp_instr_s_sconf].

   The data-side translation runs through the absorption theorem
   [tlb_inv_pt_translateAddr_load/store] INSIDE the funnel's
   σf-callback, exactly as in the `_pt` originals -- the callback hands
   the whole [tlb_inv_pt] through, and the config facts (MPRV/SXL/MXR/
   PMM) now come from [sconf]'s bundled fact sets instead of eight
   per-call premises.  Spec cleanups made in this pass:
     - the redundant [let ea := .. let a8 := ea let pa := a8] alias
       chain collapses to the single [let pa := ..];
     - ALL config premises are gone (SIE is decided by the ghost, the
       rest ride in [sconf_ms_facts]/the menvcfg conjunct);
     - the STORE needs no rd-premises at all (it writes no register,
       so [sie_cap] is not even retargeted); the LOAD keeps
       [uint rd <> 0] and [rd <> csp_rs1].
   The remaining WpSmodePtMem widths (4/1, base widths) follow this
   template mechanically.                                                *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad WpLeafCommon.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import SmodeCore WpSmodeGpr WpMmodeJal.
Require Import KptTree SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import StackOwn WpSmodeSret AlignBits.
Require Import WpIntrBits WpIntrCore IntrDefs WpIntrInv WpSmodeIntr.
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
  Lemma wp_cld_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 64) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg v]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts out of the invariant, then
       reassemble it (the absorption theorem consumes it whole) *)
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iMod (tlb_inv_pt_translateAddr_load root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg v))).
    { rewrite <- Hev.
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Load Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Load Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      apply (exec_execute_LOAD_8_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg v]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg v]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sd rs2, imm(rs1) -- width-8 RVC store.  No register write, so no   *)
  (* rd premises and no [sie_cap] retarget.                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csd_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true
              (STORE (imm, Regidx rs2, Regidx rs1, 8))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hms2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
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
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2))
                              s_tr.(mdev))).
    {
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      pose proof (exec_execute_STORE_8_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id in H0.
      exact H0. }
    iMod (word_pointsto_write s_tr.(mem) pa vold (m !!! Regidx rs2) with "Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2)) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2)) s_tr.(mdev)).(sregs)
             = add_vec_int pc 2).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ld / sd -- the base-encoding width-8 pair: identical to the RVC      *)
  (* exemplars up to the fetch width (4-byte advance).                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ld_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 64) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg v]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts out of the invariant, then
       reassemble it (the absorption theorem consumes it whole) *)
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iMod (tlb_inv_pt_translateAddr_load root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg v))).
    { rewrite <- Hev.
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Load Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Load Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      apply (exec_execute_LOAD_8_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg v]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg v]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_sd_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 8))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hms2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
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
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2))
                              s_tr.(mdev))).
    {
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      pose proof (exec_execute_STORE_8_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id in H0.
      exact H0. }
    iMod (word_pointsto_write s_tr.(mem) pa vold (m !!! Regidx rs2) with "Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2)) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 (m !!! Regidx rs2)) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.lw / c.sw / lw / sw -- the width-4 quartet (lw sign-extends; the   *)
  (* stored word is trunc32 of rs2, definitionally the model's storeval). *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_clw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    pa ↦₄{ dqm } v -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts out of the invariant, then
       reassemble it (the absorption theorem consumes it whole) *)
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iMod (tlb_inv_pt_translateAddr_load root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Load Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Load Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
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
    iAssert (pa ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma wp_csw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (m !!! Regidx rs2) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc true
              (STORE (imm, Regidx rs2, Regidx rs1, 4))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hms2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
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
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 4 storeval)
                              s_tr.(mdev))).
    { assert (Htea : exec (transform_effective_address
            (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
          = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
 { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm))
            (exec_translationMode_S_sv39 satp1 s_pc
               ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
 pose proof (exec_execute_STORE_4_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      exact H0. }
    iMod (upd_window_4 s_tr.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 2).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


  Lemma wp_lw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dqm : dfrac} :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    pa ↦₄{ dqm } v -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hrd Hrdsp.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    (* unbundle the config: the data path needs MPRV/SXL/MXR/PMM + values *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts out of the invariant, then
       reassemble it (the absorption theorem consumes it whole) *)
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iMod (tlb_inv_pt_translateAddr_load root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Load Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Load Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma wp_sw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (m !!! Regidx rs2) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 4))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hms2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
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
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 4 storeval)
                              s_tr.(mdev))).
    { assert (Htea : exec (transform_effective_address
            (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
          = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
 { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm))
            (exec_translationMode_S_sv39 satp1 s_pc
               ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
 pose proof (exec_execute_STORE_4_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lv2 Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      exact H0. }
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
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.




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

  Lemma wp_sb_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 8) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := trunc8 (m !!! Regidx rs2) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    pa ↦ₘ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦ₘ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbyte Hcont".
    iDestruct (mem_ram with "Hbyte") as %Hrampa.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 1))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 1) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hms2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 1 <= ram_base + ram_size)%Z)
      by (destruct Hrampa as [_ Hh]; unfold ram_base, ram_size in *; lia).
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 1 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
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
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
    { assert (Htea : exec (transform_effective_address
            (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
          = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               (exec_translationMode_S_sv39 satp1 s_pc
                  ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      pose proof (exec_execute_STORE_1_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr
                    Htea
                    ltac:(apply is_aligned_vaddr_1)
                    ltac:(rewrite Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact Htr_pc)
                    Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                    ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
                    ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul1 subrange_id sign_extend'_id; exact Hrange_st)
                    ltac:(rewrite Lpmpc_tr; exact HW)
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
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbyte").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.ldsp / c.sdsp -- the sp-relative immediate forms, bridged onto     *)
  (* the c.ld / c.sd leaves by [sext9_12_64] (pure immediate rewrite).    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cldsp_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : mword 64) {dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg v]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm pa Hrd Hrdsp.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_sconf γ root_ppn Φ pc rd csp_rs1 imm m v (dqm:=dqm) Hrd Hrdsp).
  Qed.

  Lemma wp_csdsp_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : mword 64) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm pa.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_sconf γ root_ppn Φ pc rs2 csp_rs1 imm m vold).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* sd zero, imm(rs1) -- release's unconditional zero store.             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sd_zero_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : mword 64) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := (zero_reg : mword 64) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
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
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
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
      assert (Htea : exec (transform_effective_address
                 (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
               = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      pose proof (exec_execute_STORE_8_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
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
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.


End WpSconfMem.
