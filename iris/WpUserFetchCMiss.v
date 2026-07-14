(* WpUserFetchCMiss.v -- the COMPRESSED fetch-miss engine wp_instr_c_miss,
   and the combined compressed fetch engine wp_instr_c.

   wp_instr_c_miss is the 16-bit twin of wp_instr_u_miss: given [spec!!vpn]
   and a TLB miss, the model WALKS the page table, FILLS the TLB with
   [upt_entry vpn ie], then fetches the compressed halfword (in EITHER the
   4-aligned full-word mode or the 2-aligned single-halfword mode, exactly
   as wp_instr_c_hit), decodes, expands (ExecuteAs), executes and retires --
   all in the one fetch step.  The re-established frame closes over the
   FILLED TLB.

   wp_instr_c is the compressed analogue of wp_instr_u: it dispatches on the
   TLB state (hit -> wp_instr_c_hit, collapsing the filled TLB back via
   vec64_update_same; miss -> wp_instr_c_miss), so compressed arms riding it
   carry NO fetch-hit precondition.                                        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr WpIntrCore.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall UmodeWalk.
Require Import UptInv SmodeCore.
Require Import WpUserComputeMiss.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserFetchCMiss.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation mie_v := (WpUserBase.mie_v U).
  Local Notation midl_v := (WpUserBase.midl_v U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation mip_v := (WpUserBase.mip_v U).
  Local Notation meip := (WpUserBase.meip U).
  Local Notation seip := (WpUserBase.seip U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation wp_instr_c_hit := (WpUserBase.wp_instr_c_hit U).
  Local Notation wp_instr_u_hit := (WpUserBase.wp_instr_u_hit U).


  (* ================================================================== *)
  (* The COMPRESSED fetch-miss engine: walk + fill + (two-mode) RVC fetch *)
  (* + decode + expand + execute, all in one step; frame over the filled *)
  (* TLB.  Merges wp_instr_u_miss's walk-fill with wp_instr_c_hit's       *)
  (* mode-split fetch (now at the FILLED state).                          *)
  (* ================================================================== *)
  Lemma wp_instr_c_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii ii_b : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some ie ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (forall s : mstate, exec (execute ii) s = Some (ExecuteAs ii_b, s)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii_b) (set_reg σ nextPC (add_vec_int va 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (upt_entry vpn ie))) -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          upt_inv root slots spec -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hmiss Hchk0 HupdN HSXL Hval0 Hcanon Hmode HisRVC Hdec Hexp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HA' Hord' HR' Hcov' Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    set (tlbvec' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (upt_entry vpn ie))).
    set (σ' := set_reg σ tlb tlbvec').
    assert (Htr : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
                    = Some (Ok (Physaddr (u_walk_pa (uw_pte0 ie) va),
                                PBMT_PMA, init_ext_ptw), σ')).
    { destruct Hmiss as [Hvec | (ent' & Hvec & Hnm)].
      - exact (exec_translateAddr_fetch_walk_u vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hval0 Hcanon).
      - exact (exec_translateAddr_fetch_walk_u_nomatch ent' vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec Hnm HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hval0 Hcanon). }
    set (pa := u_walk_pa (uw_pte0 ie) va) in *.
    assert (LpmpcX : register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0)
      by (unfold σ'; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00)
      by (unfold σ'; lk; exact Lpmpa).
    assert (LpmaX : register_lookup pma_regions σ'.(sregs) = pmar0)
      by (unfold σ'; lk; exact Lpma).
    assert (LhtifX : register_lookup htif_tohost_base σ'.(sregs) = None)
      by (unfold σ'; lk; exact Lhtif).
    assert (LprivX : register_lookup cur_privilege σ'.(sregs) = User)
      by (unfold σ'; lk; exact Lpriv).
    assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
      by (unfold σ'; lk; exact Lelp).
    assert (LmisaX : register_lookup misa σ'.(sregs) = misa0)
      by (unfold σ'; lk; exact Lmisa).
    assert (LpcX : register_lookup PC σ'.(sregs) = va)
      by (unfold σ'; lk; exact Lpc).
    assert (HZcaX : exec (currentlyEnabled Ext_Zca) σ' = Some (true, σ')).
    { apply exec_currentlyEnabled_Zca. rewrite LmisaX. exact HmisaC. }
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagX.
    pose proof (Hdec σ' HagX) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite LelpX; exact Help_np).
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    destruct Hmode as
      [ (w4 & Hvalm & Hpaal & Hcw & Hh_eq)
      | (Hb0v & Hb1v & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, the halfword is its low half *)
      iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte w4 j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
        iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite LpmpaX.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ'.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite LpmaX; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ')).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ' region
                 Lpc Hvalm Htr
                 ltac:(rewrite LpmpcX; exact HpmpA)
                 ltac:(rewrite LpmpaX; exact Hpmp_ord)
                 Hrange'
                 ltac:(rewrite LpmpcX; exact HpmpX)
                 Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ' Hnc ltac:(lia))
                 (within_sig_false pa 4 σ' Hns ltac:(lia))
                 (within_htif_false pa 4 σ' LhtifX)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf LprivX).
        rewrite <- Hh_eq. exact HisRVC. }
      iMod ("H" $! σ' LpcX HagX with "[Hreg Hmem Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      { unfold σ', set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ' s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad LpcX HZcaX).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc' Hupt").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
    - (* pc == 2 (mod 4): single 2-byte fetch *)
      iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 1%nat ltac:(lia)) with "Hcode") as "Hb1".
        iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 2) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite LpmpaX.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ'.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite LpmaX; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ')).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ' region
                 Lpc Hb0v Hb1v Hval4 HmisaC' Htr
                 ltac:(rewrite LpmpcX; exact HpmpA)
                 ltac:(rewrite LpmpaX; exact Hpmp_ord)
                 Hrange'
                 ltac:(rewrite LpmpcX; exact HpmpX)
                 Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ' Hnc ltac:(lia))
                 (within_sig_false pa 2 σ' Hns ltac:(lia))
                 (within_htif_false pa 2 σ' LhtifX)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf LprivX HisRVC). }
      iMod ("H" $! σ' LpcX HagX with "[Hreg Hmem Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      { unfold σ', set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ' s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad LpcX HZcaX).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc' Hupt").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  (* ================================================================== *)
  (* THE COMBINED COMPRESSED FETCH ENGINE.  Compressed analogue of        *)
  (* wp_instr_u: dispatches on the TLB state (hit -> wp_instr_c_hit, with  *)
  (* the filled TLB collapsed back to the original via vec64_update_same;  *)
  (* empty/colliding -> wp_instr_c_miss, converting the hit-form code      *)
  (* address to the walk form via the PA bridge).  Both branches hand back *)
  (* the FILLED TLB + upt_inv; compressed arms riding it carry NO          *)
  (* fetch-hit precondition.                                               *)
  (* ================================================================== *)
  Lemma wp_instr_c
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii ii_b : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (forall s : mstate, exec (execute ii) s = Some (ExecuteAs ii_b, s)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii_b) (set_reg σ nextPC (add_vec_int va 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (upt_entry vpn ie))) -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          upt_inv root slots spec -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN HSXL Hval0 Hcanon Hmode HisRVC Hdec Hexp.
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    (* the walk-form mode fact, for the two miss branches *)
    pose proof Hmode as Hmode_w.
    rewrite (WpUserComputeMiss.u_pa_upt_entry_walk vpn ie va) in Hmode_w.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + (* HIT *)
        destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (upt_entry vpn ie)) = tlbvec).
        { apply (WpUserComputeMiss.vec64_update_same tlbvec (tlb_hash (__id 39) vpn)
                   (Some (upt_entry vpn ie)));
            [ pose proof (tlb_hash_range vpn); lia | exact Hvacc ]. }
        iApply (wp_instr_c_hit va vpn ie h ii ii_b ms_v tlbvec E Φ HN Hvacc Hchk0 HupdN
                  Hpbmt0 HSXL Hval0 Hcanon Hmode HisRVC Hdec Hexp
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hcfg").
        iIntros (σ Hpceq Hag Hpins) "Hσ".
        iMod ("H" $! σ Hpceq Hag with "Hσ") as (s_exec) "(%Hexe & Hσ' & Hcont)".
        iModIntro. iExists s_exec. iFrame "Hσ'". iSplitR; [iPureIntro; exact Hexe |].
        iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
        iApply ("Hcont" with "Hhs' Hpriv' Hms' [Htlbc'] Hpc' Hupt Hcfg'").
        rewrite Hfill_id. iExact "Htlbc'".
      + (* colliding miss *)
        iApply (wp_instr_c_miss va vpn ie h ii ii_b ms_v tlbvec E Φ HN Hsome
                  (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN HSXL Hval0 Hcanon Hmode_w HisRVC Hdec Hexp
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
    - (* empty miss *)
      iApply (wp_instr_c_miss va vpn ie h ii ii_b ms_v tlbvec E Φ HN Hsome
                (or_introl Hvacc)
                Hchk0 HupdN HSXL Hval0 Hcanon Hmode_w HisRVC Hdec Hexp
                with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
  Qed.

End WpUserFetchCMiss.
