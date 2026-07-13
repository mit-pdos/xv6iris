(* WpLockLeaves.v -- instruction leaves that access the 4-byte lock word
   THROUGH the CSL lock invariant [is_lock] (WpLock.v) instead of an owned
   byte window.  Each leaf opens [is_lock]'s [inv] INSIDE the step engine's
   [E ∖ ↑minstretN] callback (the design hook documented in MinstretInv.v),
   uses the timeless byte window for the single instruction step, and
   re-closes the invariant before the step commits:

     wp_amoswap_lockinv     -- amoswap.w.aq on the lock word: loads some w
                               (existential), stores a nonzero word; if w = 0
                               the caller RECEIVES [locked γ ∗ R] (the lock
                               was free and this swap acquired it)
     wp_clw_lockinv         -- c.lw of the lock word: value existential,
                               invariant unchanged (holding()'s read)
     wp_clw_lockinv_locked  -- same, but the caller's [locked γ] token
                               refutes the free branch, so the loaded value
                               is known nonzero (release()'s holding check)
     wp_sw_zero_lockinv     -- 32-bit [sw zero,imm(rs1)] on the lock word:
                               the caller SUPPLIES [locked γ ∗ R], the
                               invariant is re-closed in the free state
                               (release()'s lock clear)
     wp_sd_zero_s           -- plain 32-bit [sd zero,imm(rs1)] on an OWNED
                               8-byte window (release() zeroing lk->cpu;
                               no invariant involved) *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.TypeCasts SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpPushOffMem WpAmo WpLock.
Local Open Scope Z_scope.
Import Defs.

Section WpLockLeaves.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* amoswap.w.aq rd, rs2, (rs1) on the LOCK WORD, through [is_lock].     *)
  (* Structured like a plain amoswap.w.aq step (cf. WpAmo.v's amoswap      *)
  (* value shims); the byte window comes out of the                       *)
  (* opened invariant (value [w] existential) and goes back with the      *)
  (* stored (nonzero) word under the "held" disjunct.  The pre-swap       *)
  (* branch payload is handed VERBATIM to the continuation: if the lock   *)
  (* was free, that is [locked γ ∗ R] -- acquisition.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_amoswap_lockinv (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (zeros' 64) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    pa = lk ->
    (* the swapped-in word is NONZERO (re-closes the "held" disjunct) *)
    neq_vec (sign_extend' 64 (amoswap_stored (m !!! Regidx rs2))) zero_reg = true ->
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
    (* fetch (4-byte base instruction) *)
    (* data address: the whole superpage-identity geometry AND the 4-byte
       alignment are DERIVED internally from the lock invariant's [lk ↦₄ _]
       (which carries [addr_is_ram] + alignment) -- see below -- so no geometry
       or alignment premise is taken here. *)
    (* the walks' PTE read *)
    (* AMO PMP: TOR entry 0 covers pa with R and W.  The AMO PMA side-condition
       (region matches pa, is R/W, and supports amoswap.w) is DERIVED internally
       from [pma_allows_all] -- which now pins [PMA_atomic_support] to [AMOSwap]
       -- so no premise is threaded here. *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) -∗
    is_lock γ lk R -∗
    ( ∀ w : mword 32,
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) -∗
      (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked γ ∗ R
       ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN HNl Hpalk Hstz Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_amo & Hmatch_amo & _ & Hread_amo & Hwrite_amo & Hatomic_supp_amo).
    assert (Hatomic_amo : pma_allows_atomic_op
              ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
              AMOSWAP 4 = true)
      by (rewrite Hatomic_supp_amo; vm_compute; reflexivity).
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* open the LOCK invariant for the duration of this instruction step *)
    iMod (inv_acc (E ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    (* recover the slot geometry (svpn := svpn_of pa) + vaddr alignment from
       [addr_is_ram pa] + the invariant's paddr alignment, instead of premises. *)
    set (svpn := svpn_of pa).
    pose proof (ram_canonical pa Hrampa) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (ram_ident root_ppn pa Hrampa) as Hident.
    pose proof (ram_mask pa Hrampa) as Hmask.
    pose proof (ram_svpn2 pa Hrampa) as Hvpn2.
    pose proof (ram_mvpn pa Hrampa) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn pa Hrampa) as Hmppn.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
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
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_amo.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
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
    assert (Hea_pc : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                             (zeros' 64) = pa)
      by (rewrite Lva; reflexivity).
    assert (Ha8_pc : sign_extend' 64 (subrange_vec_dec
                       (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                                (zeros' 64)) (xlen - 0 - 1) 0) = pa)
      by (rewrite Hea_pc subrange_id sign_extend'_id; reflexivity).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the AMO's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_f Lhtif_f) as Hwhr.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwhw.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr pa) (Atomic (AMOSWAP, Data, Data))) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { apply (exec_translateAddr_amo_walk root_ppn pa svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp (addr_is_ram_not_dev _ Hramp) Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := set_reg (MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 (amoswap_stored (m !!! Regidx rs2))) s_f.(mdev))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (amoswap_loaded w))).
      assert (Hexec : exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s_pc
                      = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_AMOSWAP_4_gpr_S_walk rs2 rs1 rd region_amo satp0 tlbf2 w s_pc Hrd
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Ha8_pc; exact Halign4)
                   ltac:(rewrite Ha8_pc; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Ha8_pc; exact Hrange_amo) ltac:(rewrite Lpmpc_f; exact HR)
                   ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Ha8_pc; exact Hmatch_amo)
                   ltac:(rewrite Ha8_pc; exact Hpalign4)
                   Hread_amo Hwrite_amo Hatomic_amo
                   ltac:(rewrite Ha8_pc; apply Hwc) ltac:(rewrite Ha8_pc; apply Hws)
                   ltac:(rewrite Ha8_pc; apply Hwhr) ltac:(rewrite Ha8_pc; apply Hwhw)
                   ltac:(rewrite Ha8_pc; exact (addr_is_ram_not_dev _ Hrampa))
                   ltac:(rewrite Ha8_pc; exact Hbytesf)).
        assert (Hsf_gpr : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_f.(sregs)
                          = register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
          by (unfold s_f; tmig; reflexivity).
        pose proof Lv2 as Lv2_f. rewrite <- Hsf_gpr in Lv2_f.
        subst s_x. unfold amoswap_stored, amoswap_loaded.
        rewrite Ha8_pc. rewrite Lv2_f. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (amoswap_loaded w))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (amoswap_loaded w)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod (upd_window_4 σ.(mem) pa (amoswap_stored (m !!! Regidx rs2)) w with "Hmem Hbytes") as "[Hmem Hbytes]".
      (* re-close the lock invariant: the word is now the NONZERO stored one *)
      iMod ("Hclose" with "[Hbytes]") as "_".
      { iNext. iExists (amoswap_stored (m !!! Regidx rs2)).
        iSplitL. { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iRight. iPureIntro. exact Hstz. }
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iNext.
      iApply ("Hcont" $! w with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbr").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
    - (* ---- data slot RESIDENT: TLB hit (state-preserving translate) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_pc Lhtif_pc) as Hwhr.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwhw.
      assert (Htr_pc : exec (translateAddr (Virtaddr pa) (Atomic (AMOSWAP, Data, Data))) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { apply (exec_translateAddr_amo_hit root_ppn pa svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := set_reg (MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 (amoswap_stored (m !!! Regidx rs2))) s_pc.(mdev))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (amoswap_loaded w))).
      assert (Hexec : exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s_pc
                      = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_AMOSWAP_4_gpr_S rs2 rs1 rd region_amo satp0 w s_pc Hrd
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Ha8_pc; exact Halign4)
                   ltac:(rewrite Ha8_pc; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Ha8_pc; exact Hrange_amo) ltac:(rewrite Lpmpc_pc; exact HR)
                   ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Ha8_pc; exact Hmatch_amo)
                   ltac:(rewrite Ha8_pc; exact Hpalign4)
                   Hread_amo Hwrite_amo Hatomic_amo
                   ltac:(rewrite Ha8_pc; apply Hwc) ltac:(rewrite Ha8_pc; apply Hws)
                   ltac:(rewrite Ha8_pc; apply Hwhr) ltac:(rewrite Ha8_pc; apply Hwhw)
                   ltac:(rewrite Ha8_pc; exact (addr_is_ram_not_dev _ Hrampa))
                   ltac:(rewrite Ha8_pc; exact Hbytesf)).
        subst s_x. unfold amoswap_stored, amoswap_loaded.
        rewrite Ha8_pc. rewrite Lv2. reflexivity. }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (amoswap_loaded w))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (amoswap_loaded w)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod (upd_window_4 σ.(mem) pa (amoswap_stored (m !!! Regidx rs2)) w with "Hmem Hbytes") as "[Hmem Hbytes]".
      iMod ("Hclose" with "[Hbytes]") as "_".
      { iNext. iExists (amoswap_stored (m !!! Regidx rs2)).
        iSplitL. { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iRight. iPureIntro. exact Hstz. }
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iNext.
      iApply ("Hcont" $! w with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbr").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.lw rd, imm(rs1) READING the lock word through [is_lock]: the       *)
  (* loaded value [v] is existential (whatever the invariant holds), and  *)
  (* the invariant is re-closed UNCHANGED.  holding()'s lock-word read.   *)
  (* Cloned from WpPushOffMem.wp_clw_s.                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_clw_lockinv (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    pa = lk ->
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
    (* fetch *)
    (* data address: the superpage-identity geometry AND the 4-byte alignment
       are DERIVED internally from the lock invariant's [lk ↦₄ _]
       (addr_is_ram + alignment) -- see below -- no premise taken. *)
    (* the walks' PTE read *)
    (* load PMP: TOR entry 0 covers pa with R *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗
    ( ∀ v : mword 32,
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN HNl Hpalk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (E ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    (* recover the slot geometry (svpn := svpn_of pa) + vaddr alignment from
       [addr_is_ram pa] + the invariant's paddr alignment, instead of premises. *)
    set (svpn := svpn_of pa).
    pose proof (ram_canonical pa Hrampa) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (ram_ident root_ppn pa Hrampa) as Hident.
    pose proof (ram_mask pa Hrampa) as Hmask.
    pose proof (ram_svpn2 pa Hrampa) as Hvpn2.
    pose proof (ram_mvpn pa Hrampa) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn pa Hrampa) as Hmppn.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampab.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hbb".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hbb") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampab as [_ Hhi]. rewrite Heq in Hhi. change (Z.of_nat 3) with 3 in Hhi.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
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
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 4)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the load's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_load_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp (addr_is_ram_not_dev _ Hramp) Hpbytesf Lmenv_pc HPBMTE). }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S_walk rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod ("Hclose" with "[Hbytes Hbr]") as "_".
      { iNext. iExists v. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iExact "Hbr". }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" $! v with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_load_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod ("Hclose" with "[Hbytes Hbr]") as "_".
      { iNext. iExists v. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iExact "Hbr". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" $! v with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Same read, but the caller HOLDS [locked γ]: the invariant's free     *)
  (* disjunct would contain a second token, so it is refuted and the      *)
  (* loaded value is known NONZERO.  release()'s holding() check.         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_clw_lockinv_locked (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    pa = lk ->
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
    (* fetch *)
    (* data address: the superpage-identity geometry AND the 4-byte alignment
       are DERIVED internally from the lock invariant's [lk ↦₄ _]
       (addr_is_ram + alignment) -- see below -- no premise taken. *)
    (* the walks' PTE read *)
    (* load PMP: TOR entry 0 covers pa with R *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗
    locked γ -∗
    ( ∀ v : mword 32,
      ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
      locked γ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN HNl Hpalk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Htok Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (E ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iDestruct "Hbr" as "[(_ & >Htok2 & _) | >%Hvnz]".
    { iExFalso. iApply (locked_exclusive with "Htok Htok2"). }
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    (* recover the slot geometry (svpn := svpn_of pa) + vaddr alignment from
       [addr_is_ram pa] + the invariant's paddr alignment, instead of premises. *)
    set (svpn := svpn_of pa).
    pose proof (ram_canonical pa Hrampa) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (ram_ident root_ppn pa Hrampa) as Hident.
    pose proof (ram_mask pa Hrampa) as Hmask.
    pose proof (ram_svpn2 pa Hrampa) as Hvpn2.
    pose proof (ram_mvpn pa Hrampa) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn pa Hrampa) as Hmppn.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampab.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hbb".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hbb") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampab as [_ Hhi]. rewrite Heq in Hhi. change (Z.of_nat 3) with 3 in Hhi.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
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
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 4)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the load's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_load_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp (addr_is_ram_not_dev _ Hramp) Hpbytesf Lmenv_pc HPBMTE). }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S_walk rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod ("Hclose" with "[Hbytes]") as "_".
      { iNext. iExists v. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iRight. iPureIntro. exact Hvnz. }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" $! v with "[//] Htok Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_load_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iMod ("Hclose" with "[Hbytes]") as "_".
      { iNext. iExists v. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iRight. iPureIntro. exact Hvnz. }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" $! v with "[//] Htok Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 32-bit [sd zero, imm(rs1)] -- 8-byte store of x0 through a GENERAL   *)
  (* base register onto an OWNED window (release() zeroing lk->cpu).      *)
  (* Cloned from WpAcquireMem.wp_csd_s with rs2 := x0, is_rvc := false.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sd_zero_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (zero_reg : mword 64) in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: X-bit + RAM coverage (geometry derived from instr_bytes) *)
    (* data address: the superpage-identity geometry AND alignment are DERIVED
       internally (addr_is_ram + alignment from the owned points-to/invariant)
       -- see below -- no premise taken. *)
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (svpn := svpn_of pa).
    pose proof (ram_canonical pa Hrampa) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (ram_ident root_ppn pa Hrampa) as Hident.
    pose proof (ram_mask pa Hrampa) as Hmask.
    pose proof (ram_svpn2 pa Hrampa) as Hvpn2.
    pose proof (ram_mvpn pa Hrampa) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn pa Hrampa) as Hmppn.
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
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
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampab.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hbb".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hbb") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampab as [_ Hhi]. rewrite Heq in Hhi. change (Z.of_nat 7) with 7 in Hhi.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
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
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp (addr_is_ram_not_dev _ Hramp) Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S_walk (mword_of_int 0 : mword 5) rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))).
        subst s_x. do 3 f_equal. rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id.
        first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S (mword_of_int 0 : mword 5) rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))).
        subst s_x. do 3 f_equal. rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id.
        first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 32-bit [sw zero, imm(rs1)] CLEARING the lock word through [is_lock]: *)
  (* the caller supplies [locked γ ∗ R] and the invariant is re-closed in *)
  (* the FREE state.  release()'s lock clear.  Cloned from                *)
  (* WpPushOffMem.wp_csw_s with rs2 := x0, is_rvc := false.               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sw_zero_lockinv (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    pa = lk ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: the superpage-identity geometry AND alignment are DERIVED
       internally (addr_is_ram + alignment from the owned points-to/invariant)
       -- see below -- no premise taken. *)
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    is_lock γ lk R -∗
    locked γ -∗
    R -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN HNl Hpalk HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    set (storeval := (mword_of_int 0 : mword 32)).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Htok HRes Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (E ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes _]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    set (svpn := svpn_of pa).
    pose proof (ram_canonical pa Hrampa) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (ram_ident root_ppn pa Hrampa) as Hident.
    pose proof (ram_mask pa Hrampa) as Hmask.
    pose proof (ram_svpn2 pa Hrampa) as Hvpn2.
    pose proof (ram_mvpn pa Hrampa) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn pa Hrampa) as Hmppn.
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampab.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hbb".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hbb") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampab as [_ Hhi]. rewrite Heq in Hhi. change (Z.of_nat 3) with 3 in Hhi.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
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
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp (addr_is_ram_not_dev _ Hramp) Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S_walk (mword_of_int 0 : mword 5) rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))).
        subst s_x. do 3 f_equal. rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id.
        first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_4 σ.(mem) pa storeval w with "Hmem Hbytes") as "[Hmem Hbytes]".
      iMod ("Hclose" with "[Hbytes Htok HRes]") as "_".
      { iNext. iExists storeval. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iLeft. iFrame "Htok HRes". iPureIntro. reflexivity. }
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S (mword_of_int 0 : mword 5) rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))).
        subst s_x. do 3 f_equal. rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id.
        first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
      iMod (upd_window_4 σ.(mem) pa storeval w with "Hmem Hbytes") as "[Hmem Hbytes]".
      iMod ("Hclose" with "[Hbytes Htok HRes]") as "_".
      { iNext. iExists storeval. iSplitL "Hbytes".
        { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
        iLeft. iFrame "Htok HRes". iPureIntro. reflexivity. }
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap]").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

End WpLockLeaves.
