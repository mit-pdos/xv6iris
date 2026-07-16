(* WpUserSplitData.v -- the DATA-capable split-fetch (pc == 2 mod 4, 32-bit
   F_Base) U-mode retire engine.  Apply the [hit] -> [hit_data] delta of
   [WpUserBase.wp_instr_u_hit] -> [wp_instr_u_hit_data] to the combined
   split-fetch engine [WpUserSplitFetchMiss.wp_instr_u_split_combined]:

   the execute callback ADDITIONALLY receives the fetch-filled [tlb] cell +
   [upt_inv] (so a memory arm can walk+fill the DATA EA during execute), and
   the returned continuation DROPS them.  [upt_inv] survives the fetch walk
   ([upt_walk_read_ptes] is read-only), so it is threaded through BOTH fetch
   branches to the data callback.  Mirror of [WpUserComputeMiss.wp_instr_u_data].

   Three lemmas:
     [wp_instr_u_split_hit_data]  -- data twin of [WpUserSplitFetch.wp_instr_u_split]
     [wp_instr_u_split_miss_data] -- data twin of [wp_instr_u_split_miss]
     [wp_instr_u_split_data]      -- the combined dispatcher. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore SmodePte WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall UmodeWalk CommonWalk.
Require Import UptInv WpUserLoop.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.
Require Import WpUserComputeMiss.
Require Import WpUserSplitFetch.
Require Import WpUserSplitFetchMiss.

Section WpUserSplitData.
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
  Local Notation dqc := (WpUserBase.dqc U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation Htvd := (WpUserBase.Htvd U).
  Local Notation Hdel_ecall := (WpUserBase.Hdel_ecall U).
  Local Notation Hdel_fetchpf := (WpUserBase.Hdel_fetchpf U).
  Local Notation Hdel_loadpf := (WpUserBase.Hdel_loadpf U).
  Local Notation Hdel_samopf := (WpUserBase.Hdel_samopf U).
  Local Notation Hdel_illegal := (WpUserBase.Hdel_illegal U).
  Local Notation Hdel_break := (WpUserBase.Hdel_break U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).

  (* ================================================================= *)
  (* Data twin of [WpUserSplitFetch.wp_instr_u_split] (the HIT split      *)
  (* engine): the execute callback additionally receives [tlb] + [upt_inv],*)
  (* the returned continuation drops [tlb].                                *)
  (* ================================================================= *)
  Lemma wp_instr_u_split_hit_data
      (va : mword 64) (vpnL vpnH : mword 27) (ieL ieH : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* LOW half fetch-hit: va -> pal via vpnL/ieL *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnL) = Some (upt_entry vpnL ieL) ->
    uw_check_ok (InstructionFetch tt) ieL ->
    update_PTE_Bits (uw_pte0 ieL) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieL)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpnL ieL) va vpnL) j
         = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)) ->
    (* HIGH half fetch-hit: va+2 -> pah via vpnH/ieH *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnH) = Some (upt_entry vpnH ieH) ->
    uw_check_ok (InstructionFetch tt) ieH ->
    update_PTE_Bits (uw_pte0 ieH) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieH)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpnH ieH) (add_vec_int va 2) vpnH) j
         = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va geometry: pc == 2 (mod 4) *)
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    (* low half canon / vpn / pa-align *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnL ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnL ieL) va vpnL)) 2 = true ->
    (* high half canon / vpn / pa-align *)
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnH ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnH ieH) (add_vec_int va 2) vpnH)) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ tlbvec -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HvecL Hchk0L HupdNL Hpbmt0L HcwL
               HvecH Hchk0H HupdNH Hpbmt0H HcwH
               HSXL Hbit0 Hbit1 Hvalign4
               HcanonL Hvpn_defL HalignL
               HcanonH Hvpn_defH HalignH
               HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the per-half leaf facts, transported onto the stored TLB entries *)
    assert (HchkL' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnL ieL)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnL ieL))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0L. }
    assert (HupdL' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnL ieL)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdNL. }
    assert (HpbmtL' : forall s0, exec (tlb_get_pbmt (upt_entry vpnL ieL)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnL ieL s0 Hpbmt0L). }
    assert (HchkH' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnH ieH)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnH ieH))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0H. }
    assert (HupdH' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnH ieH)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdNH. }
    assert (HpbmtH' : forall s0, exec (tlb_get_pbmt (upt_entry vpnH ieH)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnH ieH s0 Hpbmt0H). }
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
    (* ---- the two halfword code pages: bytes + RAM-ness ---- *)
    set (palv := u_pa (upt_entry vpnL ieL) va vpnL) in *.
    set (pahv := u_pa (upt_entry vpnH ieH) (add_vec_int va 2) vpnH) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               σ.(mem) !! (pa_add palv j)
                 = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)⌝)%I as %HbfL.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               σ.(mem) !! (pa_add pahv j)
                 = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)⌝)%I as %HbfH.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram palv⌝)%I as %HramL.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add palv 1)⌝)%I as %HramL1.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL 1%nat ltac:(lia)) with "Hcode") as "Hb1".
      iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
    iAssert (⌜addr_is_ram pahv⌝)%I as %HramH.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pahv 1)⌝)%I as %HramH1.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH 1%nat ltac:(lia)) with "Hcode") as "Hb1".
      iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
    pose proof (addr_is_ram_not_in_clint _ HramL) as HncL.
    pose proof (addr_is_ram_not_in_sig _ HramL) as HnsL.
    pose proof (addr_is_ram_not_in_clint _ HramH) as HncH.
    pose proof (addr_is_ram_not_in_sig _ HramH) as HnsH.
    (* ---- pure facts: interrupts, translate, fetch, decode at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC).
    (* the two independent halfword translates (each state-preserving) *)
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpnL ieL) vpnL HchkL' HupdL'
                  HpbmtL' (upt_entry_match vpnL ieL) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb HvecL HcanonL Hvpn_defL) as HtrL.
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpnH ieH) vpnH HchkH' HupdH'
                  HpbmtH' (upt_entry_match vpnH ieH) (add_vec_int va 2) satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb HvecH HcanonH Hvpn_defH) as HtrH.
    (* shared PMP facts (pmpcfg / pmpaddr at σ, address-independent) *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    (* low half PMP range + PMA region *)
    destruct (Hpma_all palv 2) as (regl & HpmamL & HpmaxL & _ & _ & _).
    assert (HrangeL' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint palv) (uint (to_bits 64 2)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp palv (vec_access_dec pmpaddr00 0) 2 1
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramL HramL1 Hpmp_cov). }
    assert (HpmamL' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr palv) 2 = Some regl)
      by (rewrite Lpma; exact HpmamL).
    (* high half PMP range + PMA region *)
    destruct (Hpma_all pahv 2) as (regh & HpmamH & HpmaxH & _ & _ & _).
    assert (HrangeH' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pahv) (uint (to_bits 64 2)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pahv (vec_access_dec pmpaddr00 0) 2 1
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramH HramH1 Hpmp_cov). }
    assert (HpmamH' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pahv) 2 = Some regh)
      by (rewrite Lpma; exact HpmamH).
    (* the split (2+2) fetch *)
    pose proof (exec_fetch_F_Base_2_U_gen va palv pahv w σ σ σ regl regh
                  Lpc Lpc HmisaC' Hbit0 Hbit1 Hvalign4 HtrL HtrH
                  HA' Hord' HrangeL' HX' HpmamL' HalignL HpmaxL
                  (within_clint_false palv 2 σ HncL ltac:(lia))
                  (within_sig_false palv 2 σ HnsL ltac:(lia))
                  (within_htif_false palv 2 σ Lhtif)
                  (addr_is_ram_not_dev _ HramL) HbfL Lpriv
                  HA' Hord' HrangeH' HX' HpmamH' HalignH HpmaxH
                  (within_clint_false pahv 2 σ HncH ltac:(lia))
                  (within_sig_false pahv 2 σ HnsH ltac:(lia))
                  (within_htif_false pahv 2 σ Lhtif)
                  (addr_is_ram_not_dev _ HramH) HbfH Lpriv
                  HnotRVC (concat_subranges_id w)) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- the caller's execute fact ---- *)
    iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
            (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
            with "Htlbc Hupt [$Hreg $Hmem $Hdev]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  (* ================================================================= *)
  (* Data twin of [wp_instr_u_split_miss] (the MISS split engine): the    *)
  (* walk-filled [tlb] cell + [upt_inv] are threaded into the execute      *)
  (* callback ([upt_inv] survives the fetch walk since [upt_walk_read_ptes]*)
  (* is read-only), the returned continuation drops them.                  *)
  (* ================================================================= *)
  Lemma wp_instr_u_split_miss_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some ie ->
    (* the lookup MISSES: the hash slot is empty, or holds a non-matching
       (colliding) entry *)
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (* LOW half bytes (physaddr [u_pa (upt_entry vpn ie) va vpn]) *)
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j
         = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)) ->
    (* HIGH half bytes (same page, physaddr [u_pa (upt_entry vpn ie) (va+2) vpn]) *)
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) j
         = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va geometry: pc == 2 (mod 4) *)
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    (* low half canon / vpn / pa-align *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true ->
    (* high half canon / vpn (SAME vpn: non-straddling) / pa-align *)
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn)) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = vec_update_dec tlbvec
                                                  (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hvec Hchk0 HupdN HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    (* the high-half leaf facts, transported onto the (to-be-)stored entry *)
    assert (HchkH' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (HupdH' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (HpbmtH' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    (* transport the LOW-half bytes / pa-align onto the WALK address *)
    assert (HcwL' : forall j : nat, (j < 2)%nat ->
              code !! pa_add (u_walk_pa (uw_pte0 ie) va) j
                = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
    { intros j Hj. rewrite <- (u_pa_upt_entry_walk vpn ie va). exact (HcwL j Hj). }
    assert (HalignL' : is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 2 = true).
    { rewrite <- (u_pa_upt_entry_walk vpn ie va). exact HalignL. }
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
    (* ---- shared PMP facts at σ (for the walk translate) ---- *)
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
    (* ---- pure facts: interrupts + the walk-filling low translate ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    set (tlbvec' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (upt_entry vpn ie))).
    set (σ' := set_reg σ tlb tlbvec').
    assert (HtrL : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
                    = Some (Ok (Physaddr (u_walk_pa (uw_pte0 ie) va),
                                PBMT_PMA, init_ext_ptw), σ')).
    { destruct Hvec as [Hvec | (ent' & Hvec & Hnm)].
      - exact (exec_translateAddr_fetch_walk_u vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 HcanonL Hvpn_defL).
      - exact (exec_translateAddr_fetch_walk_u_nomatch ent' vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec Hnm HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 HcanonL Hvpn_defL). }
    (* the two physical addresses *)
    set (pal := u_walk_pa (uw_pte0 ie) va) in *.
    set (pah := u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) in *.
    (* ---- σ' pins: everything except tlb is untouched ---- *)
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
    assert (LmsX : register_lookup mstatus σ'.(sregs) = ms_v)
      by (unfold σ'; lk; exact Lms).
    assert (LsatpX : register_lookup satp σ'.(sregs) = satp0)
      by (unfold σ'; lk; exact Lsatp).
    assert (LpcX : register_lookup PC σ'.(sregs) = va)
      by (unfold σ'; lk; exact Lpc).
    assert (LtlbX : register_lookup tlb σ'.(sregs) = tlbvec')
      by (unfold σ'; lk; reflexivity).
    assert (HSXLX : _get_Mstatus_SXL (register_lookup mstatus σ'.(sregs)) = 'b"10")
      by (rewrite LmsX; exact HSXL).
    assert (HvaccX : vec_access_dec tlbvec' (tlb_hash (__id 39) vpn)
                       = Some (upt_entry vpn ie)).
    { unfold tlbvec'.
      rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)).
      rewrite Z.eqb_refl. reflexivity. }
    assert (HpinsX : register_lookup cur_privilege σ'.(sregs) = User
                  /\ register_lookup mstatus σ'.(sregs) = ms_v
                  /\ register_lookup satp σ'.(sregs) = satp0
                  /\ register_lookup tlb σ'.(sregs) = tlbvec'
                  /\ register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0
                  /\ register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00)
      by (split; [exact LprivX | split; [exact LmsX | split; [exact LsatpX |
          split; [exact LtlbX | split; [exact LpmpcX | exact LpmpaX]]]]]).
    (* the HIGH-half hit translate at σ' (same page: hits the filled entry) *)
    assert (HtrH : exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) σ'
                    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), σ')).
    { exact (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn HchkH' HupdH'
               HpbmtH' (upt_entry_match vpn ie) (add_vec_int va 2) satp0 tlbvec' σ'
               LprivX HSXLX LsatpX Hsatpmode Hasid LtlbX HvaccX HcanonH Hvpn_defH). }
    (* ---- the two halfword code pages: bytes + RAM-ness (at σ) ---- *)
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               σ.(mem) !! (pa_add pal j)
                 = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)⌝)%I as %HbfL.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL' j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               σ.(mem) !! (pa_add pah j)
                 = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)⌝)%I as %HbfH.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pal⌝)%I as %HramL.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL' 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pal 1)⌝)%I as %HramL1.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL' 1%nat ltac:(lia)) with "Hcode") as "Hb1".
      iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
    iAssert (⌜addr_is_ram pah⌝)%I as %HramH.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pah 1)⌝)%I as %HramH1.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwH 1%nat ltac:(lia)) with "Hcode") as "Hb1".
      iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
    pose proof (addr_is_ram_not_in_clint _ HramL) as HncL.
    pose proof (addr_is_ram_not_in_sig _ HramL) as HnsL.
    pose proof (addr_is_ram_not_in_clint _ HramH) as HncH.
    pose proof (addr_is_ram_not_in_sig _ HramH) as HnsH.
    (* ---- shared PMP facts at σ' + per-half PMA/range ---- *)
    assert (HAX : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR)
      by (rewrite LpmpcX; exact HpmpA).
    assert (HordX : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false)
      by (rewrite LpmpaX; exact Hpmp_ord).
    assert (HXX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
      by (rewrite LpmpcX; exact HpmpX).
    destruct (Hpma_all pal 2) as (regl & HpmamL & HpmaxL & _ & _ & _).
    assert (HrangeL' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pal) (uint (to_bits 64 2)) = PMP_Match).
    { rewrite LpmpaX.
      exact (ram_fetch_pmp pal (vec_access_dec pmpaddr00 0) 2 1
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramL HramL1 Hpmp_cov). }
    assert (HpmamL' : matching_pma_region (register_lookup pma_regions σ'.(sregs))
              (Physaddr pal) 2 = Some regl)
      by (rewrite LpmaX; exact HpmamL).
    destruct (Hpma_all pah 2) as (regh & HpmamH & HpmaxH & _ & _ & _).
    assert (HrangeH' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pah) (uint (to_bits 64 2)) = PMP_Match).
    { rewrite LpmpaX.
      exact (ram_fetch_pmp pah (vec_access_dec pmpaddr00 0) 2 1
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramH HramH1 Hpmp_cov). }
    assert (HpmamH' : matching_pma_region (register_lookup pma_regions σ'.(sregs))
              (Physaddr pah) 2 = Some regh)
      by (rewrite LpmaX; exact HpmamH).
    (* the split (2+2) fetch through σ -> σ' -> σ' *)
    pose proof (exec_fetch_F_Base_2_U_gen va pal pah w σ σ' σ' regl regh
                  Lpc LpcX HmisaC' Hbit0 Hbit1 Hvalign4 HtrL HtrH
                  HAX HordX HrangeL' HXX HpmamL' HalignL' HpmaxL
                  (within_clint_false pal 2 σ' HncL ltac:(lia))
                  (within_sig_false pal 2 σ' HnsL ltac:(lia))
                  (within_htif_false pal 2 σ' LhtifX)
                  (addr_is_ram_not_dev _ HramL) HbfL LprivX
                  HAX HordX HrangeH' HXX HpmamH' HalignH HpmaxH
                  (within_clint_false pah 2 σ' HncH ltac:(lia))
                  (within_sig_false pah 2 σ' HnsH ltac:(lia))
                  (within_htif_false pah 2 σ' LhtifX)
                  (addr_is_ram_not_dev _ HramH) HbfH LprivX
                  HnotRVC (concat_subranges_id w)) as Hfetch.
    (* decode at σ' (agreement survives the tlb fill) *)
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagX.
    pose proof (Hdec σ' HagX) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false).
    { assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
        by (unfold σ'; lk; exact Lelp).
      rewrite LelpX; exact Help_np. }
    (* ---- ghost tlb fill, then the caller's execute fact at σ' ---- *)
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod ("H" $! σ' LpcX HagX HpinsX with "Htlbc Hupt [Hreg Hmem Hdev]") as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    { unfold σ', set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ' s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad LpcX).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  (* ================================================================== *)
  (* THE COMBINED data-capable non-straddling split-fetch ENGINE.         *)
  (* Dispatches on the fetch TLB slot for [vpn] (matching cached entry ->  *)
  (* HIT data engine, empty/colliding -> MISS data engine); both branches  *)
  (* present ONE uniform data callback: the fetch-FILLED tlb + [upt_inv].  *)
  (* Mirror of [WpUserComputeMiss.wp_instr_u_data].                        *)
  (* ================================================================== *)
  Lemma wp_instr_u_split_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j
         = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)) ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) j
         = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn)) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = vec_update_dec tlbvec
                                                  (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
           HnotRVC Hdec Hnlpad.
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - (* the slot is occupied *)
      destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + (* HIT: the stored entry is forced to be [upt_entry vpn ie] *)
        destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (upt_entry vpn ie)) = tlbvec).
        { apply vec64_update_same; [ pose proof (tlb_hash_range vpn); lia | exact Hvacc ]. }
        iApply (wp_instr_u_split_hit_data va vpn vpn ie ie w ii ms_v tlbvec E Φ HN
                  Hvacc Hchk0 HupdN Hpbmt0 HcwL Hvacc Hchk0 HupdN Hpbmt0 HcwH
                  HSXL Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL
                  HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg").
        iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt Hσ".
        rewrite <- Hfill_id in Hpins.
        iMod ("H" $! σ Hpceq Hag Hpins
                with "[Htlbc] Hupt Hσ") as (s_exec) "(%Hexe & Hσ' & Hcont)".
        { rewrite Hfill_id. iExact "Htlbc". }
        iModIntro. iExists s_exec. iFrame "Hσ'". iSplitR; [iPureIntro; exact Hexe |].
        iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
        iApply ("Hcont" with "Hhs' Hpriv' Hms' Hpc' Hcfg'").
      + (* colliding miss: the walk fills a fresh entry *)
        iApply (wp_instr_u_split_miss_data va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                  (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
                  HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
                  HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
    - (* empty miss: the walk fills the slot *)
      iApply (wp_instr_u_split_miss_data va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                (or_introl Hvacc)
                Hchk0 HupdN HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
                HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
                HnotRVC Hdec Hnlpad
                with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
  Qed.

End WpUserSplitData.
