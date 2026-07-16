(* WpUserSplitTrap.v -- the 2-aligned (pc == 2 mod 4) split-fetch trapish
   combined-fetch engine for U-mode sync-trap arms.  It is the split (2+2)
   fetch twin of [WpUserTrapish.wp_exec_trapish_u]: SAME callback [K]
   contract (given the post-fetch state s_x with nextPC ticked to va+4 and
   tlb = the fetch-filled vector, provide the execute -> Trap fact + the
   trap cause/xtval + the delegation) and SAME generic U-mode
   sync-trap-delivery tower; the ONLY change is the FETCH front, which is
   the 2-aligned split form (dispatch the single non-straddling fetch TLB
   slot hit/miss exactly as [WpUserSplitFetchMiss.wp_instr_u_split_combined]
   does, wrapping [exec_fetch_F_Base_2_U_gen] instead of the 4-byte
   [exec_fetch_F_Base_4_U_gen]).

   SCOPE: only the non-straddling case (the low half at [va] and the high
   half at [va+2] share the same page/vpn), matching the retiring split
   engines.  The straddling case is a documented gap. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore SmodePte WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall.
Require Import UptInv UmodeData.
Require Import WpMmodeLeafBase.
Require Import WpLeafCommon UmodeTrap UmodeStep UmodeFetchFault.
Require Import UmodeWalk CommonWalk WpUserComputeMiss.
Require Import Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserSplitTrap.
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
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hdel_loadpf := (WpUserBase.Hdel_loadpf U).
  Local Notation Hdel_samopf := (WpUserBase.Hdel_samopf U).
  Local Notation Hdel_illegal := (WpUserBase.Hdel_illegal U).
  Local Notation Hdel_break := (WpUserBase.Hdel_break U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).

  Notation ill_cause := (rv64d_types.Exception (E_Illegal_Instr tt)).

  (* ================================================================== *)
  (* The split-fetch trapish fetch-HIT engine.  Fetch is a (non-         *)
  (* straddling) split fetch through a single TLB hit; the callback [K]  *)
  (* supplies the execute->Trap fact at the post-fetch state, the trap   *)
  (* cause [tc] + xtval [xv], and the medeleg delegation for [tc].       *)
  (* Clone of [WpUserTrapish.wp_exec_trapish_hit] with the 4-byte fetch  *)
  (* front swapped for the 2+2 split fetch.                              *)
  (* ================================================================== *)
  Lemma wp_exec_trapish_split_hit
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hnlp : is_lpad_instruction ii = false) by exact Hnlpad.
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
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
    (* the two halfword physical addresses (both hit the same entry) *)
    set (palv := u_pa (upt_entry vpn ie) va vpn) in *.
    set (pahv := u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) in *.
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
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec HcanonL Hvpn_defL) as HtrL.
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) (add_vec_int va 2) satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec HcanonH Hvpn_defH) as HtrH.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
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
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                         (Some (upt_entry vpn ie)) = tlbvec).
    { apply vec64_update_same; [ pose proof (tlb_hash_range vpn); lia | exact Hvec ]. }
    assert (LpcX : register_lookup PC s_x.(sregs) = va) by (unfold s_x; lk; exact Lpc).
    assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
      by (unfold s_x; lk; reflexivity).
    assert (LprivX : register_lookup cur_privilege s_x.(sregs) = User) by (unfold s_x; lk; exact Lpriv).
    assert (LmsX : register_lookup mstatus s_x.(sregs) = ms_v) by (unfold s_x; lk; exact Lms).
    assert (LsatpX : register_lookup satp s_x.(sregs) = satp0) by (unfold s_x; lk; exact Lsatp).
    assert (LpmpcX : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0) by (unfold s_x; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00) by (unfold s_x; lk; exact Lpmpa).
    assert (LtlbX : register_lookup tlb s_x.(sregs) = tlbvec) by (unfold s_x; lk; exact Ltlb).
    assert (HagX : agree_on D_u s_x dstateU).
    { unfold s_x.
      exact (agree_u_set_nextPC σ (add_vec_int va 4)
               (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')). }
    rewrite <- Hfill_id in LtlbX.
    iMod ("K" $! s_x LpcX LnpcX LprivX LmsX LsatpX LpmpcX LpmpaX HagX LtlbX
            with "[Htlbc] Hupt Hgpr [Hreg Hmem Hdev]")
      as (tc xv s' tlbvecD) "(%Hexec & %Hdel & %LpcS & %LtlbS & %HokD & Hσ' & Htlbc & Hupt & Hgpr)".
    { rewrite Hfill_id. iExact "Htlbc". }
    { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct "Hσ'" as "[Hreg [Hmem Hdev]]".
    set (resf := rv64d_types.Trap (User, make_sync_exception tc xv, va)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (resf, zero_extend' 32 w), s')).
    { apply (exec_hart_active_progress_base_gen User σ σ s' w ii va resf
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlp Lpc).
      - unfold resf. exact Hexec.
      - exact I. }
    iDestruct (reg_valid with "Hreg Hpriv") as %LprivX'.
    iDestruct (reg_valid with "Hreg Hms") as %LmsX'.
    iDestruct (reg_valid with "Hreg Hsc") as %LscX'.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %LstvecX'.
    iDestruct (reg_valid_dq with "Hreg Help") as %LelpX'.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %LmisaX'.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %LmedlX'.
    assert (LmisaSX' : eq_vec (_get_Misa_S (register_lookup misa s'.(sregs))) ('b"1") = true)
      by (rewrite LmisaX'; exact HmisaS).
    assert (LmedlX'' : bit_to_bool (access_vec_dec (register_lookup medeleg s'.(sregs))
                       (uint (exceptionType_bits_forwards tc))) = true)
      by (rewrite LmedlX'; exact Hdel).
    pose proof (exec_exception_handler_ne_M s' (rv64d_types.Exception tc) User va
                  (xtval_exception_value tc xv)
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX' LmsX' LscX' LstvecX' LelpX' LmisaSX' Htvd
                  (make_sync_exception tc xv)
                  eq_refl eq_refl eq_refl LmedlX'') as Hehe.
    match type of Hehe with _ = Some (_, ?T) => set (s9x := T) in Hehe end.
    set (s_trap := set_reg s9x nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch (Step_Execute (resf, zero_extend' 32 w))) s'
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch, resf. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hehe).
      unfold s_trap. apply exec_set_next_pc. }
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s'.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpX'. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception tc))))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception tc) sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value tc xv))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (resf, zero_extend' 32 w)), s', s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s9x. lk. exact LpcS. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. unfold s_trap, s9x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause (rv64d_types.Exception tc) sc_v),
            (tval (xtval_exception_value tc xv)),
            va, g, tlbvecD.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact HokD |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

  (* ================================================================== *)
  (* The split-fetch trapish fetch-MISS engine.  The low half walks +   *)
  (* fills the TLB for [vpn], the high half (same page) hits the fresh   *)
  (* entry; the callback [K] is identical to the hit engine's.  Clone    *)
  (* of [WpUserTrapish.wp_exec_trapish_miss] with the 4-byte walk fetch  *)
  (* front swapped for the 2+2 split walk/hit fetch.                     *)
  (* ================================================================== *)
  Lemma wp_exec_trapish_split_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hmiss Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hnlp : is_lpad_instruction ii = false) by exact Hnlpad.
    (* single-page ie high-half leaf facts (the fill IS [upt_entry vpn ie]) *)
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
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
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
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & _).
    assert (HAf : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hordf : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HRf : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcovf : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HAf Hordf HRf Hcovf Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
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
    { destruct Hmiss as [Hvec | (ent' & Hvec & Hnm)].
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
    set (pal := u_walk_pa (uw_pte0 ie) va) in *.
    set (pah := u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) in *.
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
    assert (LpcSf : register_lookup PC σ'.(sregs) = va)
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
    assert (HtrH : exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) σ'
                    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), σ')).
    { exact (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn HchkH' HupdH'
               HpbmtH' (upt_entry_match vpn ie) (add_vec_int va 2) satp0 tlbvec' σ'
               LprivX HSXLX LsatpX Hsatpmode Hasid LtlbX HvaccX HcanonH Hvpn_defH). }
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
    pose proof (exec_fetch_F_Base_2_U_gen va pal pah w σ σ' σ' regl regh
                  Lpc LpcSf HmisaC' Hbit0 Hbit1 Hvalign4 HtrL HtrH
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
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagXf.
    pose proof (Hdec σ' HagXf) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false).
    { assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
        by (unfold σ'; lk; exact Lelp).
      rewrite LelpX; exact Help_np. }
    set (s_x := set_reg σ' nextPC (add_vec_int va 4)).
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LpcX : register_lookup PC s_x.(sregs) = va) by (unfold s_x, σ'; lk; exact Lpc).
    assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
      by (unfold s_x; lk; reflexivity).
    assert (LprivXX : register_lookup cur_privilege s_x.(sregs) = User) by (unfold s_x, σ'; lk; exact Lpriv).
    assert (LmsX' : register_lookup mstatus s_x.(sregs) = ms_v) by (unfold s_x, σ'; lk; exact Lms).
    assert (LsatpX' : register_lookup satp s_x.(sregs) = satp0) by (unfold s_x, σ'; lk; exact Lsatp).
    assert (LpmpcX' : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0) by (unfold s_x, σ'; lk; exact Lpmpc).
    assert (LpmpaX' : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00) by (unfold s_x, σ'; lk; exact Lpmpa).
    assert (LtlbXX : register_lookup tlb s_x.(sregs)
                    = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    { unfold s_x, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      unfold σ', set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (HagX : agree_on D_u s_x dstateU).
    { unfold s_x. exact (agree_u_set_nextPC σ' (add_vec_int va 4) HagXf). }
    iMod ("K" $! s_x LpcX LnpcX LprivXX LmsX' LsatpX' LpmpcX' LpmpaX' HagX LtlbXX
            with "Htlbc Hupt Hgpr [Hreg Hmem Hdev]")
      as (tc xv s' tlbvecD) "(%Hexec & %Hdel & %LpcS & %LtlbS & %HokD & Hσ' & Htlbc & Hupt & Hgpr)".
    { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct "Hσ'" as "[Hreg [Hmem Hdev]]".
    set (resf := rv64d_types.Trap (User, make_sync_exception tc xv, va)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (resf, zero_extend' 32 w), s')).
    { apply (exec_hart_active_progress_base_gen User σ σ' s' w ii va resf
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlp LpcSf).
      - unfold resf. exact Hexec.
      - exact I. }
    iDestruct (reg_valid with "Hreg Hpriv") as %LprivX'.
    iDestruct (reg_valid with "Hreg Hms") as %LmsX''.
    iDestruct (reg_valid with "Hreg Hsc") as %LscX'.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %LstvecX'.
    iDestruct (reg_valid_dq with "Hreg Help") as %LelpX'.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %LmisaX'.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %LmedlX'.
    assert (LmisaSX' : eq_vec (_get_Misa_S (register_lookup misa s'.(sregs))) ('b"1") = true)
      by (rewrite LmisaX'; exact HmisaS).
    assert (LmedlX'' : bit_to_bool (access_vec_dec (register_lookup medeleg s'.(sregs))
                       (uint (exceptionType_bits_forwards tc))) = true)
      by (rewrite LmedlX'; exact Hdel).
    pose proof (exec_exception_handler_ne_M s' (rv64d_types.Exception tc) User va
                  (xtval_exception_value tc xv)
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX' LmsX'' LscX' LstvecX' LelpX' LmisaSX' Htvd
                  (make_sync_exception tc xv)
                  eq_refl eq_refl eq_refl LmedlX'') as Hehe.
    match type of Hehe with _ = Some (_, ?T) => set (s9x := T) in Hehe end.
    set (s_trap := set_reg s9x nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch (Step_Execute (resf, zero_extend' 32 w))) s'
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch, resf. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hehe).
      unfold s_trap. apply exec_set_next_pc. }
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s'.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpX'. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception tc))))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception tc) sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value tc xv))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (resf, zero_extend' 32 w)), s', s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s9x. lk. exact LpcS. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. unfold s_trap, s9x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause (rv64d_types.Exception tc) sc_v),
            (tval (xtval_exception_value tc xv)),
            va, g, tlbvecD.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact HokD |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

  (* ================================================================== *)
  (* Combined split-fetch trapish engine: dispatch on the fetch TLB      *)
  (* slot, exactly as [wp_instr_u_split_combined].                       *)
  (* ================================================================== *)
  Lemma wp_exec_trapish_u_split
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        iApply (wp_exec_trapish_split_hit va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hvacc Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
                  HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg K Hcont").
      + iApply (wp_exec_trapish_split_miss va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
                  HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg K Hcont").
    - iApply (wp_exec_trapish_split_miss va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hsome (or_introl Hvacc)
                Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
                HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg K Hcont").
  Qed.

  (* ================================================================== *)
  (* 2-aligned EBREAK-in-U arm, riding [wp_exec_trapish_u_split].  The   *)
  (* callback K returns the software-breakpoint Trap (cause E_Breakpoint *)
  (* Brk_Software, stval = va) directly -- execute is state-preserving,  *)
  (* so s' = s_x and tlbvecD = the fetch-fill (no data walk).            *)
  (* ================================================================== *)
  Lemma ustep_u_split_ebreak_u (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       register_lookup PC s.(sregs) = va ->
       exec (execute ii) s
         = Some (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_bp Hnlpad Hok Hsome Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1
           Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    iApply (wp_exec_trapish_u_split va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
              HN Hok Hsome Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL Hbit0 Hbit1 Hvalign4
              HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                    Hcode Hdata Hcfg [] Hcont").
    iIntros (s_x Hpcx Hnpcx Hprx Hmsx Hsatpx Hpmpcx Hpmpax Hagx Htlx)
            "Htlbc Hupt Hgpr Hσ".
    iModIntro.
    iExists (E_Breakpoint Brk_Software), va, s_x,
            (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iSplitR; [iPureIntro; exact (Hexec_bp s_x Hprx Hpcx) |].
    iSplitR; [iPureIntro; exact Hdel_break |].
    iSplitR; [iPureIntro; exact Hpcx |].
    iSplitR; [iPureIntro; exact Htlx |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iFrame "Hσ Htlbc Hupt Hgpr".
  Qed.

  (* ================================================================== *)
  (* 2-aligned illegal-in-U engines.  An illegal instruction's execute   *)
  (* returns [Illegal_Instruction] (NOT a [Trap]), which [try_step_      *)
  (* dispatch] delivers via [handle_exception] rather than the trap arm  *)
  (* used by [wp_exec_trapish_u_split].  So these arms cannot ride that   *)
  (* engine; instead they clone its split-fetch front + sync-trap tower   *)
  (* with the Illegal dispatch inlined (cause [E_Illegal_Instr], stval =  *)
  (* the fetched word).  Self-contained (no callback), like the 4-aligned *)
  (* [ustep_illegal_st_miss]/[WpUserTrap.ustep_illegal_st].              *)
  (* ================================================================== *)
  Lemma ustep_split_illegal_miss (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_ill Hnlpad Hok Hsome Hmiss Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
           Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
           HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
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
    assert (HcwL' : forall j : nat, (j < 2)%nat ->
              code !! pa_add (u_walk_pa (uw_pte0 ie) va) j
                = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
    { intros j Hj. rewrite <- (u_pa_upt_entry_walk vpn ie va). exact (HcwL j Hj). }
    assert (HalignL' : is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 2 = true).
    { rewrite <- (u_pa_upt_entry_walk vpn ie va). exact HalignL. }
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
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
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & _).
    assert (HAf : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hordf : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HRf : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcovf : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HAf Hordf HRf Hcovf Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
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
    { destruct Hmiss as [Hvec | (ent' & Hvec & Hnm)].
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
    set (pal := u_walk_pa (uw_pte0 ie) va) in *.
    set (pah := u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) in *.
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
    assert (LpcSf : register_lookup PC σ'.(sregs) = va)
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
    assert (HtrH : exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) σ'
                    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), σ')).
    { exact (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn HchkH' HupdH'
               HpbmtH' (upt_entry_match vpn ie) (add_vec_int va 2) satp0 tlbvec' σ'
               LprivX HSXLX LsatpX Hsatpmode Hasid LtlbX HvaccX HcanonH Hvpn_defH). }
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
    pose proof (exec_fetch_F_Base_2_U_gen va pal pah w σ σ' σ' regl regh
                  Lpc LpcSf HmisaC' Hbit0 Hbit1 Hvalign4 HtrL HtrH
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
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagXf.
    pose proof (Hdec σ' HagXf) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false).
    { assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
        by (unfold σ'; lk; exact Lelp).
      rewrite LelpX; exact Help_np. }
    set (s_x := set_reg σ' nextPC (add_vec_int va 4)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ' s_x w ii va
               (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad LpcSf).
      - apply (Hexec_ill s_x). unfold s_x, σ'; lk. exact Lpriv.
      - exact I. }
    assert (LprivXi : register_lookup cur_privilege s_x.(sregs) = User)
      by (unfold s_x, σ'; lk; exact Lpriv).
    assert (LmsXi : register_lookup mstatus s_x.(sregs) = ms_v)
      by (unfold s_x, σ'; lk; exact Lms).
    assert (LscXi : register_lookup scause s_x.(sregs) = sc_v)
      by (unfold s_x, σ'; lk; exact Lsc).
    assert (LstvecXi : register_lookup stvec s_x.(sregs) = stvec_v)
      by (unfold s_x, σ'; lk; exact Lstvec).
    assert (LelpXi : register_lookup elp s_x.(sregs) = elp0)
      by (unfold s_x, σ'; lk; exact Lelp).
    assert (LpcXx : register_lookup PC s_x.(sregs) = va)
      by (unfold s_x, σ'; lk; exact Lpc).
    assert (LmisaSXi : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true).
    { unfold s_x, σ'; lk. rewrite Lmisa. exact HmisaS. }
    assert (LmedlXi : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
    { unfold s_x, σ'; lk. rewrite Lmedl. exact Hdel_illegal. }
    pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                  (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivXi LmsXi LscXi LstvecXi LelpXi LmisaSXi Htvd LpcXx
                  (zero_extend' 64 (zero_extend' 32 w)) (E_Illegal_Instr tt)
                  eq_refl eq_refl LmedlXi) as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch
                       (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w))) s_x
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s_x.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpXi. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt ill_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause ill_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w))))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w)), s_x, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s_x, σ'. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s_trap, s_x, σ', set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause ill_cause sc_v),
            (tval (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))),
            va, g, tlbvec'.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

  Lemma ustep_split_illegal_hit (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_ill Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
           Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
           HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
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
    set (palv := u_pa (upt_entry vpn ie) va vpn) in *.
    set (pahv := u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) in *.
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
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec HcanonL Hvpn_defL) as HtrL.
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) (add_vec_int va 2) satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec HcanonH Hvpn_defH) as HtrH.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
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
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x w ii va
               (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - apply (Hexec_ill s_x). unfold s_x; lk. exact Lpriv.
      - exact I. }
    assert (LprivXi : register_lookup cur_privilege s_x.(sregs) = User)
      by (unfold s_x; lk; exact Lpriv).
    assert (LmsXi : register_lookup mstatus s_x.(sregs) = ms_v)
      by (unfold s_x; lk; exact Lms).
    assert (LscXi : register_lookup scause s_x.(sregs) = sc_v)
      by (unfold s_x; lk; exact Lsc).
    assert (LstvecXi : register_lookup stvec s_x.(sregs) = stvec_v)
      by (unfold s_x; lk; exact Lstvec).
    assert (LelpXi : register_lookup elp s_x.(sregs) = elp0)
      by (unfold s_x; lk; exact Lelp).
    assert (LpcXx : register_lookup PC s_x.(sregs) = va)
      by (unfold s_x; lk; exact Lpc).
    assert (LmisaSXi : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true).
    { unfold s_x; lk. rewrite Lmisa. exact HmisaS. }
    assert (LmedlXi : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
    { unfold s_x; lk. rewrite Lmedl. exact Hdel_illegal. }
    pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                  (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivXi LmsXi LscXi LstvecXi LelpXi LmisaSXi Htvd LpcXx
                  (zero_extend' 64 (zero_extend' 32 w)) (E_Illegal_Instr tt)
                  eq_refl eq_refl LmedlXi) as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch
                       (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w))) s_x
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s_x.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpXi. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt ill_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause ill_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w))))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w)), s_x, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s_x. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s_trap, s_x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause ill_cause sc_v),
            (tval (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))),
            va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

  (* Combined 2-aligned illegal-in-U arm: dispatch on the fetch TLB slot. *)
  Lemma ustep_u_split_illegal_u (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_ill Hnlpad Hok Hsome Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
           Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
           HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        iApply (ustep_split_illegal_hit ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hexec_ill Hnlpad Hok Hvacc Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
                  Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
                  HnotRVC Hdec
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg Hcont").
      + iApply (ustep_split_illegal_miss ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hexec_ill Hnlpad Hok Hsome (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
                  Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
                  HnotRVC Hdec
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg Hcont").
    - iApply (ustep_split_illegal_miss ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_ill Hnlpad Hok Hsome (or_introl Hvacc)
                Hchk0 HupdN Hpbmt0 HcwL HcwH HSXL
                Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH
                HnotRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg Hcont").
  Qed.

End WpUserSplitTrap.
